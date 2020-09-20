(*
 * Copyright (c)
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module F = Format
module L = Logging
module BoUtils = BufferOverrunUtils
module BoSemantics = BufferOverrunSemantics
module BoDomain = BufferOverrunDomain
module APIDom = APIMisuseDomain
module Sem = APIMisuseSemantics
module CFG = ProcCfg.NormalOneInstrPerNode

type model_env =
  { pname: Procname.t
  ; node: CFG.Node.t
  ; node_hash: int
  ; bo_mem_opt: BoDomain.Mem.t AbstractInterpreter.State.t option
  ; location: Location.t }

module Models = struct
  open ProcnameDispatcher.Call.FuncArg
  open AbsLoc
  module Dom = APIMisuseDomain

  type exec_fun = model_env -> ret:Ident.t * Typ.t -> APIMisuseDomain.Mem.t -> APIMisuseDomain.Mem.t

  type check_fun = model_env -> APIDom.Mem.t -> APIDom.CondSet.t -> APIDom.CondSet.t

  type model = {exec: exec_fun; check: check_fun}

  let empty_exec_fun _ ~ret:_ mem = mem

  let empty_check_fun _ _ condset = condset

  let empty = {exec= empty_exec_fun; check= empty_check_fun}

  let constructor _ {exp} =
    let exec {pname; node_hash} ~ret:_ mem =
      match exp with
      | Exp.Lvar v ->
          let allocsite =
            Allocsite.make pname ~node_hash ~inst_num:0 ~dimension:1 ~path:None
              ~represents_multiple_values:false
          in
          let loc = Loc.of_pvar v |> Dom.LocWithIdx.of_loc in
          let v =
            Loc.of_allocsite allocsite |> Dom.LocWithIdx.of_loc |> Dom.PowLocWithIdx.singleton
            |> Dom.Val.of_pow_loc
          in
          Dom.Mem.add loc v mem
      | _ ->
          L.user_warning "Invalid argument of std::map" ;
          mem
    in
    {exec; check= empty_check_fun}


  let at _ {exp= map_exp} {exp= idx} =
    let eval_maploc map_exp mem =
      match map_exp with
      | Exp.Lvar v ->
          Loc.of_pvar v |> Dom.LocWithIdx.of_loc |> Fun.flip Dom.Mem.find mem |> Dom.Val.get_powloc
      | Exp.Var id ->
          Loc.of_id id |> Dom.LocWithIdx.of_loc |> Fun.flip Dom.Mem.find mem |> Dom.Val.get_powloc
      | _ ->
          L.die Die.InternalError "Unreachable"
    in
    let exec {bo_mem_opt} ~ret mem =
      match (map_exp, bo_mem_opt) with
      | Exp.Lvar _, Some bomem | Exp.Var _, Some bomem ->
          let idx_val =
            BoSemantics.eval_locs idx bomem.post
            |> Fun.flip BoDomain.Mem.find_set bomem.pre
            |> BoDomain.Val.get_itv
          in
          let retloc = fst ret |> Loc.of_id |> Dom.LocWithIdx.of_loc in
          let maploc = eval_maploc map_exp mem in
          let v =
            Dom.PowLocWithIdx.map (Fun.flip Dom.LocWithIdx.append_idx idx_val) maploc
            |> Dom.Val.of_pow_loc
          in
          Dom.Mem.add retloc v mem
      | _, _ ->
          mem
    in
    {exec; check= empty_check_fun}


  let fread buffer =
    let exec {node; bo_mem_opt; location} ~ret:_ mem =
      match (buffer, bo_mem_opt) with
      | Exp.Lvar _, Some bomem | Exp.Var _, Some bomem ->
          BoSemantics.eval_locs buffer bomem.pre
          |> Fun.flip
               (PowLoc.fold (fun l mem ->
                    let v = Dom.UserInput.make node location |> Dom.Val.of_user_input in
                    let loc = Dom.LocWithIdx.of_loc l in
                    Dom.Mem.add loc v mem ))
               mem
      | _, _ ->
          mem
    in
    {exec; check= empty_check_fun}


  let malloc size =
    let check {location} mem condset =
      let v = Sem.eval size mem |> APIDom.Val.get_int_overflow in
      APIDom.CondSet.add (APIDom.Cond.make_overflow v location) condset
    in
    {empty with check}


  let dispatch =
    let open ProcnameDispatcher.Call in
    make_dispatcher
      [ -"std" &:: "map" < capt_all >:: "operator[]" $ capt_arg $+ capt_arg $!--> at
      ; -"std" &:: "map" < capt_all >:: "map" $ capt_arg $+? any_arg $+? any_arg $+? any_arg
        $!--> constructor
      ; -"fread" <>$ capt_exp $+...$--> fread
      ; -"malloc" <>$ capt_exp $--> malloc ]
end

type analysis_data =
  (APIMisuseDomain.Summary.t option * BufferOverrunAnalysisSummary.t option)
  InterproceduralAnalysis.t

module TransferFunctions = struct
  module CFG = CFG
  module Domain = APIMisuseDomain.Mem

  type nonrec analysis_data = analysis_data

  open AbsLoc

  let exec_instr : Domain.t -> analysis_data -> CFG.Node.t -> Sil.instr -> Domain.t =
   fun mem ({proc_desc; tenv} as analysis_data) node instr ->
    let bo_inv_map =
      BufferOverrunAnalysis.cached_compute_invariant_map
        (InterproceduralAnalysis.bind_payload analysis_data ~f:snd)
    in
    let bo_mem_opt = BufferOverrunAnalysis.extract_state (CFG.Node.id node) bo_inv_map in
    match instr with
    | Load {id; e; typ} ->
        (* id is a pure variable. id itself is a valid loc *)
        let loc = Loc.of_id id |> APIDom.LocWithIdx.of_loc in
        let v =
          APIDom.PowLocWithIdx.fold
            (fun l v -> APIDom.Mem.find_on_demand ~typ l mem |> APIDom.Val.join v)
            (Sem.eval_locs e bo_mem_opt mem) APIDom.Val.bottom
        in
        APIDom.Mem.add loc v mem
    | Prune _ ->
        mem
    | Store {e1; e2} ->
        (* e1 can be either PVar or LVar. *)
        let locs1 = Sem.eval_locs e1 bo_mem_opt mem in
        let v = Sem.eval e2 mem in
        APIDom.PowLocWithIdx.fold (fun l m -> APIDom.Mem.add l v m) locs1 mem
    | Call (((_, _) as ret), Const (Cfun callee_pname), args, location, _) -> (
        let fun_arg_list =
          List.map args ~f:(fun (exp, typ) ->
              ProcnameDispatcher.Call.FuncArg.{exp; typ; arg_payload= ()} )
        in
        match Models.dispatch tenv callee_pname fun_arg_list with
        | Some {Models.exec} ->
            let pname = Procdesc.get_proc_name proc_desc in
            let node_hash = CFG.Node.hash node in
            let model_env = {pname; node; node_hash; bo_mem_opt; location} in
            exec model_env ~ret mem
        | None ->
            (* TODO: instantiate *)
            mem )
    | _ ->
        mem


  let pp_session_name _node fmt = F.pp_print_string fmt "API misuse"
end

module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions)
module LocationSet = AbstractDomain.FiniteSet (Location)
module Summary = APIDom.Summary
open AbsLoc

let get_symbol pvar =
  match pvar |> Loc.of_pvar |> Loc.get_path with
  | Some p ->
      Allocsite.make_symbol p |> Loc.of_allocsite |> Option.some
  | _ ->
      None


let rec make_subst formals actuals bo_mem mem subst =
  match (formals, actuals) with
  | (pvar, _) :: t1, (exp, _) :: t2 -> (
    match get_symbol pvar with
    | Some sym ->
        L.(debug Analysis Quiet) "make subst sym: %a" AbsLoc.Loc.pp sym ;
        let locs =
          Sem.eval_locs exp bo_mem mem |> Fun.flip APIDom.Mem.find_set mem |> APIDom.Val.get_powloc
        in
        let locs =
          APIDom.PowLocWithIdx.fold
            (fun l s -> APIDom.LocWithIdx.to_loc l |> Fun.flip AbsLoc.PowLoc.add s)
            locs AbsLoc.PowLoc.bot
        in
        L.(debug Analysis Quiet) "make subst locs: %a" AbsLoc.PowLoc.pp locs ;
        (fun s -> if AbsLoc.Loc.equal s sym then locs else subst s) |> make_subst t1 t2 bo_mem mem
    | _ ->
        subst )
  | _, _ ->
      subst


let check_instr {InterproceduralAnalysis.tenv; proc_desc} get_summary get_formals bo_mem_opt mem
    node instr condset =
  match instr with
  | Sil.Load {e; loc} ->
      let locs =
        Sem.eval_locs e bo_mem_opt mem
        |> APIDom.PowLocWithIdx.filter (function APIDom.LocWithIdx.Idx (_, _) -> true | _ -> false)
      in
      if APIDom.PowLocWithIdx.is_empty locs then condset
      else
        let v =
          APIDom.PowLocWithIdx.fold
            (fun l v -> APIDom.Mem.find l mem |> APIDom.Val.join v)
            locs APIDom.Val.bottom
          |> APIDom.Val.get_init
        in
        if APIDom.Init.equal v APIDom.Init.Init |> not then
          let absloc = APIDom.PowLocWithIdx.choose locs in
          APIDom.CondSet.add (APIDom.Cond.make_uninit absloc APIDom.Init.UnInit loc) condset
        else condset
  | Sil.Call (_, Const (Cfun callee_pname), args, location, _) -> (
      let fun_arg_list =
        List.map args ~f:(fun (exp, typ) ->
            ProcnameDispatcher.Call.FuncArg.{exp; typ; arg_payload= ()} )
      in
      match Models.dispatch tenv callee_pname fun_arg_list with
      | Some {Models.check} ->
          let pname = Procdesc.get_proc_name proc_desc in
          let node_hash = CFG.Node.hash node in
          let model_env = {pname; node; node_hash; bo_mem_opt; location} in
          check model_env mem condset
      | None -> (
        match (get_summary callee_pname, get_formals callee_pname) with
        | Some (Some api_summary, Some _), Some callee_formals ->
            let eval_sym =
              make_subst callee_formals args bo_mem_opt mem (fun _ -> AbsLoc.PowLoc.bot)
            in
            L.d_printfln_escaped "Callee summary %a" APIDom.Summary.pp api_summary ;
            APIDom.CondSet.subst eval_sym mem api_summary.APIDom.Summary.condset
            |> APIDom.CondSet.join condset
        | _ ->
            condset ) )
  | _ ->
      condset


let collect_instrs analysis_data get_summary get_formals bo_mem mem node instrs condset =
  if Instrs.is_empty instrs then condset
  else
    let instr = Instrs.nth_exn instrs 0 in
    check_instr analysis_data get_summary get_formals bo_mem mem node instr condset


let collect_node analysis_data get_summary get_formals inv_map node condset =
  let bo_mem =
    BufferOverrunAnalysis.cached_compute_invariant_map
      (InterproceduralAnalysis.bind_payload analysis_data ~f:snd)
    |> BufferOverrunAnalysis.extract_state (CFG.Node.id node)
  in
  match Analyzer.extract_pre (CFG.Node.id node) inv_map with
  | Some mem ->
      let instrs = CFG.instrs node in
      collect_instrs analysis_data get_summary get_formals bo_mem mem node instrs condset
  | None ->
      condset


let collect analysis_data get_summary get_formals inv_map cfg =
  CFG.fold_nodes cfg
    ~f:(fun condset node -> collect_node analysis_data get_summary get_formals inv_map node condset)
    ~init:APIDom.CondSet.empty


let report {InterproceduralAnalysis.proc_desc; err_log} condset =
  APIDom.CondSet.fold
    (fun cond condset ->
      if APIDom.Cond.is_symbolic cond || APIDom.Cond.is_reported cond then
        APIDom.CondSet.add cond condset
      else
        let loc = APIDom.Cond.get_location cond in
        match cond with
        | APIDom.Cond.UnInit _ when APIDom.Cond.is_init cond |> not ->
            Reporting.log_issue proc_desc err_log ~loc APIMisuse IssueType.api_misuse "UnInit" ;
            APIDom.CondSet.add (APIDom.Cond.reported cond) condset
        | APIDom.Cond.Overflow _ when APIDom.Cond.may_overflow cond ->
            Reporting.log_issue proc_desc err_log ~loc APIMisuse IssueType.api_misuse "Overflow" ;
            APIDom.CondSet.add (APIDom.Cond.reported cond) condset
        | _ ->
            APIDom.CondSet.add cond condset )
    condset APIDom.CondSet.empty


let compute_summary ({InterproceduralAnalysis.analyze_dependency} as analysis_data) cfg inv_map =
  let open IOption.Let_syntax in
  let exit_node_id = CFG.exit_node cfg |> CFG.Node.id in
  let get_summary proc_name = analyze_dependency proc_name >>| snd in
  let get_formals callee_pname =
    AnalysisCallbacks.get_proc_desc callee_pname >>| Procdesc.get_pvar_formals
  in
  match Analyzer.extract_post exit_node_id inv_map with
  | Some mem ->
      let condset =
        collect analysis_data get_summary get_formals inv_map cfg |> report analysis_data
      in
      Some (APIDom.Summary.make mem condset)
  | None ->
      None


let checker ({InterproceduralAnalysis.proc_desc} as analysis_data) =
  BufferOverrunAnalysis.cached_compute_invariant_map
    (InterproceduralAnalysis.bind_payload analysis_data ~f:snd)
  |> ignore ;
  let cfg = CFG.from_pdesc proc_desc in
  let inv_map = Analyzer.exec_pdesc analysis_data ~initial:APIMisuseDomain.Mem.initial proc_desc in
  compute_summary analysis_data cfg inv_map
