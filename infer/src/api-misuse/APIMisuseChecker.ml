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
  {pname: Procname.t; node: CFG.Node.t; node_hash: int; inv_map: BufferOverrunAnalysis.invariant_map}

module Models = struct
  open ProcnameDispatcher.Call.FuncArg
  open AbsLoc
  module Dom = APIMisuseDomain

  type exec_fun = model_env -> ret:Ident.t * Typ.t -> APIMisuseDomain.Mem.t -> APIMisuseDomain.Mem.t

  type model = {exec: exec_fun}

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
    {exec}


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
    let exec {node; inv_map} ~ret mem =
      match (map_exp, BufferOverrunAnalysis.extract_state (CFG.Node.id node) inv_map) with
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
    {exec}


  let dispatch =
    let open ProcnameDispatcher.Call in
    make_dispatcher
      [ -"std" &:: "map" < capt_all >:: "operator[]" $ capt_arg $+ capt_arg $!--> at
      ; -"std" &:: "map" < capt_all >:: "map" $ capt_arg $!--> constructor ]
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
    match instr with
    | Load {id; e; typ} ->
        (* id is a pure variable. id itself is a valid loc *)
        let mem =
          let loc = Loc.of_id id |> APIDom.LocWithIdx.of_loc in
          let v =
            APIDom.PowLocWithIdx.fold
              (fun l v -> APIDom.Mem.find_on_demand ~typ l mem |> APIDom.Val.join v)
              (Sem.eval_locs e mem) APIDom.Val.bottom
          in
          APIDom.Mem.add loc v mem
        in
        mem
    | Prune _ ->
        mem
    | Store {e1; e2} ->
        (* e1 can be either PVar or LVar. *)
        let locs1 = Sem.eval_locs e1 mem in
        let v =
          Sem.eval_locs e2 mem |> APIDom.Val.of_pow_loc
          |> APIDom.Val.join (APIDom.Init.Init |> APIMisuseDomain.Val.of_init)
        in
        APIDom.PowLocWithIdx.fold (fun l m -> APIDom.Mem.add l v m) locs1 mem
    | Call (((_, _) as ret), Const (Cfun callee_pname), args, _, _) -> (
        let inv_map =
          BufferOverrunAnalysis.cached_compute_invariant_map
            (InterproceduralAnalysis.bind_payload analysis_data ~f:snd)
        in
        let fun_arg_list =
          List.map args ~f:(fun (exp, typ) ->
              ProcnameDispatcher.Call.FuncArg.{exp; typ; arg_payload= ()} )
        in
        match Models.dispatch tenv callee_pname fun_arg_list with
        | Some {Models.exec} ->
            let pname = Procdesc.get_proc_name proc_desc in
            let node_hash = CFG.Node.hash node in
            let model_env = {pname; node; node_hash; inv_map} in
            exec model_env ~ret mem
        | None ->
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


let rec make_subst formals actuals mem subst =
  match (formals, actuals) with
  | (pvar, _) :: t1, (exp, _) :: t2 -> (
    match get_symbol pvar with
    | Some sym ->
        L.(debug Analysis Quiet) "make subst sym: %a" AbsLoc.Loc.pp sym ;
        let locs =
          Sem.eval_locs exp mem |> Fun.flip APIDom.Mem.find_set mem |> APIDom.Val.get_powloc
        in
        let locs =
          APIDom.PowLocWithIdx.fold
            (fun l s -> APIDom.LocWithIdx.to_loc l |> Fun.flip AbsLoc.PowLoc.add s)
            locs AbsLoc.PowLoc.bot
        in
        L.(debug Analysis Quiet) "make subst locs: %a" AbsLoc.PowLoc.pp locs ;
        (fun s -> if AbsLoc.Loc.equal s sym then locs else subst s) |> make_subst t1 t2 mem
    | _ ->
        subst )
  | _, _ ->
      subst


let check_instr get_summary get_formals mem instr condset =
  match instr with
  | Sil.Load {e; loc} ->
      let locs =
        Sem.eval_locs e mem
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
          APIDom.CondSet.add (APIDom.Cond.make absloc APIDom.Init.UnInit loc) condset
        else condset
  | Sil.Call (_, Const (Cfun callee_pname), args, _, _) -> (
    match (get_summary callee_pname, get_formals callee_pname) with
    | Some (Some api_summary, Some _), Some callee_formals ->
        let eval_sym = make_subst callee_formals args mem (fun _ -> AbsLoc.PowLoc.bot) in
        L.d_printfln_escaped "Callee summary %a" APIDom.Summary.pp api_summary ;
        APIDom.CondSet.subst eval_sym mem api_summary.APIDom.Summary.condset
        |> APIDom.CondSet.join condset
    | _ ->
        condset )
  | _ ->
      condset


let collect_instrs get_summary get_formals mem instrs condset =
  if Instrs.is_empty instrs then condset
  else
    let instr = Instrs.nth_exn instrs 0 in
    check_instr get_summary get_formals mem instr condset


let collect_node get_summary get_formals inv_map node condset =
  match Analyzer.extract_pre (CFG.Node.id node) inv_map with
  | Some mem ->
      let instrs = CFG.instrs node in
      collect_instrs get_summary get_formals mem instrs condset
  | None ->
      condset


let collect get_summary get_formals inv_map cfg =
  CFG.fold_nodes cfg
    ~f:(fun condset node -> collect_node get_summary get_formals inv_map node condset)
    ~init:APIDom.CondSet.empty


let report {InterproceduralAnalysis.proc_desc; err_log} condset =
  APIDom.CondSet.iter
    (fun cond ->
      if APIDom.Cond.is_symbolic cond || APIDom.Cond.is_init cond then ()
      else
        Reporting.log_issue proc_desc err_log ~loc:cond.loc APIMisuse IssueType.api_misuse
          "API Misuse" )
    condset


let compute_summary ({InterproceduralAnalysis.analyze_dependency} as analysis_data) cfg inv_map =
  let open IOption.Let_syntax in
  let exit_node_id = CFG.exit_node cfg |> CFG.Node.id in
  let get_summary proc_name = analyze_dependency proc_name >>| snd in
  let get_formals callee_pname =
    AnalysisCallbacks.get_proc_desc callee_pname >>| Procdesc.get_pvar_formals
  in
  match Analyzer.extract_post exit_node_id inv_map with
  | Some mem ->
      let condset = collect get_summary get_formals inv_map cfg in
      report analysis_data condset ;
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
