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
module Dom = APIMisuseDomain
module Sem = APIMisuseSemantics
module Models = APIMisuseModel
module CFG = ProcCfg.NormalOneInstrPerNode
module LocationSet = AbstractDomain.FiniteSet (Location)
module Summary = Dom.Summary
module SPath = Symb.SymbolPath
module Trace = APIMisuseTrace
module TraceSet = APIMisuseTrace.Set
open AbsLoc

type analysis_data =
  { interproc:
      (APIMisuseDomain.Summary.t option * BufferOverrunAnalysisSummary.t option)
      InterproceduralAnalysis.t
  ; get_summary:
         Procname.t
      -> (APIMisuseDomain.Summary.t option * BufferOverrunAnalysisSummary.t option) option
  ; get_formals: Procname.t -> (Pvar.t * Typ.t) list option }

let make_subst_traces p v location mem s =
  let sym_absloc = Allocsite.make_symbol p |> Loc.of_allocsite in
  let sym_absloc_deref =
    SPath.deref ~deref_kind:SPath.Deref_CPointer p |> Allocsite.make_symbol |> Loc.of_allocsite
  in
  let traces = Dom.Val.get_traces v in
  TraceSet.fold
    (fun trace set ->
      match List.last trace with
      | Some (Trace.SymbolDecl l) when Loc.equal l sym_absloc ->
          TraceSet.fold
            (fun t set ->
              let t = Trace.concat [Trace.make_call location] t in
              let t = Trace.concat trace t in
              TraceSet.add t set)
            traces set
      | Some (Trace.SymbolDecl l) when Loc.equal l sym_absloc_deref ->
          let deref_subst_val =
            try Sem.Mem.find (Dom.PowLocWithIdx.min_elt (Dom.Val.get_powloc v)) mem
            with _ -> Dom.Val.bottom
          in
          let traces = Dom.Val.get_traces deref_subst_val in
          TraceSet.fold
            (fun t set ->
              let t = Trace.concat [Trace.make_call location] t in
              let t = Trace.concat trace t in
              TraceSet.add t set)
            traces set
      | _ ->
          TraceSet.add trace set)
    s TraceSet.empty


let rec make_subst formals actuals location bo_mem mem
    ({Dom.Subst.subst_powloc; subst_int_overflow; subst_user_input} as subst) =
  match (formals, actuals) with
  | (pvar, _) :: t1, (exp, _) :: t2 -> (
    match pvar |> Loc.of_pvar |> Loc.get_path with
    | Some p ->
        let sym_absloc = Allocsite.make_symbol p |> Loc.of_allocsite in
        let sym_int_overflow = Dom.IntOverflow.make_symbol p in
        let sym_user_input = Dom.UserInput.make_symbol p in
        L.(debug Analysis Quiet) "make subst sym: %a\n" AbsLoc.Loc.pp sym_absloc ;
        let v = Sem.eval exp location mem in
        let locs = Dom.Val.get_powloc v in
        let locs =
          Dom.PowLocWithIdx.fold
            (fun l s -> Dom.LocWithIdx.to_loc l |> Fun.flip AbsLoc.PowLoc.add s)
            locs AbsLoc.PowLoc.bot
        in
        let int_overflow = Dom.Val.get_int_overflow v in
        let user_input = Dom.Val.get_user_input v in
        L.(debug Analysis Quiet) "make subst locs: %a\n" AbsLoc.PowLoc.pp locs ;
        L.(debug Analysis Quiet) "make subst int overflow: %a\n" Dom.IntOverflow.pp int_overflow ;
        L.(debug Analysis Quiet) "make subst user input: %a\n" Dom.UserInput.pp user_input ;
        { Dom.Subst.subst_powloc=
            (fun s -> if AbsLoc.Loc.equal s sym_absloc then locs else subst_powloc s)
        ; subst_int_overflow=
            (fun s ->
              if Dom.IntOverflow.equal s sym_int_overflow then int_overflow
              else subst_int_overflow s)
        ; subst_user_input=
            (fun s ->
              match s with
              | SetSymbol ss ->
                  Dom.UserInput.SetSymbol.fold
                    (fun sym s ->
                      let setsymbol_sym = Dom.UserInput.make_symbol sym in
                      let subst_val =
                        match sym with
                        | BufferOverrunField.Prim (SPath.Deref (_, p)) ->
                            let deref_subst_val =
                              try
                                Sem.Mem.find (Dom.PowLocWithIdx.min_elt (Dom.Val.get_powloc v)) mem
                              with _ -> Dom.Val.bottom
                            in
                            if Dom.UserInput.equal (Dom.UserInput.make_symbol p) sym_user_input then
                              Dom.Val.get_user_input deref_subst_val
                            else subst_user_input setsymbol_sym
                        | _ ->
                            if Dom.UserInput.equal setsymbol_sym sym_user_input then user_input
                            else subst_user_input setsymbol_sym
                      in
                      Dom.UserInput.join subst_val s)
                    ss Dom.UserInput.bottom
              | _ ->
                  subst_user_input s)
        ; subst_traces= make_subst_traces p v location mem }
        |> make_subst t1 t2 location bo_mem mem
    | _ ->
        subst )
  | _, _ ->
      subst


module TransferFunctions = struct
  module CFG = CFG
  module Domain = APIMisuseDomain.Mem

  type nonrec analysis_data = analysis_data

  open AbsLoc

  let instantiate_param callee_formals params
      (bo_mem : GOption.some BoDomain.Mem.t0 AbstractInterpreter.State.t option) callee_exit_mem mem
      =
    let m =
      List.fold2 callee_formals params ~init:mem ~f:(fun m (p, _) (e, _) ->
          match (p |> Loc.of_pvar |> Loc.get_path, e) with
          | Some formal, Exp.Lvar pvar ->
              let param_powloc =
                ( match bo_mem with
                | Some bomem ->
                    BoSemantics.eval_locs e bomem.pre
                | _ ->
                    PowLoc.bot )
                |> Dom.PowLocWithIdx.of_pow_loc
              in
              let formal_loc =
                formal
                |> SPath.deref ~deref_kind:SPath.Deref_CPointer
                |> Allocsite.make_symbol |> Loc.of_allocsite |> Dom.LocWithIdx.of_loc
              in
              let param_val =
                let l = pvar |> Loc.of_pvar |> Dom.LocWithIdx.of_loc in
                Dom.Mem.find l mem
              in
              let v = Domain.find formal_loc callee_exit_mem in
              let v = {v with traces= TraceSet.concat param_val.Dom.Val.traces v.Dom.Val.traces} in
              let param_var = Dom.Val.get_powloc param_val in
              Dom.PowLocWithIdx.fold
                (fun l mem -> Domain.add l v mem)
                (Dom.PowLocWithIdx.join param_var param_powloc)
                m
          | _, _ ->
              m)
    in
    match m with
    | IStd.List.Or_unequal_lengths.Ok result_mem ->
        result_mem
    | IStd.List.Or_unequal_lengths.Unequal_lengths ->
        mem


  let instantiate_ret ret_id callee_formals callee_pname params location bo_mem callee_exit_mem mem
      =
    let ret_var = ret_id |> Loc.of_id |> Dom.LocWithIdx.of_loc in
    let subst = make_subst callee_formals params location bo_mem mem Dom.Subst.empty in
    let ret_val =
      Domain.find
        (Loc.of_pvar (Pvar.get_ret_pvar callee_pname) |> Dom.LocWithIdx.of_loc)
        callee_exit_mem
      |> Dom.Val.subst subst
    in
    let rec add_val_rec var present_mem present_depth =
      if present_depth > 3 then present_mem
      else
        let add_val = Domain.find var callee_exit_mem |> Dom.Val.subst subst in
        let add_val_powloc = Dom.Val.get_powloc add_val in
        let new_mem =
          Dom.PowLocWithIdx.fold
            (fun l m -> Dom.Mem.join m (add_val_rec l m (present_depth + 1)))
            add_val_powloc present_mem
        in
        Domain.add var add_val new_mem
    in
    let ret_val_powloc = Dom.Val.get_powloc ret_val in
    let new_mem =
      Dom.PowLocWithIdx.fold (fun l m -> Dom.Mem.join m (add_val_rec l m 0)) ret_val_powloc mem
    in
    Domain.add ret_var ret_val new_mem


  let instantiate_mem (ret_id, _) callee_formals callee_pname params location bo_mem mem
      callee_exit_mem =
    instantiate_ret ret_id callee_formals callee_pname params location bo_mem callee_exit_mem mem
    |> instantiate_param callee_formals params bo_mem callee_exit_mem


  let exec_instr : Domain.t -> analysis_data -> CFG.Node.t -> Sil.instr -> Domain.t =
   fun mem {interproc= {proc_desc; tenv} as interproc; get_summary; get_formals} node instr ->
    let bo_inv_map =
      BufferOverrunAnalysis.cached_compute_invariant_map
        (InterproceduralAnalysis.bind_payload interproc ~f:snd)
    in
    let bo_mem_opt = BufferOverrunAnalysis.extract_state (CFG.Node.id node) bo_inv_map in
    match instr with
    | Load {id; e; typ} ->
        (* id is a pure variable. id itself is a valid loc *)
        let loc = Loc.of_id id |> Dom.LocWithIdx.of_loc in
        let v =
          Dom.PowLocWithIdx.fold
            (fun l v -> Dom.Mem.find_on_demand ~typ l mem |> Dom.Val.join v)
            (Sem.eval_locs e bo_mem_opt mem) Dom.Val.bottom
        in
        let new_mem = Dom.Mem.add loc v mem in
        let v_powloc = Dom.Val.get_powloc v in
        Dom.PowLocWithIdx.fold
          (fun l m ->
            match Dom.Mem.find_opt l m with Some _ -> m | None -> Dom.Mem.add l Dom.Val.bottom m)
          v_powloc new_mem
    | Prune _ ->
        mem
    | Store {e1; e2} ->
        (* e1 can be either PVar or LVar. *)
        let locs1 = Sem.eval_locs e1 bo_mem_opt mem in
        let v = Sem.eval e2 (CFG.Node.loc node) mem in
        Dom.PowLocWithIdx.fold (fun l m -> Dom.Mem.add l v m) locs1 mem
    | Call (((_, _) as ret), Const (Cfun callee_pname), params, location, _) -> (
        let fun_arg_list =
          List.map params ~f:(fun (exp, typ) ->
              ProcnameDispatcher.Call.FuncArg.{exp; typ; arg_payload= ()})
        in
        match Models.dispatch tenv callee_pname fun_arg_list with
        | Some {Models.exec} ->
            let pname = Procdesc.get_proc_name proc_desc in
            let node_hash = CFG.Node.hash node in
            let model_env = {Models.pname; node; node_hash; bo_mem_opt; location} in
            exec model_env ~ret mem
        | None -> (
          match
            (callee_pname, Tenv.get_summary_formals tenv ~get_summary ~get_formals callee_pname)
          with
          | callee_pname, `Found ((Some {mem= exit_mem}, _), callee_formals) ->
              instantiate_mem ret callee_formals callee_pname params location bo_mem_opt mem
                exit_mem
          | _, _ ->
              L.d_printfln_escaped "/!\\ Unknown call to %a" Procname.pp callee_pname ;
              mem ) )
    | _ ->
        mem


  let pp_session_name _node fmt = F.pp_print_string fmt "API misuse"
end

module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions)

let check_instr {interproc= {InterproceduralAnalysis.tenv; proc_desc}; get_summary; get_formals}
    bo_mem_opt mem node instr condset =
  match instr with
  | Sil.Load {e; loc} ->
      let locs =
        Sem.eval_locs e bo_mem_opt mem
        |> Dom.PowLocWithIdx.filter (function Dom.LocWithIdx.Idx (_, _) -> true | _ -> false)
      in
      if Dom.PowLocWithIdx.is_empty locs then condset
      else
        let v =
          Dom.PowLocWithIdx.fold
            (fun l v -> Dom.Mem.find l mem |> Dom.Val.join v)
            locs Dom.Val.bottom
          |> Dom.Val.get_init
        in
        if Dom.Init.equal v Dom.Init.Init |> not then
          let absloc = Dom.PowLocWithIdx.choose locs in
          Dom.CondSet.add (Dom.Cond.make_uninit absloc Dom.Init.UnInit loc) condset
        else condset
  | Sil.Call (_, Const (Cfun callee_pname), args, location, _) -> (
      let fun_arg_list =
        List.map args ~f:(fun (exp, typ) ->
            ProcnameDispatcher.Call.FuncArg.{exp; typ; arg_payload= ()})
      in
      match Models.dispatch tenv callee_pname fun_arg_list with
      | Some {Models.check} ->
          let pname = Procdesc.get_proc_name proc_desc in
          let node_hash = CFG.Node.hash node in
          let model_env = {Models.pname; node; node_hash; bo_mem_opt; location} in
          check model_env mem condset
      | None -> (
        match (get_summary callee_pname, get_formals callee_pname) with
        | Some (Some api_summary, Some _), Some callee_formals ->
            let eval_sym = make_subst callee_formals args location bo_mem_opt mem Dom.Subst.empty in
            L.d_printfln_escaped "Callee summary %a" Dom.Summary.pp api_summary ;
            Dom.CondSet.subst eval_sym mem api_summary.Dom.Summary.condset
            |> Dom.CondSet.join condset
        | _ ->
            condset ) )
  | _ ->
      condset


let collect_instrs analysis_data bo_mem mem node instrs condset =
  if Instrs.is_empty instrs then condset
  else
    let instr = Instrs.nth_exn instrs 0 in
    check_instr analysis_data bo_mem mem node instr condset


let collect_node ({interproc} as analysis_data) inv_map node condset =
  let bo_mem =
    BufferOverrunAnalysis.cached_compute_invariant_map
      (InterproceduralAnalysis.bind_payload interproc ~f:snd)
    |> BufferOverrunAnalysis.extract_state (CFG.Node.id node)
  in
  match Analyzer.extract_pre (CFG.Node.id node) inv_map with
  | Some mem ->
      let instrs = CFG.instrs node in
      collect_instrs analysis_data bo_mem mem node instrs condset
  | None ->
      condset


let collect analysis_data inv_map cfg =
  CFG.fold_nodes cfg
    ~f:(fun condset node -> collect_node analysis_data inv_map node condset)
    ~init:Dom.CondSet.empty


let report {interproc= {InterproceduralAnalysis.proc_desc; err_log}} condset =
  Dom.CondSet.fold
    (fun cond condset ->
      if Dom.Cond.is_symbolic cond || Dom.Cond.is_reported cond then Dom.CondSet.add cond condset
      else
        let loc = Dom.Cond.get_location cond in
        match cond with
        | Dom.Cond.UnInit _ when Dom.Cond.is_init cond |> not ->
            Reporting.log_issue proc_desc err_log ~loc APIMisuse IssueType.api_misuse "UnInit" ;
            Dom.CondSet.add (Dom.Cond.reported cond) condset
        | Dom.Cond.Overflow c when Dom.Cond.may_overflow cond ->
            let ltr_set = TraceSet.make_err_trace c.traces |> Option.some in
            Reporting.log_issue proc_desc err_log ~loc ~ltr_set APIMisuse IssueType.api_misuse
              "Overflow" ;
            Dom.CondSet.add (Dom.Cond.reported cond) condset
        | Dom.Cond.Format c when Dom.Cond.is_user_input cond ->
            let ltr_set = TraceSet.make_err_trace c.traces |> Option.some in
            let _ = F.printf "report loc : %a\n\n" Location.pp_file_pos loc in
            Reporting.log_issue proc_desc err_log ~loc ~ltr_set APIMisuse IssueType.api_misuse
              "Format" ;
            Dom.CondSet.add (Dom.Cond.reported cond) condset
        | _ ->
            Dom.CondSet.add cond condset)
    condset Dom.CondSet.empty


let compute_summary analysis_data cfg inv_map =
  let exit_node_id = CFG.exit_node cfg |> CFG.Node.id in
  match Analyzer.extract_post exit_node_id inv_map with
  | Some mem ->
      let condset = collect analysis_data inv_map cfg |> report analysis_data in
      Some (Dom.Summary.make mem condset)
  | None ->
      None


let initial_state {interproc} start_node =
  let bo_inv_map =
    BufferOverrunAnalysis.cached_compute_invariant_map
      (InterproceduralAnalysis.bind_payload interproc ~f:snd)
  in
  match BufferOverrunAnalysis.extract_state (CFG.Node.id start_node) bo_inv_map with
  | Some bomem ->
      BoDomain.Mem.fold
        ~f:(fun l v mem ->
          let loc = Dom.LocWithIdx.of_loc l in
          BoDomain.Val.get_all_locs v |> Dom.PowLocWithIdx.of_pow_loc |> Dom.Val.of_pow_loc
          |> Fun.flip (Dom.Mem.add loc) mem)
        bomem.post APIMisuseDomain.Mem.initial
  | None ->
      APIMisuseDomain.Mem.initial


let checker ({InterproceduralAnalysis.proc_desc; analyze_dependency} as analysis_data) =
  BufferOverrunAnalysis.cached_compute_invariant_map
    (InterproceduralAnalysis.bind_payload analysis_data ~f:snd)
  |> ignore ;
  let open IOption.Let_syntax in
  let cfg = CFG.from_pdesc proc_desc in
  let get_summary proc_name = analyze_dependency proc_name >>| snd in
  let get_formals callee_pname =
    AnalysisCallbacks.get_proc_desc callee_pname >>| Procdesc.get_pvar_formals
  in
  let analysis_data = {interproc= analysis_data; get_summary; get_formals} in
  let initial = initial_state analysis_data (CFG.start_node cfg) in
  let inv_map = Analyzer.exec_pdesc analysis_data ~initial proc_desc in
  compute_summary analysis_data cfg inv_map
