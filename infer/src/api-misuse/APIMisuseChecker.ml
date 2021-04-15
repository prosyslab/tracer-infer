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
  ; get_formals: Procname.t -> (Pvar.t * Typ.t) list option
  ; all_proc: ProcAttributes.t list }

let symbol_subst sym p exp typ_exp location bo_mem mem =
  let ({Dom.Val.powloc; _} as v) = Sem.eval exp location bo_mem mem in
  match sym with
  | BufferOverrunField.Prim (SPath.Deref (_, Prim (Deref (_, Prim (Deref (_, p2)))))) ->
      let {Dom.Val.powloc; _} =
        Dom.PowLocWithIdx.fold
          (fun l v -> Dom.Mem.find l mem |> Dom.Val.join v)
          powloc Dom.Val.bottom
      in
      let deref2_subst_val =
        Dom.PowLocWithIdx.fold
          (fun l v -> Dom.Mem.find l mem |> Dom.Val.join v)
          powloc Dom.Val.bottom
      in
      L.(debug Analysis Verbose) "v: %a\n" Dom.Val.pp v ;
      L.d_printfln_escaped "Path *** %a =? %a -> %a" Symb.SymbolPath.pp_partial sym
        Symb.SymbolPath.pp_partial p Dom.Val.pp deref2_subst_val ;
      L.(debug Analysis Verbose)
        "Path *** %a =? %a -> %a\n" Symb.SymbolPath.pp_partial p2 Symb.SymbolPath.pp_partial p
        Dom.Val.pp deref2_subst_val ;
      if SPath.equal_partial p p2 then
        let _ = L.d_printfln_escaped "subst" in
        let _ = L.(debug Analysis Verbose) "subst\n" in
        Some deref2_subst_val
      else None
  | BufferOverrunField.Prim (SPath.Deref (_, Prim (Deref (_, p2)))) ->
      let deref2_subst_val =
        Dom.PowLocWithIdx.fold
          (fun l v -> Dom.Mem.find_on_demand l mem |> Dom.Val.join v)
          powloc Dom.Val.bottom
      in
      L.(debug Analysis Verbose) "v: %a\n" Dom.Val.pp v ;
      L.d_printfln_escaped "Path ** %a =? %a -> %a" Symb.SymbolPath.pp_partial sym
        Symb.SymbolPath.pp_partial p Dom.Val.pp deref2_subst_val ;
      L.(debug Analysis Verbose)
        "Path ** %a =? %a -> %a\n" Symb.SymbolPath.pp_partial p2 Symb.SymbolPath.pp_partial p
        Dom.Val.pp deref2_subst_val ;
      if SPath.equal_partial p p2 then
        let _ = L.d_printfln_escaped "subst" in
        let _ = L.(debug Analysis Verbose) "subst\n" in
        Some deref2_subst_val
      else None
  | BufferOverrunField.Prim (SPath.Deref (_, p2)) ->
      let deref_subst_val =
        Dom.PowLocWithIdx.fold
          (fun l v -> Dom.Mem.find_on_demand l mem |> Dom.Val.join v)
          (Dom.Val.get_powloc v) Dom.Val.bottom
      in
      L.d_printfln_escaped "Path * %a =? %a -> %a" Symb.SymbolPath.pp_partial sym
        Symb.SymbolPath.pp_partial p Dom.Val.pp v ;
      L.(debug Analysis Verbose)
        "Path * %a =? %a -> %a" Symb.SymbolPath.pp_partial sym Symb.SymbolPath.pp_partial p
        Dom.Val.pp v ;
      if SPath.equal_partial p p2 then
        let _ = L.d_printfln_escaped "subst" in
        Some deref_subst_val
      else None
  | BufferOverrunField.Field {prefix; fn; typ} -> (
    match prefix with
    | BufferOverrunField.Prim (SPath.Deref (_, prefix_deref)) ->
        if SPath.equal_partial p prefix_deref then
          let lfield_exp = Exp.Lfield (exp, fn, typ_exp) in
          let lfield_exp_powloc = Sem.eval_locs lfield_exp location bo_mem mem in
          Some
            (Dom.PowLocWithIdx.fold
               (fun l v -> Dom.Mem.find_on_demand ?typ l mem |> Dom.Val.join v)
               lfield_exp_powloc Dom.Val.bottom)
        else None
    | _ ->
        None )
  | _ ->
      L.d_printfln_escaped "Path %a =? %a -> %a" Symb.SymbolPath.pp_partial sym
        Symb.SymbolPath.pp_partial p Dom.Val.pp v ;
      if SPath.equal_partial sym p then Some v else None


let make_subst_traces callee_pname p exp typ_exp location bo_mem mem subst_traces s =
  TraceSet.fold
    (fun trace set ->
      match Trace.last_elem trace with
      | Some (Trace.SymbolDecl l) -> (
        match Loc.get_path l with
        | Some sym -> (
            L.d_printfln_escaped "make_subst_traces %a" Symb.SymbolPath.pp_partial sym ;
            match symbol_subst sym p exp typ_exp location bo_mem mem with
            | Some v ->
                let substed_traces = Dom.Val.get_traces v in
                L.d_printfln_escaped "traces set: %a\n" TraceSet.pp substed_traces ;
                TraceSet.fold
                  (fun t set ->
                    let t =
                      Trace.concat (Trace.make_call callee_pname location |> Trace.make_singleton) t
                    in
                    let t = Trace.concat trace t in
                    TraceSet.add t set)
                  substed_traces set
            | _ ->
                TraceSet.add trace set )
        | _ ->
            TraceSet.add trace set )
      | _ ->
          TraceSet.add trace set)
    s TraceSet.empty
  |> subst_traces


let make_subst_user_input p exp typ_exp location bo_mem mem subst_user_input s =
  Dom.UserInput.Set.fold
    (fun elem s ->
      match elem with
      | Symbol sym -> (
        match symbol_subst sym p exp typ_exp location bo_mem mem with
        | Some v ->
            Dom.Val.get_user_input v |> Dom.UserInput.join s
        | None ->
            Dom.UserInput.Set.add elem s )
      | _ ->
          Dom.UserInput.Set.add elem s)
    s Dom.UserInput.bottom
  |> subst_user_input


let loc_of_symbol s = Allocsite.make_symbol s |> Loc.of_allocsite

let make_subst_powloc p exp typ_exp location bo_mem mem _subst_powloc s =
  match Loc.get_path s with
  | Some sym -> (
    match symbol_subst sym p exp typ_exp location bo_mem mem with
    | Some _ ->
        AbsLoc.PowLoc.singleton s
    | None ->
        AbsLoc.PowLoc.singleton s )
  | None ->
      AbsLoc.PowLoc.singleton s


let make_subst_int_overflow p exp typ_exp location bo_mem mem subst_int_overflow s =
  ( match s with
  | Dom.IntOverflow.Symbol sym -> (
    match symbol_subst sym p exp typ_exp location bo_mem mem with
    | Some v ->
        Dom.Val.get_int_overflow v
    | None ->
        s )
  | _ ->
      s )
  |> subst_int_overflow


let make_subst_int_underflow p exp typ_exp location bo_mem mem subst_int_underflow s =
  ( match s with
  | Dom.IntOverflow.Symbol sym -> (
    match symbol_subst sym p exp typ_exp location bo_mem mem with
    | Some v ->
        Dom.Val.get_int_underflow v
    | None ->
        s )
  | _ ->
      s )
  |> subst_int_underflow


let rec make_subst callee_pname formals actuals location bo_mem mem
    ( { Dom.Subst.subst_powloc
      ; subst_int_overflow
      ; subst_int_underflow
      ; subst_user_input
      ; subst_traces } as subst ) =
  match (formals, actuals) with
  | (pvar, _) :: t1, (exp, typ_exp) :: t2 -> (
    match pvar |> Loc.of_pvar |> Loc.get_path with
    | Some p ->
        let ({Dom.Val.int_overflow; user_input; _} as v_exp) = Sem.eval exp location bo_mem mem in
        L.d_printfln_escaped "make subst: %a %a\n" SPath.pp_partial p Dom.Val.pp v_exp ;
        L.d_printfln_escaped "make subst int overflow: %a" Dom.IntOverflow.pp int_overflow ;
        L.d_printfln_escaped "make subst user input: %a" Dom.UserInput.pp user_input ;
        { Dom.Subst.subst_powloc
        ; subst_int_overflow=
            make_subst_int_overflow p exp typ_exp location bo_mem mem subst_int_overflow
        ; subst_int_underflow=
            make_subst_int_underflow p exp typ_exp location bo_mem mem subst_int_underflow
        ; subst_user_input= make_subst_user_input p exp typ_exp location bo_mem mem subst_user_input
        ; subst_traces=
            make_subst_traces callee_pname p exp typ_exp location bo_mem mem subst_traces }
        |> make_subst callee_pname t1 t2 location bo_mem mem
    | _ ->
        subst )
  | _, _ ->
      subst


module TransferFunctions = struct
  module CFG = CFG
  module Domain = APIMisuseDomain.Mem

  type nonrec analysis_data = analysis_data

  open AbsLoc

  let instantiate_param subst callee_formals params
      (bo_mem : GOption.some BoDomain.Mem.t0 AbstractInterpreter.State.t option) location
      callee_exit_mem mem =
    List.fold2 callee_formals params ~init:mem ~f:(fun mem (p, _) (e, _) ->
        match (p |> Loc.of_pvar |> Loc.get_path, e) with
        | Some formal, exp -> (
            let param_powloc =
              (match bo_mem with Some bomem -> BoSemantics.eval_locs e bomem.pre | _ -> PowLoc.bot)
              |> Dom.PowLocWithIdx.of_pow_loc
            in
            let deref_sym = formal |> SPath.deref ~deref_kind:SPath.Deref_CPointer in
            let deref_formal_loc = Dom.LocWithIdx.of_symbol deref_sym in
            let mem =
              Dom.PowLocWithIdx.fold
                (fun loc mem ->
                  Dom.Mem.fold
                    (fun k v mem ->
                      if Dom.LocWithIdx.field_of k deref_formal_loc then
                        Dom.Mem.weak_update (Dom.LocWithIdx.replace_prefix k loc) v mem
                      else mem)
                    callee_exit_mem mem)
                param_powloc mem
            in
            match Domain.find_opt deref_formal_loc callee_exit_mem with
            | Some v ->
                L.d_printfln_escaped "\nInstantiate_param" ;
                let param_val = Sem.eval exp location bo_mem mem in
                let v =
                  let substed_v = Dom.Val.subst subst v in
                  {substed_v with traces= TraceSet.concat param_val.traces substed_v.traces}
                in
                L.d_printfln_escaped "Formal loc: %a" Dom.LocWithIdx.pp deref_formal_loc ;
                L.d_printfln_escaped "Param Value: %a" Dom.Val.pp param_val ;
                L.d_printfln_escaped "Value: %a" Dom.Val.pp v ;
                L.d_printfln_escaped "Param Powloc %a" Dom.PowLocWithIdx.pp param_powloc ;
                let param_var = Dom.Val.get_powloc param_val in
                let joined_var = Dom.PowLocWithIdx.join param_var param_powloc in
                Dom.PowLocWithIdx.fold (fun l mem -> Domain.weak_update l v mem) joined_var mem
                (* TODO : field of param update *)
            | None ->
                (* if parameter is not touched in the callee, skip *)
                mem )
        | _, _ ->
            mem)
    |> function
    | IStd.List.Or_unequal_lengths.Ok result_mem ->
        result_mem
    | IStd.List.Or_unequal_lengths.Unequal_lengths ->
        mem


  let instantiate_ret subst ret_id callee_pname callee_exit_mem mem =
    let ret_var = ret_id |> Loc.of_id |> Dom.LocWithIdx.of_loc in
    L.d_printfln_escaped "\nInstantiate_return" ;
    let ret_val =
      Domain.find
        (Loc.of_pvar (Pvar.get_ret_pvar callee_pname) |> Dom.LocWithIdx.of_loc)
        callee_exit_mem
    in
    let ret_val = ret_val |> Dom.Val.subst subst in
    let rec add_val_rec var present_mem present_depth =
      if present_depth > 2 then present_mem
      else
        let add_val = Domain.find var callee_exit_mem |> Dom.Val.subst subst in
        let add_val_powloc = Dom.Val.get_powloc add_val in
        let new_mem =
          Dom.PowLocWithIdx.fold
            (fun l m -> Dom.Mem.join m (add_val_rec l m (present_depth + 1)))
            add_val_powloc present_mem
        in
        Domain.weak_update var add_val new_mem
    in
    let ret_val_powloc = Dom.Val.get_powloc ret_val in
    let new_mem =
      let field_update_mem =
        Dom.Mem.fold
          (fun l _ m ->
            let l_is_field =
              Dom.PowLocWithIdx.exists (fun ret_l -> Dom.LocWithIdx.field_of l ret_l) ret_val_powloc
            in
            if l_is_field then add_val_rec l m 0 else m)
          callee_exit_mem mem
      in
      Dom.PowLocWithIdx.fold
        (fun l m -> Dom.Mem.join m (add_val_rec l m 0))
        ret_val_powloc field_update_mem
    in
    Domain.weak_update ret_var ret_val new_mem


  let instantiate_mem (ret_id, _) callee_formals callee_pname params location bo_mem mem
      callee_exit_mem =
    let subst = make_subst callee_pname callee_formals params location bo_mem mem Dom.Subst.empty in
    instantiate_ret subst ret_id callee_pname callee_exit_mem mem
    |> instantiate_param subst callee_formals params bo_mem location callee_exit_mem


  let exec_instr : Domain.t -> analysis_data -> CFG.Node.t -> Sil.instr -> Domain.t =
   fun mem {interproc= {proc_desc; tenv} as interproc; get_summary; get_formals; all_proc} node
       instr ->
    let bo_inv_map =
      BufferOverrunAnalysis.cached_compute_invariant_map
        (InterproceduralAnalysis.bind_payload interproc ~f:snd)
    in
    let bo_mem_opt = BufferOverrunAnalysis.extract_state (CFG.Node.id node) bo_inv_map in
    let user_call ret callee_pname params location =
      match (callee_pname, get_summary callee_pname, get_formals callee_pname) with
      | callee_pname, Some (Some {mem= exit_mem}, _), Some callee_formals ->
          instantiate_mem ret callee_formals callee_pname params location bo_mem_opt mem exit_mem
      | _, _, _ ->
          let caller_pname = Procdesc.get_proc_name proc_desc in
          L.d_printfln_escaped "/!\\ Unknown call to %a from %a" Procname.pp callee_pname
            Procname.pp caller_pname ;
          L.(debug Analysis Verbose)
            "Unknown call to: %a from %a\n" Procname.pp callee_pname Procname.pp caller_pname ;
          mem
    in
    let location = CFG.Node.loc node in
    match instr with
    | Load {id; e; typ; _} ->
        (* id is a pure variable. id itself is a valid loc *)
        let id_loc = Loc.of_id id |> Dom.LocWithIdx.of_loc in
        let locs = Sem.eval_locs e location bo_mem_opt mem in
        let v, mem =
          Dom.PowLocWithIdx.fold
            (fun l (v, mem) ->
              let v', mem = Dom.Mem.find_init_on_demand ~typ l mem in
              (Dom.Val.join v v', mem))
            locs (Dom.Val.bottom, mem)
        in
        Dom.Mem.add id_loc v mem
    | Prune (exp, location, branch, if_kind) ->
        Sem.Prune.prune exp location bo_mem_opt mem branch if_kind
    | Store {e1; e2} ->
        (* e1 can be either PVar or LVar. *)
        let locs1 = Sem.eval_locs e1 location bo_mem_opt mem in
        let v = Sem.eval e2 location bo_mem_opt mem in
        let v = {v with traces= TraceSet.append (Trace.make_store e1 e2 location) v.traces} in
        Dom.PowLocWithIdx.fold (fun l m -> Dom.Mem.update l v m) locs1 mem
    | Call (ret, Const (Cfun callee_pname), params, location, _) -> (
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
        | None ->
            user_call ret callee_pname params location )
    | Call (((_, ret_typ) as ret), _, params, location, _) ->
        let candidates = BufferOverrunUtils.get_func_candidates proc_desc all_proc ret_typ params in
        List.iter
          ~f:(fun att ->
            L.d_printfln_escaped "candidate functions: %a\n" Procname.pp
              (ProcAttributes.get_proc_name att))
          candidates ;
        List.fold_left candidates
          ~f:(fun mem att ->
            let callee_pname = ProcAttributes.get_proc_name att in
            user_call ret callee_pname params location |> APIMisuseDomain.Mem.join mem)
          ~init:mem
    | Metadata (ExitScope (dead_vars, _)) ->
        Dom.Mem.remove_temps (List.filter_map dead_vars ~f:Var.get_ident) mem
    | _ ->
        mem


  let pp_session_name _node fmt = F.pp_print_string fmt "API misuse"
end

module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions)

let check_instr
    {interproc= {InterproceduralAnalysis.tenv; proc_desc}; get_summary; get_formals; all_proc}
    bo_mem_opt mem node instr condset =
  let user_call callee_pname params location =
    match (get_summary callee_pname, get_formals callee_pname) with
    | Some (Some api_summary, Some _), Some callee_formals ->
        let eval_sym =
          make_subst callee_pname callee_formals params location bo_mem_opt mem Dom.Subst.empty
        in
        L.d_printfln_escaped "Callee summary %a" Dom.Summary.pp api_summary ;
        Dom.CondSet.subst eval_sym mem api_summary.Dom.Summary.condset |> Dom.CondSet.join condset
    | _ ->
        condset
  in
  match instr with
  | Sil.Load {e; loc} ->
      let locs =
        Sem.eval_locs e loc bo_mem_opt mem
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
      | None ->
          user_call callee_pname args location )
  | Sil.Call ((_, ret_typ), _, params, location, _) ->
      BufferOverrunUtils.get_func_candidates proc_desc all_proc ret_typ params
      |> List.fold_left
           ~f:(fun condset att ->
             let callee_pname = ProcAttributes.get_proc_name att in
             user_call callee_pname params location |> APIMisuseDomain.CondSet.join condset)
           ~init:condset
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
        L.(debug Analysis Verbose) "alarm start %a\n" Location.pp loc ;
        let report_src_sink_pair cond ~ltr_set (bug_type : string) =
          match Dom.Cond.extract_user_input cond with
          | Some (Source (_, src_loc)) ->
              L.(debug Analysis Verbose) "alarm %a\n" Location.pp src_loc ;
              let src_loc' =
                Jsonbug_t.
                  { file= SourceFile.to_string src_loc.file
                  ; lnum= src_loc.line
                  ; cnum= src_loc.col
                  ; enum= 0 }
              in
              let extras =
                Jsonbug_t.
                  { nullsafe_extra= None
                  ; cost_polynomial= None
                  ; cost_degree= None
                  ; bug_src_loc= Some src_loc' }
              in
              let ltr_set = Trace.subset_match_src src_loc ltr_set in
              Reporting.log_issue proc_desc err_log ~loc ~ltr_set ~extras APIMisuse
                IssueType.api_misuse bug_type
          | _ ->
              L.(debug Analysis Verbose) "no alarm \n" ;
              ()
        in
        match cond with
        | Dom.Cond.UnInit _ when Dom.Cond.is_init cond |> not ->
            Reporting.log_issue proc_desc err_log ~loc APIMisuse IssueType.api_misuse "UnInit" ;
            Dom.CondSet.add (Dom.Cond.reported cond) condset
        | Dom.Cond.IntOverflow c when Dom.Cond.may_overflow cond ->
            let ltr_set = TraceSet.make_err_trace c.traces |> Option.some in
            report_src_sink_pair cond ~ltr_set "IntOverflow" ;
            Dom.CondSet.add (Dom.Cond.reported cond) condset
        | Dom.Cond.IntUnderflow c when Dom.Cond.may_underflow cond ->
            L.(debug Analysis Verbose) "may under flow alarm \n" ;
            let ltr_set = TraceSet.make_err_trace c.traces |> Option.some in
            report_src_sink_pair cond ~ltr_set "IntUnderflow" ;
            Dom.CondSet.add (Dom.Cond.reported cond) condset
        | Dom.Cond.FormatString c when Dom.Cond.is_user_input cond ->
            let ltr_set = TraceSet.make_err_trace c.traces |> Option.some in
            report_src_sink_pair cond ~ltr_set "FormatString" ;
            Dom.CondSet.add (Dom.Cond.reported cond) condset
        | Dom.Cond.BufferOverflow c when Dom.Cond.is_user_input cond ->
            let ltr_set = TraceSet.make_err_trace c.traces |> Option.some in
            report_src_sink_pair cond ~ltr_set "BufferOverflow" ;
            Dom.CondSet.add (Dom.Cond.reported cond) condset
        | Dom.Cond.CmdInjection c when Dom.Cond.is_user_input cond ->
            let ltr_set = TraceSet.make_err_trace c.traces |> Option.some in
            report_src_sink_pair cond ~ltr_set "CmdInjection" ;
            Dom.CondSet.add (Dom.Cond.reported cond) condset
        | _ ->
            L.(debug Analysis Verbose) "no may under flow alarm \n" ;
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


let initialize_cmd_args start_node formals mem =
  match formals with
  | Some [(_, _); (argv, _)] -> (
    match argv |> Loc.of_pvar |> Loc.get_path with
    | Some formal ->
        let location = CFG.Node.loc start_node in
        let deref2_formal_loc =
          formal
          |> SPath.deref ~deref_kind:SPath.Deref_CPointer
          |> SPath.deref ~deref_kind:SPath.Deref_CPointer
          |> Allocsite.make_symbol |> Loc.of_allocsite |> Dom.LocWithIdx.of_loc
        in
        let traces =
          Trace.make_input (Procname.from_string_c_fun "main") location
          |> Trace.make_singleton |> TraceSet.singleton
        in
        let v2 = Dom.UserInput.make start_node location |> Dom.Val.of_user_input ~traces in
        let deref_formal_loc1 =
          formal
          |> SPath.deref ~deref_kind:SPath.Deref_CPointer
          |> Allocsite.make_symbol |> Loc.of_allocsite |> Dom.LocWithIdx.of_loc
        in
        let v1 = deref2_formal_loc |> Dom.PowLocWithIdx.singleton |> Dom.Val.of_pow_loc in
        let formal_loc = Loc.of_pvar argv |> Dom.LocWithIdx.of_loc in
        let v = deref_formal_loc1 |> Dom.PowLocWithIdx.singleton |> Dom.Val.of_pow_loc in
        Dom.Mem.add formal_loc v mem |> Dom.Mem.add deref_formal_loc1 v1
        |> Dom.Mem.add deref2_formal_loc v2
    | None ->
        mem )
  | _ ->
      mem


let initial_state {interproc= {proc_desc} as interproc; get_formals} start_node =
  let bo_inv_map =
    BufferOverrunAnalysis.cached_compute_invariant_map
      (InterproceduralAnalysis.bind_payload interproc ~f:snd)
  in
  let pname = Procdesc.get_proc_name proc_desc in
  let initial =
    if Procname.get_method pname |> String.equal "main" then
      initialize_cmd_args start_node (get_formals pname) APIMisuseDomain.Mem.initial
    else APIMisuseDomain.Mem.initial
  in
  match BufferOverrunAnalysis.extract_state (CFG.Node.id start_node) bo_inv_map with
  | Some bomem ->
      BoDomain.Mem.fold
        ~f:(fun l v mem ->
          let loc = Dom.LocWithIdx.of_loc l in
          BoDomain.Val.get_all_locs v |> Dom.PowLocWithIdx.of_pow_loc |> Dom.Val.of_pow_loc
          |> Fun.flip (Dom.Mem.add loc) mem)
        bomem.post initial
  | None ->
      initial


let should_skip proc_desc =
  let node = CFG.Node.loc (CFG.start_node proc_desc) in
  let pname = Procdesc.get_proc_name proc_desc |> Procname.get_method in
  let filename = SourceFile.to_rel_path node.file in
  let check_skip =
    List.exists ~f:(String.equal filename) Config.skip_files
    || List.exists ~f:(String.equal pname) Config.skip_functions
  in
  if check_skip then true
  else
    match (Config.only_files, Config.only_functions) with
    | [], [] ->
        false
    | _, _ ->
        (not (List.exists ~f:(String.equal pname) Config.only_functions))
        || not (List.exists ~f:(String.equal filename) Config.only_files)


let checker ({InterproceduralAnalysis.proc_desc; analyze_dependency} as analysis_data) =
  let open IOption.Let_syntax in
  if should_skip proc_desc then None
  else
    let _ =
      BufferOverrunAnalysis.cached_compute_invariant_map
        (InterproceduralAnalysis.bind_payload analysis_data ~f:snd)
    in
    let cfg = CFG.from_pdesc proc_desc in
    let get_summary proc_name = analyze_dependency proc_name >>| snd in
    let get_formals callee_pname =
      AnalysisCallbacks.proc_resolve_attributes callee_pname >>| ProcAttributes.get_pvar_formals
    in
    let all_proc = ProcAttributes.get_all () in
    let analysis_data = {interproc= analysis_data; get_summary; get_formals; all_proc} in
    let initial = initial_state analysis_data (CFG.start_node cfg) in
    let inv_map = Analyzer.exec_pdesc analysis_data ~initial proc_desc in
    compute_summary analysis_data cfg inv_map
