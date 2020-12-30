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

let make_subst_traces p v location mem subst_traces s =
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
  |> subst_traces


let user_input_symbol_subst sym sym_user_input exp typ_exp v bo_mem mem subst_user_input =
  let setsymbol_sym = Dom.UserInput.make_symbol sym in
  match sym with
  | BufferOverrunField.Prim (SPath.Deref (_, p)) -> (
    match p with
    | BufferOverrunField.Prim (SPath.Deref (_, p2)) ->
        let deref2_powloc =
          Dom.Val.get_powloc v |> Dom.PowLocWithIdx.map Dom.LocWithIdx.loc_deref
        in
        let deref2_subst_val =
          Dom.PowLocWithIdx.fold
            (fun l v -> Dom.Mem.find_on_demand l mem |> Dom.Val.join v)
            deref2_powloc Dom.Val.bottom
        in
        if Dom.UserInput.equal (Dom.UserInput.make_symbol p2) sym_user_input then
          subst_user_input (Dom.Val.get_user_input deref2_subst_val)
        else subst_user_input setsymbol_sym
    | _ ->
        let deref_subst_val =
          Dom.PowLocWithIdx.fold
            (fun l v -> Dom.Mem.find_on_demand l mem |> Dom.Val.join v)
            (Dom.Val.get_powloc v) Dom.Val.bottom
        in
        if Dom.UserInput.equal (Dom.UserInput.make_symbol p) sym_user_input then
          subst_user_input (Dom.Val.get_user_input deref_subst_val)
        else subst_user_input setsymbol_sym )
  | BufferOverrunField.Field {prefix; fn; _} -> (
    match prefix with
    | BufferOverrunField.Prim (SPath.Deref (_, prefix_deref)) ->
        let prefix_sym = Dom.UserInput.make_symbol prefix_deref in
        if Dom.UserInput.equal prefix_sym sym_user_input then
          let lfield_exp = Exp.Lfield (exp, fn, typ_exp) in
          let lfield_exp_powloc = Sem.eval_locs lfield_exp bo_mem mem in
          let result =
            Dom.PowLocWithIdx.fold
              (fun l ui ->
                Dom.Mem.find_on_demand l mem |> Dom.Val.get_user_input |> Dom.UserInput.join ui)
              lfield_exp_powloc Dom.UserInput.bottom
          in
          subst_user_input result
        else subst_user_input setsymbol_sym
    | _ ->
        subst_user_input setsymbol_sym )
  | _ ->
      if Dom.UserInput.equal setsymbol_sym sym_user_input then Dom.Val.get_user_input v
      else subst_user_input setsymbol_sym


let rec make_subst formals actuals location bo_mem mem
    ({Dom.Subst.subst_powloc; subst_int_overflow; subst_user_input; subst_traces} as subst) =
  match (formals, actuals) with
  | (pvar, _) :: t1, (exp, typ_exp) :: t2 -> (
    match pvar |> Loc.of_pvar |> Loc.get_path with
    | Some p ->
        let sym_absloc = Allocsite.make_symbol p |> Loc.of_allocsite in
        let sym_int_overflow = Dom.IntOverflow.make_symbol p in
        let sym_user_input = Dom.UserInput.make_symbol p in
        L.(debug Analysis Quiet) "make subst sym: %a\n" AbsLoc.Loc.pp sym_absloc ;
        let ({Dom.Val.powloc; int_overflow; user_input; _} as v_exp) =
          Sem.eval exp location bo_mem mem
        in
        L.d_printfln_escaped "make subst: %a %a\n" SPath.pp_partial p Dom.Val.pp v_exp ;
        let powloc =
          Dom.PowLocWithIdx.fold
            (fun l s -> Dom.LocWithIdx.to_loc l |> Fun.flip AbsLoc.PowLoc.add s)
            powloc AbsLoc.PowLoc.bot
        in
        L.(debug Analysis Quiet) "make subst locs: %a\n" AbsLoc.PowLoc.pp powloc ;
        L.(debug Analysis Quiet) "make subst int overflow: %a\n" Dom.IntOverflow.pp int_overflow ;
        L.(debug Analysis Quiet) "make subst user input: %a\n" Dom.UserInput.pp user_input ;
        { Dom.Subst.subst_powloc=
            (fun s -> if AbsLoc.Loc.equal s sym_absloc then powloc else subst_powloc s)
        ; subst_int_overflow=
            (fun s ->
              if Dom.IntOverflow.equal s sym_int_overflow then int_overflow
              else subst_int_overflow s)
        ; subst_user_input=
            (fun s ->
              Dom.UserInput.Set.fold
                (fun elem s ->
                  ( match elem with
                  | Symbol sym ->
                      user_input_symbol_subst sym sym_user_input exp typ_exp v_exp bo_mem mem
                        subst_user_input
                  | _ ->
                      Dom.UserInput.make_elem elem )
                  |> Dom.UserInput.join s)
                s Dom.UserInput.bottom)
        ; subst_traces= make_subst_traces p v_exp location mem subst_traces }
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
      (bo_mem : GOption.some BoDomain.Mem.t0 AbstractInterpreter.State.t option) location
      callee_exit_mem mem =
    List.fold2 callee_formals params ~init:mem ~f:(fun m (p, _) (e, _) ->
        match (p |> Loc.of_pvar |> Loc.get_path, e) with
        | Some formal, exp ->
            let param_powloc =
              (match bo_mem with Some bomem -> BoSemantics.eval_locs e bomem.pre | _ -> PowLoc.bot)
              |> Dom.PowLocWithIdx.of_pow_loc
            in
            let deref_formal_loc =
              formal
              |> SPath.deref ~deref_kind:SPath.Deref_CPointer
              |> Allocsite.make_symbol |> Loc.of_allocsite |> Dom.LocWithIdx.of_loc
            in
            let m =
              Dom.PowLocWithIdx.fold
                (fun loc m ->
                  Dom.Mem.fold
                    (fun k v m ->
                      if Dom.LocWithIdx.field_of k deref_formal_loc then
                        Dom.Mem.weak_update (Dom.LocWithIdx.replace_prefix k loc) v m
                      else m)
                    callee_exit_mem m)
                param_powloc m
            in
            let param_val = Sem.eval exp location bo_mem mem in
            let v = Domain.find deref_formal_loc callee_exit_mem in
            let v = {v with traces= TraceSet.concat param_val.Dom.Val.traces v.Dom.Val.traces} in
            L.d_printfln_escaped "Formal loc: %a" Dom.LocWithIdx.pp deref_formal_loc ;
            L.d_printfln_escaped "Value: %a" Dom.Val.pp v ;
            L.d_printfln_escaped "Param Powloc %a" Dom.PowLocWithIdx.pp param_powloc ;
            let param_var = Dom.Val.get_powloc param_val in
            let joined_var = Dom.PowLocWithIdx.join param_var param_powloc in
            let updated_mem =
              Dom.PowLocWithIdx.fold (fun l mem -> Domain.weak_update l v mem) joined_var m
            in
            (* TODO : field of param update *)
            updated_mem
        | _, _ ->
            m)
    |> function
    | IStd.List.Or_unequal_lengths.Ok result_mem ->
        result_mem
    | IStd.List.Or_unequal_lengths.Unequal_lengths ->
        mem


  let instantiate_ret ret_id callee_formals callee_pname params location bo_mem callee_exit_mem mem
      =
    let subst = make_subst callee_formals params location bo_mem mem Dom.Subst.empty in
    let ret_var = ret_id |> Loc.of_id |> Dom.LocWithIdx.of_loc in
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
    instantiate_ret ret_id callee_formals callee_pname params location bo_mem callee_exit_mem mem
    |> instantiate_param callee_formals params bo_mem location callee_exit_mem


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
          L.(debug Analysis Quiet)
            "Unknown call to: %a from %a\n" Procname.pp callee_pname Procname.pp caller_pname ;
          mem
    in
    match instr with
    | Load {id; e; typ; loc} ->
        (* id is a pure variable. id itself is a valid loc *)
        let id_loc = Loc.of_id id |> Dom.LocWithIdx.of_loc in
        let locs = Sem.eval e loc bo_mem_opt mem |> Dom.Val.get_powloc in
        let v =
          Dom.PowLocWithIdx.fold
            (fun l v -> Dom.Mem.find_on_demand ~typ l mem |> Dom.Val.join v)
            locs Dom.Val.bottom
        in
        Dom.Mem.add id_loc v mem
    | Prune _ ->
        mem
    | Store {e1; e2} ->
        (* e1 can be either PVar or LVar. *)
        let locs1 = Sem.eval_locs e1 bo_mem_opt mem in
        let v = Sem.eval e2 (CFG.Node.loc node) bo_mem_opt mem in
        let update_func =
          match e1 with Exp.Lindex (_, _) -> Dom.Mem.weak_update | _ -> Dom.Mem.add
        in
        Dom.PowLocWithIdx.fold (fun l m -> update_func l v m) locs1 mem
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
        let eval_sym = make_subst callee_formals params location bo_mem_opt mem Dom.Subst.empty in
        L.d_printfln_escaped "Callee summary %a" Dom.Summary.pp api_summary ;
        Dom.CondSet.subst eval_sym mem api_summary.Dom.Summary.condset |> Dom.CondSet.join condset
    | _ ->
        condset
  in
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
        let report_src_sink_pair cond ~ltr_set (bug_type : string) =
          let user_input_set = Dom.Cond.extract_user_input cond in
          Dom.UserInput.Set.iter
            (fun elem ->
              match elem with
              | Source (_, src_loc) ->
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
                  ())
            user_input_set
        in
        match cond with
        | Dom.Cond.UnInit _ when Dom.Cond.is_init cond |> not ->
            Reporting.log_issue proc_desc err_log ~loc APIMisuse IssueType.api_misuse "UnInit" ;
            Dom.CondSet.add (Dom.Cond.reported cond) condset
        | Dom.Cond.Overflow c when Dom.Cond.may_overflow cond ->
            let ltr_set = TraceSet.make_err_trace c.traces |> Option.some in
            report_src_sink_pair cond ~ltr_set "Overflow" ;
            Dom.CondSet.add (Dom.Cond.reported cond) condset
        | Dom.Cond.Format c when Dom.Cond.is_user_input cond ->
            let ltr_set = TraceSet.make_err_trace c.traces |> Option.some in
            report_src_sink_pair cond ~ltr_set "Format" ;
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


let initialize_cmd_args start_node formals mem =
  match formals with
  | Some [(_, _); (argv, _)] -> (
    match argv |> Loc.of_pvar |> Loc.get_path with
    | Some formal ->
        let location = CFG.Node.loc start_node in
        let deref_formal_loc =
          formal
          |> SPath.deref ~deref_kind:SPath.Deref_CPointer
          |> SPath.deref ~deref_kind:SPath.Deref_CPointer
          |> Allocsite.make_symbol |> Loc.of_allocsite |> Dom.LocWithIdx.of_loc
        in
        let traces = [Trace.make_input location] |> TraceSet.singleton in
        let v = Dom.UserInput.make start_node location |> Dom.Val.of_user_input ~traces in
        Dom.Mem.add deref_formal_loc v mem
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
  List.exists ~f:(String.equal filename) Config.skip_files
  || List.exists ~f:(String.equal pname) Config.skip_functions


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
