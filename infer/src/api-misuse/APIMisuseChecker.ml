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
    let exec {node; inv_map} ~ret mem =
      match (map_exp, BufferOverrunAnalysis.extract_state (CFG.Node.id node) inv_map) with
      | Exp.Lvar v, Some bomem ->
          let idx_val =
            BoSemantics.eval_locs idx bomem.post
            |> Fun.flip BoDomain.Mem.find_set bomem.pre
            |> BoDomain.Val.get_itv
          in
          let retloc = fst ret |> Loc.of_id |> Dom.LocWithIdx.of_loc in
          let maploc =
            Loc.of_pvar v |> Dom.LocWithIdx.of_loc |> Fun.flip Dom.Mem.find mem
            |> Dom.Val.get_powloc
          in
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

  let exec_instr : Domain.t -> analysis_data -> CFG.Node.t -> Sil.instr -> Domain.t =
   fun mem ({proc_desc; tenv} as analysis_data) node instr ->
    match instr with
    | Load _ | Prune _ ->
        mem
    | Store {e1} ->
        let locs = Sem.eval_locs e1 mem in
        let v = APIDom.Init.Init |> APIMisuseDomain.Val.of_init in
        APIDom.PowLocWithIdx.fold (fun l m -> APIDom.Mem.add l v m) locs mem
    | Call (ret, Const (Cfun callee_pname), args, _, _) -> (
        L.(debug Analysis Quiet) "Call111111\n" ;
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
        L.(debug Analysis Quiet) "Others44444\n" ;
        mem


  let pp_session_name _node fmt = F.pp_print_string fmt "API misuse"
end

module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions)
module LocationSet = AbstractDomain.FiniteSet (Location)

let check_instr mem instr locset =
  match instr with
  | Sil.Load {e; loc} ->
      let locs =
        Sem.eval_locs e mem
        |> APIDom.PowLocWithIdx.filter (function APIDom.LocWithIdx.Idx (_, _) -> true | _ -> false)
      in
      if APIDom.PowLocWithIdx.is_empty locs then locset
      else
        let v =
          APIDom.PowLocWithIdx.fold
            (fun l v -> APIDom.Mem.find l mem |> APIDom.Val.join v)
            locs APIDom.Val.bottom
          |> APIDom.Val.get_init
        in
        if APIDom.Init.equal v APIDom.Init.Init |> not then LocationSet.add loc locset else locset
  | _ ->
      locset


let check_instrs mem instrs locset =
  if Instrs.is_empty instrs then locset
  else
    let instr = Instrs.nth_exn instrs 0 in
    check_instr mem instr locset


let check_node inv_map node locset =
  match Analyzer.extract_pre (CFG.Node.id node) inv_map with
  | Some mem ->
      let instrs = CFG.instrs node in
      check_instrs mem instrs locset
  | None ->
      locset


let report {InterproceduralAnalysis.proc_desc; err_log} cfg inv_map =
  let locset =
    CFG.fold_nodes cfg
      ~f:(fun locset node -> check_node inv_map node locset)
      ~init:LocationSet.empty
  in
  LocationSet.iter
    (fun loc ->
      Reporting.log_issue proc_desc err_log ~loc APIMisuse IssueType.api_misuse "API Misuse" )
    locset ;
  F.printf "%a\n" LocationSet.pp locset


let compute_summary cfg inv_map =
  let exit_node_id = CFG.exit_node cfg |> CFG.Node.id in
  Analyzer.extract_post exit_node_id inv_map


let checker ({InterproceduralAnalysis.proc_desc} as analysis_data) =
  BufferOverrunAnalysis.cached_compute_invariant_map
    (InterproceduralAnalysis.bind_payload analysis_data ~f:snd)
  |> ignore ;
  let cfg = CFG.from_pdesc proc_desc in
  let inv_map = Analyzer.exec_pdesc analysis_data ~initial:APIMisuseDomain.Mem.initial proc_desc in
  report analysis_data cfg inv_map ;
  compute_summary cfg inv_map
