open! IStd
module L = Logging
module BoSemantics = BufferOverrunSemantics
module BoDomain = BufferOverrunDomain
module Dom = APIMisuseDomain
module Mem = APIMisuseDomain.Mem
module Val = Dom.Val
module Trace = APIMisuseTrace
module TraceSet = APIMisuseTrace.Set

let bo_eval_locs e bo_mem_opt =
  match (bo_mem_opt : BoDomain.Mem.t AbstractInterpreter.State.t option) with
  | Some bo_mem ->
      BoSemantics.eval_locs e bo_mem.pre |> Dom.PowLocWithIdx.of_pow_loc
  | None ->
      Dom.PowLocWithIdx.bottom


let bo_eval pvar bo_mem_opt mem =
  match (bo_mem_opt : BoDomain.Mem.t AbstractInterpreter.State.t option) with
  | Some bo_mem ->
      let loc = pvar |> AbsLoc.Loc.of_pvar in
      if BoDomain.Mem.is_stack_loc loc bo_mem.pre then
        let _ = L.d_printfln_escaped "Stack loc: %a" AbsLoc.Loc.pp loc in
        Dom.LocWithIdx.of_loc loc |> Fun.flip Mem.find mem
      else
        let _ = L.d_printfln_escaped "NonStack loc: %a" AbsLoc.Loc.pp loc in
        Dom.LocWithIdx.of_loc loc |> Dom.PowLocWithIdx.singleton |> Dom.Val.of_pow_loc
  | None ->
      pvar |> AbsLoc.Loc.of_pvar |> Dom.LocWithIdx.of_loc |> Dom.PowLocWithIdx.singleton
      |> Dom.Val.of_pow_loc


let is_one exp =
  match exp with
  | Exp.Const c ->
      Const.isone_int_float c
  | Exp.Sizeof {nbytes; _} -> (
    match nbytes with Some n -> Int.equal n 1 | None -> false )
  | Exp.Var _
  | Exp.UnOp _
  | Exp.BinOp _
  | Exp.Exn _
  | Exp.Closure _
  | Exp.Cast _
  | Exp.Lvar _
  | Exp.Lfield _
  | Exp.Lindex _ ->
      false


let check_no_overflow bop e1 e2 =
  match bop with
  | Binop.Shiftlt | Binop.PlusA _ ->
      Exp.is_zero e1 || Exp.is_zero e2
  | Binop.Mult _ ->
      is_one e1 || is_one e2
  | _ ->
      true


let check_no_underflow bop e2 = match bop with Binop.MinusA _ -> Exp.is_zero e2 | _ -> true

let rec eval_locs exp _ bo_mem mem =
  match exp with
  | Exp.Var id ->
      Var.of_id id |> AbsLoc.Loc.of_var |> Dom.LocWithIdx.of_loc |> Fun.flip Mem.find mem
      |> Val.get_powloc
  | Exp.Lvar _ ->
      (* In Inferbo, there are two kinds of Lvar, stack variable and heap variable. We follow the concept *)
      bo_eval_locs exp bo_mem
  | Exp.Lindex (_, _) | Exp.Lfield (_, _, _) ->
      bo_eval_locs exp bo_mem
  | _ ->
      Dom.PowLocWithIdx.empty


and eval exp loc bo_mem mem =
  match exp with
  | Exp.Var id ->
      Var.of_id id |> AbsLoc.Loc.of_var |> Dom.LocWithIdx.of_loc |> Fun.flip Mem.find mem
  | Exp.Lvar pvar ->
      bo_eval pvar bo_mem mem
  | Exp.Const _ ->
      Dom.Init.Init |> Val.of_init
  | Exp.BinOp (bop, e1, e2) ->
      eval_binop exp bop e1 e2 loc bo_mem mem
  | Exp.UnOp (_, e, _) ->
      eval_unop e loc bo_mem mem
  | Exp.Cast (_, e1) ->
      eval e1 loc bo_mem mem
  | Exp.Lindex (e1, _) ->
      eval e1 loc bo_mem mem
  | Exp.Lfield (e, fn, typ) ->
      let powloc_field =
        eval e loc bo_mem mem |> Dom.Val.get_powloc |> Dom.PowLocWithIdx.append_field ~typ fn
      in
      Dom.PowLocWithIdx.fold
        (fun loc v -> Dom.Mem.find loc mem |> Dom.Val.join v)
        powloc_field Dom.Val.bottom
  | _ ->
      Val.bottom


and eval_binop _ bop e1 e2 loc bo_mem mem =
  let v1 = eval e1 loc bo_mem mem in
  let v2 = eval e2 loc bo_mem mem in
  let traces = TraceSet.join v1.Val.traces v2.Val.traces in
  match bop with
  | (Binop.Shiftlt | Binop.PlusA _ | Binop.Mult _) when not (check_no_overflow bop e1 e2) ->
      let overflow v =
        if v.Val.user_input |> Dom.UserInput.is_taint || v.Val.user_input |> Dom.UserInput.is_symbol
        then Dom.IntOverflow.top
        else Dom.IntOverflow.bottom
      in
      { Val.bottom with
        powloc= Dom.PowLocWithIdx.join v1.Val.powloc v2.Val.powloc
      ; Val.init= Dom.Init.join v1.Val.init v2.Val.init
      ; user_input= Dom.UserInput.join v1.Val.user_input v2.Val.user_input
      ; int_overflow= Dom.IntOverflow.join (overflow v1) (overflow v2)
      ; int_underflow= Dom.IntUnderflow.join v1.Val.int_underflow v2.Val.int_underflow
      ; traces }
  | Binop.MinusA _ when not (check_no_underflow bop e2) ->
      let underflow v =
        if v.Val.user_input |> Dom.UserInput.is_taint || v.Val.user_input |> Dom.UserInput.is_symbol
        then Dom.IntUnderflow.top
        else Dom.IntUnderflow.bottom
      in
      { Val.bottom with
        powloc= Dom.PowLocWithIdx.join v1.Val.powloc v2.Val.powloc
      ; Val.init= Dom.Init.join v1.Val.init v2.Val.init
      ; user_input= Dom.UserInput.join v1.Val.user_input v2.Val.user_input
      ; int_overflow= Dom.IntOverflow.join v1.Val.int_overflow v2.Val.int_overflow
      ; int_underflow= Dom.IntUnderflow.join (underflow v1) (underflow v2)
      ; traces }
  | _ ->
      { Val.bottom with
        powloc= Dom.PowLocWithIdx.join v1.Val.powloc v2.Val.powloc
      ; Val.init= Dom.Init.join v1.Val.init v2.Val.init
      ; user_input= Dom.UserInput.join v1.Val.user_input v2.Val.user_input
      ; int_overflow= Dom.IntOverflow.join v1.Val.int_overflow v2.Val.int_overflow
      ; int_underflow= Dom.IntUnderflow.join v1.Val.int_underflow v2.Val.int_underflow
      ; traces }


and eval_unop e loc bo_mem mem = eval e loc bo_mem mem

module Prune = struct
  let make_not_bop bop = match Binop.negate bop with Some neg_bop -> neg_bop | None -> bop

  let make_sym_bop bop = match Binop.symmetric bop with Some sym_bop -> sym_bop | None -> bop

  let rec exp_is_const_rec = function
    | Exp.Const _ | Exp.Sizeof _ ->
        true
    | Exp.UnOp (_, e, _) ->
        exp_is_const_rec e
    | Exp.BinOp (_, e1, e2) ->
        exp_is_const_rec e1 && exp_is_const_rec e2
    | Exp.Cast (_, e) ->
        exp_is_const_rec e
    | Exp.Var _ | Exp.Exn _ | Exp.Closure _ | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ ->
        false


  let update_mem_prune_trace root (v : Dom.Val.t) location mem =
    let new_traces = TraceSet.append (Trace.make_prune root location) v.traces in
    Dom.Mem.map
      (fun ({traces; _} as iter_v) ->
        if TraceSet.equal traces v.traces then {iter_v with traces= new_traces} else iter_v)
      mem


  let rec eval_prune root exp location is_not bin_op_lst mem =
    match exp with
    | Exp.Var id ->
        let loc = AbsLoc.Loc.of_id id |> Dom.LocWithIdx.of_loc in
        let v = Dom.Mem.find loc mem in
        update_mem_prune_trace root v location mem
    | Exp.BinOp (bin_op, e1, e2) ->
        let symmetric_bop = make_sym_bop bin_op in
        let bop1, bop2 =
          if is_not then (make_not_bop bin_op, make_not_bop symmetric_bop)
          else (bin_op, symmetric_bop)
        in
        mem
        |> eval_prune root e1 location is_not ((bop1, e2 |> exp_is_const_rec) :: bin_op_lst)
        |> eval_prune root e2 location is_not ((bop2, e1 |> exp_is_const_rec) :: bin_op_lst)
    | Exp.UnOp (Unop.LNot, e, _) ->
        eval_prune root e location (not is_not) bin_op_lst mem
    | Exp.UnOp (_, e, _) | Exp.Cast (_, e) ->
        eval_prune root e location is_not bin_op_lst mem
    | Exp.Exn _
    | Exp.Closure _
    | Exp.Const _
    | Exp.Lvar _
    | Exp.Lfield (_, _, _)
    | Exp.Lindex (_, _)
    | Exp.Sizeof _ ->
        mem


  let prune exp location mem branch if_kind =
    match if_kind with
    | Sil.Ik_if | Sil.Ik_bexp ->
        eval_prune exp exp location (not branch) [] mem
    | Sil.Ik_while | Sil.Ik_dowhile | Sil.Ik_for | Sil.Ik_land_lor | Sil.Ik_switch ->
        mem
end
