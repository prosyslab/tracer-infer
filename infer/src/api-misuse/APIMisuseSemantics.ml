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


let rec eval_locs exp bo_mem mem =
  match exp with
  | Exp.Var id ->
      Var.of_id id |> AbsLoc.Loc.of_var |> Dom.LocWithIdx.of_loc |> Fun.flip Mem.find mem
      |> Val.get_powloc
  | Exp.Lvar _ ->
      (* In Inferbo, there are two kinds of Lvar, stack variable and heap variable. We follow the concept *)
      bo_eval_locs exp bo_mem
  | Exp.Lindex (e1, _) ->
      bo_eval_locs e1 bo_mem
  | Exp.Lfield _ ->
      bo_eval_locs exp bo_mem
  | _ ->
      Dom.PowLocWithIdx.empty


and eval exp loc mem =
  match exp with
  | Exp.Var id ->
      Var.of_id id |> AbsLoc.Loc.of_var |> Dom.LocWithIdx.of_loc |> Fun.flip Mem.find mem
  | Exp.Lvar pvar ->
      pvar |> AbsLoc.Loc.of_pvar |> Dom.LocWithIdx.of_loc |> Fun.flip Mem.find mem
  | Exp.Const _ ->
      Dom.Init.Init |> Val.of_init
  | Exp.BinOp (bop, e1, e2) ->
      eval_binop bop e1 e2 loc mem
  | Exp.UnOp (uop, e, _) ->
      eval_unop uop e loc mem
  | Exp.Cast (_, e1) ->
      eval e1 loc mem
  | Exp.Lindex (e1, _) ->
      eval e1 loc mem
  | _ ->
      (* TODO *)
      Val.bottom


and eval_binop bop e1 e2 loc mem =
  let v1 = eval e1 loc mem in
  let v2 = eval e2 loc mem in
  let traces =
    if TraceSet.is_empty v1.Val.traces |> not then
      TraceSet.append (Trace.make_binop loc) v1.Val.traces
    else if TraceSet.is_empty v2.Val.traces |> not then
      TraceSet.append (Trace.make_binop loc) v2.Val.traces
    else TraceSet.empty
  in
  match bop with
  | Binop.Shiftlt | Binop.PlusA _ | Binop.Mult _ ->
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
      ; traces }
  | _ ->
      { Val.bottom with
        powloc= Dom.PowLocWithIdx.join v1.Val.powloc v2.Val.powloc
      ; Val.init= Dom.Init.join v1.Val.init v2.Val.init
      ; user_input= Dom.UserInput.join v1.Val.user_input v2.Val.user_input
      ; int_overflow= Dom.IntOverflow.join v1.Val.int_overflow v2.Val.int_overflow
      ; traces }


and eval_unop _ e loc mem = eval e loc mem
