open! IStd
module Dom = APIMisuseDomain
module Mem = APIMisuseDomain.Mem

let rec eval_locs : Exp.t -> Mem.t -> Dom.PowLocWithIdx.t =
 fun exp mem ->
  match exp with
  | Var id ->
      Var.of_id id |> AbsLoc.Loc.of_var |> Dom.LocWithIdx.of_loc |> Fun.flip Mem.find mem
      |> Dom.Val.get_powloc
  | Lvar pvar ->
      pvar |> AbsLoc.Loc.of_pvar |> Dom.LocWithIdx.of_loc |> Fun.flip Mem.find mem
      |> Dom.Val.get_powloc
  | _ ->
      Dom.PowLocWithIdx.empty
