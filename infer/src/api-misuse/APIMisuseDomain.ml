module F = Format

module Init = struct
  type t = Bot | Init | UnInit | Top [@@deriving compare, equal]

  let bottom = Bot

  let join x y =
    match (x, y) with
    | Bot, _ ->
        y
    | _, Bot ->
        x
    | Top, _ | _, Top ->
        Top
    | _, _ ->
        if equal x y then x else Top


  let widen ~prev ~next ~num_iters:_ = join prev next

  let leq ~lhs ~rhs =
    match (lhs, rhs) with
    | Bot, _ | _, Top ->
        true
    | _, _ when equal lhs rhs ->
        true
    | _, _ ->
        false


  let pp fmt = function
    | Bot ->
        F.fprintf fmt "Bot"
    | UnInit ->
        F.fprintf fmt "UnInit"
    | Init ->
        F.fprintf fmt "Init"
    | Top ->
        F.fprintf fmt "Top"
end

module LocWithIdx = struct
  module Loc = AbsLoc.Loc

  type t = Loc of Loc.t | Idx of Loc.t * Itv.t [@@deriving compare]

  let of_loc l = Loc l

  let append_idx l i =
    match l with
    | Loc l ->
        Idx (l, i)
    | _ ->
        prerr_endline "append_idx" ;
        assert false


  let pp fmt = function
    | Loc l ->
        AbsLoc.Loc.pp fmt l
    | Idx (l, i) ->
        F.fprintf fmt "%a[%a]" Loc.pp l Itv.pp i
end

module PowLocWithIdx = struct
  include PrettyPrintable.MakePPSet (LocWithIdx)

  let bottom = empty

  let join = union

  let widen ~prev ~next ~num_iters:_ = join prev next

  let leq ~lhs ~rhs = subset lhs rhs
end

module Val = struct
  type t = {powloc: PowLocWithIdx.t; init: Init.t} [@@deriving compare]

  let bottom = {powloc= PowLocWithIdx.bottom; init= Init.bottom}

  let of_pow_loc powloc = {powloc; init= Init.bottom}

  let of_init init = {powloc= PowLocWithIdx.empty; init}

  let get_powloc v = v.powloc

  let get_init v = v.init

  let join lhs rhs =
    {powloc= PowLocWithIdx.join lhs.powloc rhs.powloc; init= Init.join lhs.init rhs.init}


  let widen ~prev ~next ~num_iters =
    { powloc= PowLocWithIdx.widen ~prev:prev.powloc ~next:next.powloc ~num_iters
    ; init= Init.widen ~prev:prev.init ~next:next.init ~num_iters }


  let leq ~lhs ~rhs =
    PowLocWithIdx.leq ~lhs:lhs.powloc ~rhs:rhs.powloc && Init.leq ~lhs:lhs.init ~rhs:rhs.init


  let pp fmt v = F.fprintf fmt "{powloc: %a, init: %a}" PowLocWithIdx.pp v.powloc Init.pp v.init
end

module Mem = struct
  include AbstractDomain.Map (LocWithIdx) (Val)

  let initial = empty

  let find k m = try find k m with _ -> Val.bottom
end

module Summary = Mem
