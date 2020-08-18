module F = Format
module L = Logging
open AbsLoc

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

  let of_idx l i = Idx (l, i)

  let to_loc = function Loc l | Idx (l, _) -> l

  let is_symbolic = function Loc l | Idx (l, _) -> Loc.is_symbol l

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

  let matcher = QualifiedCppName.Match.of_fuzzy_qual_names ["std::map"]

  let on_demand ?typ loc =
    let open Typ in
    match typ with
    | Some {Typ.desc= Tptr ({desc= Tstruct (CppClass (name, _))}, _)}
      when QualifiedCppName.Match.match_qualifiers matcher name -> (
        L.d_printfln_escaped "Val.on_demand for %a (%a)" LocWithIdx.pp loc QualifiedCppName.pp name ;
        match LocWithIdx.to_loc loc |> Loc.get_path with
        | None ->
            L.d_printfln_escaped "Path none" ;
            bottom
        | Some p ->
            L.d_printfln_escaped "Path %a" Symb.SymbolPath.pp_partial p ;
            Allocsite.make_symbol p |> Loc.of_allocsite |> LocWithIdx.of_loc
            |> PowLocWithIdx.singleton |> of_pow_loc )
    | _ ->
        L.d_printfln_escaped "Val.on_demand for %a (Others)" LocWithIdx.pp loc ;
        bottom


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

  let find_on_demand ?typ k m = try find k m with _ -> Val.on_demand ?typ k

  let find k m = try find k m with _ -> Val.bottom

  let find_set ks m = PowLocWithIdx.fold (fun k v -> find k m |> Val.join v) ks Val.bottom
end

module Cond = struct
  type t = {absloc: LocWithIdx.t; init: Init.t; loc: Location.t} [@@deriving compare]

  let make absloc init loc = {absloc; init; loc}

  let is_symbolic cond = LocWithIdx.is_symbolic cond.absloc

  let is_init cond = Init.equal Init.Init cond.init

  let subst eval_sym mem cond =
    match cond.absloc with
    | Loc l ->
        let evals = eval_sym l in
        if AbsLoc.PowLoc.is_bot evals then [cond]
        else
          AbsLoc.PowLoc.fold
            (fun l lst ->
              let absloc = LocWithIdx.of_loc l in
              let init = Mem.find absloc mem |> Val.get_init in
              {cond with absloc; init} :: lst )
            evals []
    | Idx (l, i) ->
        let evals = eval_sym l in
        if AbsLoc.PowLoc.is_bot evals then [cond]
        else
          AbsLoc.PowLoc.fold
            (fun l lst ->
              let absloc = LocWithIdx.of_idx l i in
              let init = Mem.find absloc mem |> Val.get_init in
              {cond with absloc; init} :: lst )
            evals []


  let pp fmt cond =
    F.fprintf fmt "{absloc: %a, init: %a, loc: %a}" LocWithIdx.pp cond.absloc Init.pp cond.init
      Location.pp cond.loc
end

module CondSet = struct
  include AbstractDomain.FiniteSet (Cond)

  let subst eval_sym mem condset =
    fold (fun cond condset -> Cond.subst eval_sym mem cond |> of_list |> join condset) condset empty
end

module Summary = struct
  type t = {mem: Mem.t; condset: CondSet.t}

  let initial = {mem= Mem.initial; condset= CondSet.empty}

  let make mem condset = {mem; condset}

  let leq ~lhs ~rhs =
    Mem.leq ~lhs:lhs.mem ~rhs:rhs.mem && CondSet.leq ~lhs:lhs.condset ~rhs:rhs.condset


  let join s1 s2 = {mem= Mem.join s1.mem s2.mem; condset= CondSet.join s1.condset s2.condset}

  let widen ~prev:_ ~next ~num_iters:_ = next

  let add_mem k v s = {s with mem= Mem.add k v s.mem}

  let pp fmt summary =
    F.fprintf fmt "{mem: %a, condset: %a}" Mem.pp summary.mem CondSet.pp summary.condset
end
