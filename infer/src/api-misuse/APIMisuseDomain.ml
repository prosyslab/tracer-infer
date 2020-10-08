module F = Format
module L = Logging
open AbsLoc
module CFG = ProcCfg.NormalOneInstrPerNode

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

  let of_pow_loc ploc = PowLoc.fold (fun l s -> add (LocWithIdx.of_loc l) s) ploc bottom
end

module IntOverflow = struct
  type t = Bot | Top | Symbol of Symb.SymbolPath.partial [@@deriving compare, equal]

  let to_string = function
    | Bot ->
        "No Overflow"
    | Top ->
        "May Overflow"
    | Symbol s ->
        F.asprintf "%a" Symb.SymbolPath.pp_partial s


  let bottom = Bot

  let top = Top

  let leq ~lhs ~rhs =
    match (lhs, rhs) with
    | Bot, _ ->
        true
    | Top, Bot ->
        false
    | Top, Top ->
        true
    | Symbol _, Symbol _ ->
        equal lhs rhs
    | _, _ ->
        true


  let join x y =
    match (x, y) with
    | Bot, _ ->
        y
    | _, Bot ->
        x
    | Top, _ | _, Top ->
        Top
    | Symbol _, Symbol _ ->
        if equal x y then x else Top


  let meet x y = match (x, y) with Bot, _ -> Bot | _, Bot -> Bot | _ -> Top

  let is_bot x = equal x Bot

  let is_top x = equal x Top

  let widen ~prev ~next ~num_iters:_ = join prev next

  let narrow = meet

  let make_symbol p = Symbol p

  let pp fmt x = F.fprintf fmt "%s" (to_string x)
end

module UserInput = struct
  module Source = struct
    type t = CFG.Node.t * Location.t

    let compare x y = CFG.Node.compare_id (fst x |> CFG.Node.id) (fst y |> CFG.Node.id)

    let pp fmt (n, l) = F.fprintf fmt "%a @ %a" CFG.Node.pp_id (CFG.Node.id n) Location.pp l
  end

  module Set = PrettyPrintable.MakePPSet (Source)

  type t = Top | Set of Set.t | Symbol of Symb.SymbolPath.partial [@@deriving compare, equal]

  let bottom = Set Set.empty

  let is_bot = function Set s -> Set.is_empty s | _ -> false

  let is_symbol = function Symbol _ -> true | _ -> false

  let join x y =
    match (x, y) with
    | _, _ when is_bot x ->
        y
    | _, _ when is_bot y ->
        x
    | Set s1, Set s2 ->
        Set (Set.union s1 s2)
    | Symbol _, Symbol _ ->
        if equal x y then x else Top
    | _, _ ->
        Top


  let widen ~prev ~next ~num_iters:_ = join prev next

  let leq ~lhs ~rhs =
    match (lhs, rhs) with
    | Set s1, Set s2 ->
        Set.subset s1 s2
    | Set _, Symbol _ ->
        false
    | Symbol _, Set _ ->
        false
    | Symbol _, Symbol _ ->
        equal lhs rhs
    | _, Top ->
        true
    | _, _ ->
        false


  let make node loc = Set (Set.singleton (node, loc))

  let is_taint = function | Top -> true | Set x -> not (Set.is_empty x) | Symbol _ -> false

  let make_symbol p = Symbol p

  let pp fmt = function Top -> F.fprintf fmt "%s" "Top" | Set s -> Set.pp fmt s | Symbol s -> Symb.SymbolPath.pp_partial fmt s
end

module Subst = struct
  type subst =
    { subst_powloc: Loc.t -> PowLoc.t
    ; subst_int_overflow: IntOverflow.t -> IntOverflow.t
    ; subst_user_input: UserInput.t -> UserInput.t }

  let empty =
    { subst_powloc= (fun _ -> AbsLoc.PowLoc.bot)
    ; subst_int_overflow= Fun.id
    ; subst_user_input= Fun.id }
end

module Val = struct
  type t =
    {powloc: PowLocWithIdx.t; init: Init.t; int_overflow: IntOverflow.t; user_input: UserInput.t}
  [@@deriving compare]

  let bottom =
    { powloc= PowLocWithIdx.bottom
    ; init= Init.bottom
    ; int_overflow= IntOverflow.bottom
    ; user_input= UserInput.bottom }


  let of_pow_loc powloc = {bottom with powloc}

  let of_init init = {bottom with init}

  let of_int_overflow int_overflow = {bottom with int_overflow}

  let of_user_input user_input = {bottom with user_input}

  let matcher = QualifiedCppName.Match.of_fuzzy_qual_names ["std::map"]

  let on_demand ?typ loc =
    let open Typ in
    match LocWithIdx.to_loc loc |> Loc.get_path with
    | Some p -> (
      match typ with
      | Some {Typ.desc= Tptr ({desc= Tstruct (CppClass (name, _))}, _)}
        when QualifiedCppName.Match.match_qualifiers matcher name ->
          L.d_printfln_escaped "Val.on_demand for %a (%a)" LocWithIdx.pp loc QualifiedCppName.pp
            name ;
          L.d_printfln_escaped "Path %a" Symb.SymbolPath.pp_partial p ;
          let powloc =
            Allocsite.make_symbol p |> Loc.of_allocsite |> LocWithIdx.of_loc
            |> PowLocWithIdx.singleton
          in
          let int_overflow = IntOverflow.make_symbol p in
          let user_input = UserInput.make_symbol p in
          {bottom with powloc; int_overflow; user_input}
      | _ ->
          L.d_printfln_escaped "Val.on_demand for %a (Others)" LocWithIdx.pp loc ;
          let int_overflow = IntOverflow.make_symbol p in
          let user_input = UserInput.make_symbol p in
          {bottom with int_overflow; user_input} )
    | None ->
        L.d_printfln_escaped "Path none" ;
        bottom


  let get_powloc v = v.powloc

  let get_init v = v.init

  let get_int_overflow v = v.int_overflow

  let get_user_input v = v.user_input

  let join lhs rhs =
    { powloc= PowLocWithIdx.join lhs.powloc rhs.powloc
    ; init= Init.join lhs.init rhs.init
    ; int_overflow= IntOverflow.join lhs.int_overflow rhs.int_overflow
    ; user_input= UserInput.join lhs.user_input rhs.user_input }


  let widen ~prev ~next ~num_iters =
    { powloc= PowLocWithIdx.widen ~prev:prev.powloc ~next:next.powloc ~num_iters
    ; init= Init.widen ~prev:prev.init ~next:next.init ~num_iters
    ; int_overflow= IntOverflow.widen ~prev:prev.int_overflow ~next:next.int_overflow ~num_iters
    ; user_input= UserInput.widen ~prev:prev.user_input ~next:next.user_input ~num_iters }


  let leq ~lhs ~rhs =
    PowLocWithIdx.leq ~lhs:lhs.powloc ~rhs:rhs.powloc
    && Init.leq ~lhs:lhs.init ~rhs:rhs.init
    && IntOverflow.leq ~lhs:lhs.int_overflow ~rhs:rhs.int_overflow
    && UserInput.leq ~lhs:lhs.user_input ~rhs:rhs.user_input


  let subst {Subst.subst_int_overflow; subst_user_input} v =
    { v with
      int_overflow= subst_int_overflow v.int_overflow
    ; user_input= subst_user_input v.user_input }


  let pp fmt v =
    F.fprintf fmt "{powloc: %a, init: %a, int_overflow: %a, user_input: %a}" PowLocWithIdx.pp
      v.powloc Init.pp v.init IntOverflow.pp v.int_overflow UserInput.pp v.user_input
end

module Mem = struct
  include AbstractDomain.Map (LocWithIdx) (Val)

  let initial = empty

  let find_on_demand ?typ k m = try find k m with _ -> Val.on_demand ?typ k

  let find k m = try find k m with _ -> Val.bottom

  let find_set ks m = PowLocWithIdx.fold (fun k v -> find k m |> Val.join v) ks Val.bottom
end

module Cond = struct
  type t =
    | UnInit of {absloc: LocWithIdx.t; init: Init.t; loc: Location.t; reported: bool}
    | Overflow of {size: IntOverflow.t; user_input: UserInput.t; loc: Location.t; reported: bool}
  [@@deriving compare]

  let make_uninit absloc init loc = UnInit {absloc; init; loc; reported= false}

  let make_overflow {Val.int_overflow; user_input} loc =
    Overflow {size= int_overflow; user_input; loc; reported= false}


  let reported = function
    | UnInit cond ->
        UnInit {cond with reported= true}
    | Overflow cond ->
        Overflow {cond with reported= true}


  let is_symbolic = function
    | UnInit cond ->
        LocWithIdx.is_symbolic cond.absloc
    | Overflow _ ->
        (* TODO *)
        false


  let get_location = function UnInit cond -> cond.loc | Overflow cond -> cond.loc

  let is_reported = function UnInit cond -> cond.reported | Overflow cond -> cond.reported

  let is_init = function UnInit cond -> Init.equal Init.Init cond.init | _ -> false

  let may_overflow = function
    | Overflow cond ->
        IntOverflow.is_top cond.size && UserInput.is_taint cond.user_input
    | _ ->
        false


  let subst {Subst.subst_powloc; subst_int_overflow; subst_user_input} mem = function
    | UnInit cond -> (
      match cond.absloc with
      | Loc l ->
          let evals = subst_powloc l in
          if AbsLoc.PowLoc.is_bot evals then [UnInit cond]
          else
            AbsLoc.PowLoc.fold
              (fun l lst ->
                let absloc = LocWithIdx.of_loc l in
                let init = Mem.find absloc mem |> Val.get_init in
                UnInit {cond with absloc; init} :: lst )
              evals []
      | Idx (l, i) ->
          let evals = subst_powloc l in
          if AbsLoc.PowLoc.is_bot evals then [UnInit cond]
          else
            AbsLoc.PowLoc.fold
              (fun l lst ->
                let absloc = LocWithIdx.of_idx l i in
                let init = Mem.find absloc mem |> Val.get_init in
                UnInit {cond with absloc; init} :: lst )
              evals [] )
    | Overflow cond ->
        [ Overflow
            { cond with
              size= subst_int_overflow cond.size
            ; user_input= subst_user_input cond.user_input } ]


  let pp fmt = function
    | UnInit cond ->
        F.fprintf fmt "{absloc: %a, init: %a, loc: %a}" LocWithIdx.pp cond.absloc Init.pp cond.init
          Location.pp cond.loc
    | Overflow cond ->
        F.fprintf fmt "{loc: %a}" Location.pp cond.loc
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
