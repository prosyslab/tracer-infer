module F = Format
module L = Logging
open AbsLoc
module CFG = ProcCfg.NormalOneInstrPerNode
module Trace = APIMisuseTrace
module TraceSet = APIMisuseTrace.Set
module SPath = Symb.SymbolPath
module BoField = BufferOverrunField

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

module Str = struct
  type t = Bot | Top | V of string [@@deriving compare]

  let bottom = Bot

  let is_bottom = function Bot -> true | _ -> false

  let make s = V s

  let leq ~lhs ~rhs =
    match (lhs, rhs) with
    | Bot, _ | _, Top ->
        true
    | V s1, V s2 ->
        String.equal s1 s2
    | _, _ ->
        false


  let join x y =
    match (x, y) with
    | Bot, _ ->
        y
    | _, Bot ->
        x
    | Top, _ | _, Top ->
        Top
    | V s1, V s2 ->
        if String.equal s1 s2 then x else Top


  let widen ~prev ~next ~num_iters:_ = join prev next

  let pp fmt = function
    | Bot ->
        F.fprintf fmt "Bot"
    | V s ->
        F.fprintf fmt "\"%s\"" s
    | Top ->
        F.fprintf fmt "Top"
end

module Idx = struct
  type t = Bot | Itv of Itv.t | Str of Str.t | Top [@@deriving compare]

  let of_itv i = Itv i

  let of_str s = Str s

  let join x y =
    match (x, y) with
    | Bot, _ ->
        y
    | _, Bot ->
        x
    | Top, _ | _, Top ->
        Top
    | Itv i1, Itv i2 ->
        Itv (Itv.join i1 i2)
    | Str s1, Str s2 ->
        Str (Str.join s1 s2)
    | Itv i, Str s | Str s, Itv i ->
        if Str.is_bottom s then Itv i else Str s


  let pp fmt = function
    | Bot ->
        F.fprintf fmt "Bot"
    | Top ->
        F.fprintf fmt "Top"
    | Itv i ->
        Itv.pp fmt i
    | Str s ->
        Str.pp fmt s
end

module LocWithIdx = struct
  module Loc = AbsLoc.Loc

  type t = Loc of Loc.t | Idx of Loc.t * Idx.t [@@deriving compare]

  let of_loc l = Loc l

  let of_idx l i = Idx (l, i)

  let to_loc = function Loc l | Idx (l, _) -> l

  let is_symbolic = function Loc l | Idx (l, _) -> Loc.is_symbol l

  (* check if field = loc.f *)
  let field_of field loc =
    match (field, loc) with
    | Loc f, Loc l -> (
      match f with BoField.Field {prefix} -> Loc.equal prefix l | _ -> false )
    | _, _ ->
        false


  let replace_prefix k loc =
    match (k, loc) with
    | Loc k', Loc loc -> (
      match k' with BoField.Field f -> Loc (BoField.Field {f with prefix= loc}) | _ -> k )
    | _, _ ->
        k


  let append_idx l i =
    match l with
    | Loc l ->
        Idx (l, i)
    | _ ->
        prerr_endline "append_idx" ;
        assert false


  let append_field ?typ fn l = match l with Loc l -> Loc (Loc.append_field ?typ l fn) | _ -> l

  let of_symbol p = Allocsite.make_symbol p |> Loc.of_allocsite |> of_loc

  let pp fmt = function
    | Loc l ->
        AbsLoc.Loc.pp fmt l
    | Idx (l, i) ->
        F.fprintf fmt "%a[%a]" Loc.pp l Idx.pp i


  let loc_deref loc =
    match loc with
    | Loc l -> (
      match Loc.get_path l with
      | Some sym ->
          sym
          |> SPath.deref ~deref_kind:SPath.Deref_CPointer
          |> Allocsite.make_symbol |> Loc.of_allocsite |> of_loc
      | _ ->
          loc )
    | _ ->
        loc
end

module PowLocWithIdx = struct
  include PrettyPrintable.MakePPSet (LocWithIdx)

  let bottom = empty

  let join x y = if cardinal x + cardinal y > Config.api_misuse_max_powloc then x else union x y

  let add elt t = if cardinal t < Config.api_misuse_max_powloc then add elt t else t

  let widen ~prev ~next ~num_iters:_ = join prev next

  let leq ~lhs ~rhs = subset lhs rhs

  let of_pow_loc ploc = PowLoc.fold (fun l s -> add (LocWithIdx.of_loc l) s) ploc bottom

  let to_pow_loc plocwithind =
    fold (fun l s -> PowLoc.add (LocWithIdx.to_loc l) s) plocwithind PowLoc.bot


  let append_field ?typ fn set = map (LocWithIdx.append_field ?typ fn) set
end

module BTS = struct
  type t = Bot | Top | Symbol of Symb.SymbolPath.partial [@@deriving compare, equal]

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
end

module IntOverflow = struct
  include BTS

  let to_string = function
    | Bot ->
        "No IntOverflow"
    | Top ->
        "May IntOverflow"
    | Symbol s ->
        F.asprintf "%a" Symb.SymbolPath.pp_partial s


  let pp fmt x = F.fprintf fmt "%s" (to_string x)
end

module IntUnderflow = struct
  include BTS

  let to_string = function
    | Bot ->
        "No IntUnderflow"
    | Top ->
        "May IntUnderflow"
    | Symbol s ->
        F.asprintf "%a" Symb.SymbolPath.pp_partial s


  let pp fmt x = F.fprintf fmt "%s" (to_string x)
end

module Allocated = struct
  type t = Bot | Top | Alloc | Free | Symbol of Symb.SymbolPath.partial | MaybeFree
  [@@deriving compare, equal]

  let bottom = Bot

  let top = Top

  let alloc = Alloc

  let free = Free

  let is_bottom t = match t with Bot -> true | _ -> false

  let may_freed t = match t with Free | MaybeFree | Top -> true | _ -> false

  let make_symbol p = Symbol p

  let join x y =
    match (x, y) with
    | Bot, Bot ->
        Bot
    | Alloc, Alloc ->
        Alloc
    | Free, Free ->
        Free
    | Symbol _, Symbol _ ->
        if equal x y then x else Top
    | _, Bot ->
        x
    | Bot, _ ->
        y
    | Alloc, Symbol _
    | Symbol _, Alloc
    | Free, Symbol _
    | Symbol _, Free
    | MaybeFree, Symbol _
    | Symbol _, MaybeFree ->
        Top
    | Alloc, Free
    | Free, Alloc
    | MaybeFree, Alloc
    | Alloc, MaybeFree
    | MaybeFree, Free
    | Free, MaybeFree
    | MaybeFree, MaybeFree ->
        MaybeFree
    | Top, _ | _, Top ->
        Top


  let widen ~prev ~next ~num_iters:_ = join prev next

  let to_string t =
    match t with
    | Bot ->
        "Bot"
    | Top ->
        "Top"
    | Alloc ->
        "Alloc"
    | Free ->
        "Free"
    | Symbol s ->
        F.asprintf "%a" Symb.SymbolPath.pp_partial s
    | MaybeFree ->
        "MaybeFree"


  let pp fmt t = F.fprintf fmt "%s" (to_string t)
end

module UserInput = struct
  module Source = struct
    type t = CFG.Node.t * Location.t

    let compare x y =
      let compare_node = CFG.Node.compare_id (fst x |> CFG.Node.id) (fst y |> CFG.Node.id) in
      if equal_int compare_node 0 then Location.compare (snd x) (snd y) else compare_node


    let equal (_, x) (_, y) = Location.equal x y

    let pp fmt (n, l) = F.fprintf fmt "%a @ %a" CFG.Node.pp_id (CFG.Node.id n) Location.pp l
  end

  module PrettyPrintableSymbol = struct
    type t = Symb.SymbolPath.partial [@@deriving compare, equal]

    let pp fmt s = F.fprintf fmt "%a" Symb.SymbolPath.pp_partial s
  end

  module Elem = struct
    type t = Source of Source.t | Symbol of PrettyPrintableSymbol.t [@@deriving compare, equal]

    let pp fmt e =
      match e with
      | Source src ->
          Source.pp fmt src
      | Symbol sym ->
          PrettyPrintableSymbol.pp fmt sym


    let is_source elem = match elem with Source _ -> true | _ -> false

    let is_symbol elem = match elem with Symbol _ -> true | _ -> false
  end

  module Set = PrettyPrintable.MakePPSet (Elem)

  type t = Set.t [@@deriving compare, equal]

  let bottom = Set.empty

  let is_bot = Set.is_empty

  let is_symbol = Set.exists (fun e -> Elem.is_symbol e)

  let cardinal = Set.cardinal

  let join x y =
    if Config.api_misuse_max_set >= 0 then
      if cardinal x > Config.api_misuse_max_set then x
      else if cardinal y > Config.api_misuse_max_set then y
      else Set.union x y
    else Set.union x y


  let widen ~prev ~next ~num_iters:_ = join prev next

  let leq ~lhs ~rhs =
    if Config.api_misuse_max_set >= 0 then
      if cardinal rhs > Config.api_misuse_max_set then true else Set.subset lhs rhs
    else Set.subset lhs rhs


  let make node loc = Set.singleton (Source (node, loc))

  let is_taint = Set.exists Elem.is_source

  let make_symbol p = Set.singleton (Symbol p)

  let pp = Set.pp

  let make_elem e = Set.singleton e

  let to_list s = Set.fold (fun elem l -> elem :: l) s []
end

module Subst = struct
  type subst =
    { subst_powloc: Loc.t -> PowLoc.t
    ; subst_int_overflow: IntOverflow.t -> IntOverflow.t
    ; subst_int_underflow: IntUnderflow.t -> IntUnderflow.t
    ; subst_allocated: Allocated.t -> Allocated.t
    ; subst_user_input: UserInput.t -> UserInput.t
    ; subst_traces: TraceSet.t -> TraceSet.t }

  let empty =
    { subst_powloc= (fun loc -> AbsLoc.PowLoc.singleton loc)
    ; subst_int_overflow= Fun.id
    ; subst_int_underflow= Fun.id
    ; subst_allocated= Fun.id
    ; subst_user_input= Fun.id
    ; subst_traces= Fun.id }


  let apply_subst_powloc subst_powloc powloc =
    PowLoc.fold (fun loc result -> PowLoc.join (subst_powloc loc) result) powloc PowLoc.bot
end

module Val = struct
  type t =
    { powloc: PowLocWithIdx.t
    ; init: Init.t
    ; int_overflow: IntOverflow.t
    ; int_underflow: IntUnderflow.t
    ; allocated: Allocated.t
    ; user_input: UserInput.t
    ; str: Str.t
    ; traces: (TraceSet.t[@compare.ignore]) }
  [@@deriving compare]

  let bottom =
    { powloc= PowLocWithIdx.bottom
    ; init= Init.bottom
    ; int_overflow= IntOverflow.bottom
    ; int_underflow= IntUnderflow.bottom
    ; allocated= Allocated.bottom
    ; user_input= UserInput.bottom
    ; str= Str.bottom
    ; traces= TraceSet.bottom }


  let of_pow_loc powloc = {bottom with powloc}

  let of_init init = {bottom with init}

  let of_int_overflow int_overflow = {bottom with int_overflow}

  let of_user_input ?(traces = TraceSet.bottom) user_input = {bottom with user_input; traces}

  let of_str str = {bottom with str}

  let matcher = QualifiedCppName.Match.of_fuzzy_qual_names ["std::map"]

  let get_powloc v = v.powloc

  let get_init v = v.init

  let get_int_overflow v = v.int_overflow

  let get_int_underflow v = v.int_underflow

  let get_allocated v = v.allocated

  let get_user_input v = v.user_input

  let get_traces v = v.traces

  let get_str v = v.str

  let append_trace_elem elem v =
    let new_traces = TraceSet.append elem v.traces in
    {v with traces= new_traces}


  let append_libcall v f_name args location =
    let user_input = get_user_input v in
    if UserInput.is_symbol user_input || UserInput.is_taint user_input then
      append_trace_elem (Trace.make_libcall f_name args location) v
    else v


  let join lhs rhs =
    { powloc= PowLocWithIdx.join lhs.powloc rhs.powloc
    ; init= Init.join lhs.init rhs.init
    ; int_overflow= IntOverflow.join lhs.int_overflow rhs.int_overflow
    ; int_underflow= IntUnderflow.join lhs.int_underflow rhs.int_underflow
    ; allocated= Allocated.join lhs.allocated rhs.allocated
    ; user_input= UserInput.join lhs.user_input rhs.user_input
    ; str= Str.join lhs.str rhs.str
    ; traces= TraceSet.join lhs.traces rhs.traces }


  let widen ~prev ~next ~num_iters =
    { powloc= PowLocWithIdx.widen ~prev:prev.powloc ~next:next.powloc ~num_iters
    ; init= Init.widen ~prev:prev.init ~next:next.init ~num_iters
    ; int_overflow= IntOverflow.widen ~prev:prev.int_overflow ~next:next.int_overflow ~num_iters
    ; int_underflow= IntUnderflow.widen ~prev:prev.int_underflow ~next:next.int_underflow ~num_iters
    ; allocated= Allocated.widen ~prev:prev.allocated ~next:next.allocated ~num_iters
    ; user_input= UserInput.widen ~prev:prev.user_input ~next:next.user_input ~num_iters
    ; str= Str.widen ~prev:prev.str ~next:next.str ~num_iters
    ; traces= TraceSet.widen ~prev:prev.traces ~next:next.traces ~num_iters }


  let leq ~lhs ~rhs =
    PowLocWithIdx.leq ~lhs:lhs.powloc ~rhs:rhs.powloc
    && Init.leq ~lhs:lhs.init ~rhs:rhs.init
    && IntOverflow.leq ~lhs:lhs.int_overflow ~rhs:rhs.int_overflow
    && IntUnderflow.leq ~lhs:lhs.int_underflow ~rhs:rhs.int_underflow
    && UserInput.leq ~lhs:lhs.user_input ~rhs:rhs.user_input
    && Str.leq ~lhs:lhs.str ~rhs:rhs.str


  let subst
      { Subst.subst_int_overflow
      ; subst_int_underflow
      ; subst_allocated
      ; subst_user_input
      ; subst_traces } v =
    { v with
      int_overflow= subst_int_overflow v.int_overflow
    ; int_underflow= subst_int_underflow v.int_underflow
    ; allocated= subst_allocated v.allocated
    ; user_input= subst_user_input v.user_input
    ; traces= subst_traces v.traces }


  let symbol p =
    let loc = p |> Allocsite.make_symbol |> Loc.of_allocsite in
    let powloc = loc |> LocWithIdx.of_loc |> PowLocWithIdx.singleton in
    let traces = Trace.make_symbol_decl loc |> Trace.make_singleton |> TraceSet.singleton in
    let user_input = UserInput.make_symbol p in
    let int_overflow = IntOverflow.make_symbol p in
    let int_underflow = IntUnderflow.make_symbol p in
    let allocated = Allocated.make_symbol p in
    {bottom with powloc; int_overflow; int_underflow; allocated; user_input; traces}


  let pp fmt v =
    F.fprintf fmt
      "{powloc: %a, init: %a, int_overflow: %a, int_underflow: %a, user_input: %a, allocated: %a, \
       str: %a, traces: %a}"
      PowLocWithIdx.pp v.powloc Init.pp v.init IntOverflow.pp v.int_overflow IntUnderflow.pp
      v.int_underflow UserInput.pp v.user_input Allocated.pp v.allocated Str.pp v.str TraceSet.pp
      v.traces
end

module Mem = struct
  include AbstractDomain.Map (LocWithIdx) (Val)

  let initial = empty

  let on_demand ?typ loc mem =
    let open Typ in
    let open Val in
    match LocWithIdx.to_loc loc |> Loc.get_path with
    | Some (BufferOverrunField.Prim (SPath.Deref (_, Prim (Deref (_, Prim (Deref (_, _))))))) | None
      ->
        L.d_printfln_escaped "Path none" ;
        (bottom, mem)
    | Some p -> (
      match typ with
      | Some {Typ.desc= Tptr ({desc= Tstruct (CppClass (name, _))}, _)}
        when QualifiedCppName.Match.match_qualifiers matcher name ->
          L.d_printfln_escaped "Val.on_demand for %a (%a)" LocWithIdx.pp loc QualifiedCppName.pp
            name ;
          L.d_printfln_escaped "Path %a" Symb.SymbolPath.pp_partial p ;
          let loc = p |> Allocsite.make_symbol |> Loc.of_allocsite in
          let powloc = loc |> LocWithIdx.of_loc |> PowLocWithIdx.singleton in
          let int_overflow = IntOverflow.make_symbol p in
          let int_underflow = IntUnderflow.make_symbol p in
          let user_input = UserInput.make_symbol p in
          let traces = [Trace.make_symbol_decl loc] |> TraceSet.singleton in
          ({bottom with powloc; int_overflow; int_underflow; user_input; traces}, mem)
      | Some ({Typ.desc= Tptr _} as typ) ->
          L.d_printfln_escaped "Val.on_demand for %a (%s)" LocWithIdx.pp loc (Typ.to_string typ) ;
          L.d_printfln_escaped "Path %a" Symb.SymbolPath.pp_partial p ;
          let loc = p |> Allocsite.make_symbol |> Loc.of_allocsite in
          let deref_sym = p |> SPath.deref ~deref_kind:SPath.Deref_CPointer in
          let powloc = LocWithIdx.of_symbol deref_sym |> PowLocWithIdx.singleton in
          L.d_printfln_escaped "Powloc: %a" PowLocWithIdx.pp powloc ;
          let deref2_sym = deref_sym |> SPath.deref ~deref_kind:SPath.Deref_CPointer in
          let deref3_sym = deref2_sym |> SPath.deref ~deref_kind:SPath.Deref_CPointer in
          let mem =
            add (LocWithIdx.of_loc loc) (Val.symbol deref_sym) mem
            |> add (LocWithIdx.of_symbol deref_sym) (Val.symbol deref2_sym)
            |> add (LocWithIdx.of_symbol deref2_sym) (Val.symbol deref3_sym)
          in
          (Val.symbol deref_sym, mem)
      | Some typ ->
          L.d_printfln_escaped "Val.on_demand for %a (%a)" LocWithIdx.pp loc (Typ.pp Pp.text) typ ;
          (Val.symbol p, mem)
      | None ->
          L.(debug Analysis Verbose) "Unknown: %a\n" SPath.pp_partial p ;
          L.d_printfln_escaped "Path %a" Symb.SymbolPath.pp_partial p ;
          let loc = p |> Allocsite.make_symbol |> Loc.of_allocsite in
          let deref_sym = p |> SPath.deref ~deref_kind:SPath.Deref_CPointer in
          let powloc = LocWithIdx.of_symbol deref_sym |> PowLocWithIdx.singleton in
          L.d_printfln_escaped "Powloc: %a" PowLocWithIdx.pp powloc ;
          let deref2_sym = deref_sym |> SPath.deref ~deref_kind:SPath.Deref_CPointer in
          let mem =
            add (LocWithIdx.of_loc loc) (Val.symbol deref_sym) mem
            |> add (LocWithIdx.of_symbol deref_sym) (Val.symbol deref2_sym)
          in
          (Val.symbol deref_sym, mem) )


  let find_var_or_symbol k m =
    try Some (find k m)
    with _ -> (
      match LocWithIdx.to_loc k |> Loc.get_path with
      | Some p -> (
        try Some (find (LocWithIdx.of_symbol p) m) with _ -> None )
      | None ->
          None )


  let find_init_on_demand ?typ k m =
    match find_var_or_symbol k m with Some v -> (v, m) | None -> on_demand ?typ k m


  let find_on_demand ?typ k m = find_init_on_demand ?typ k m |> fst

  let find k m = try find k m with _ -> Val.bottom

  let find_set ks m = PowLocWithIdx.fold (fun k v -> find k m |> Val.join v) ks Val.bottom

  let weak_update k v m =
    let joined_v = find k m |> Val.join v in
    add k joined_v m


  let can_strong_update l = match l with LocWithIdx.Loc l -> Loc.is_var l | _ -> false

  let update k v m = if can_strong_update k then add k v m else weak_update k v m

  let remove_temps vars m =
    List.fold_left vars ~init:m ~f:(fun m var ->
        let k = Loc.of_id var |> LocWithIdx.of_loc in
        remove k m)
end

module Cond = struct
  type t =
    | UnInit of
        { absloc: LocWithIdx.t
        ; init: Init.t
        ; loc: Location.t
        ; traces: (TraceSet.t[@compare.ignore])
        ; reported: bool }
    | IntOverflow of
        { size: IntOverflow.t
        ; user_input_elem: UserInput.Elem.t
        ; loc: Location.t
        ; traces: (TraceSet.t[@compare.ignore])
        ; reported: bool }
    | IntUnderflow of
        { size: IntUnderflow.t
        ; user_input_elem: UserInput.Elem.t
        ; loc: Location.t
        ; traces: (TraceSet.t[@compare.ignore])
        ; reported: bool }
    | FormatString of
        { user_input_elem: UserInput.Elem.t
        ; loc: Location.t
        ; traces: (TraceSet.t[@compare.ignore])
        ; reported: bool }
    | BufferOverflow of
        { user_input_elem: UserInput.Elem.t
        ; loc: Location.t
        ; traces: (TraceSet.t[@compare.ignore])
        ; reported: bool }
    | CmdInjection of
        { user_input_elem: UserInput.Elem.t
        ; loc: Location.t
        ; traces: (TraceSet.t[@compare.ignore])
        ; reported: bool }
    | DoubleFree of
        { allocated: Allocated.t
        ; loc: Location.t
        ; traces: (TraceSet.t[@compare.ignore])
        ; reported: bool }
    | UseAfterFree of
        { allocated: Allocated.t
        ; loc: Location.t
        ; traces: (TraceSet.t[@compare.ignore])
        ; reported: bool }
  [@@deriving compare]

  let make_uninit absloc init loc =
    UnInit {absloc; init; loc; traces= TraceSet.empty; reported= false}


  let make_overflow {Val.int_overflow; traces} user_input_elem loc =
    IntOverflow {size= int_overflow; user_input_elem; loc; traces; reported= false}


  let make_underflow {Val.int_underflow; traces} user_input_elem loc =
    IntUnderflow {size= int_underflow; user_input_elem; loc; traces; reported= false}


  let make_format {Val.traces} user_input_elem loc =
    FormatString {user_input_elem; loc; traces; reported= false}


  let make_buffer_overflow {Val.traces} user_input_elem loc =
    BufferOverflow {user_input_elem; loc; traces; reported= false}


  let make_exec {Val.traces} user_input_elem loc =
    CmdInjection {user_input_elem; loc; traces; reported= false}


  let make_double_free {Val.allocated; traces} loc =
    DoubleFree {allocated; loc; traces; reported= false}


  let make_use_after_free {Val.allocated; traces} loc =
    UseAfterFree {allocated; loc; traces; reported= false}


  let reported = function
    | UnInit cond ->
        UnInit {cond with reported= true}
    | IntOverflow cond ->
        IntOverflow {cond with reported= true}
    | IntUnderflow cond ->
        IntUnderflow {cond with reported= true}
    | FormatString cond ->
        FormatString {cond with reported= true}
    | BufferOverflow cond ->
        BufferOverflow {cond with reported= true}
    | CmdInjection cond ->
        CmdInjection {cond with reported= true}
    | DoubleFree cond ->
        DoubleFree {cond with reported= true}
    | UseAfterFree cond ->
        UseAfterFree {cond with reported= true}


  let is_symbolic = function
    | UnInit cond ->
        LocWithIdx.is_symbolic cond.absloc
    | IntOverflow _
    | IntUnderflow _
    | FormatString _
    | BufferOverflow _
    | CmdInjection _
    | DoubleFree _
    | UseAfterFree _ ->
        (* TODO *)
        false


  let get_location = function
    | UnInit cond ->
        cond.loc
    | IntOverflow cond ->
        cond.loc
    | IntUnderflow cond ->
        cond.loc
    | FormatString cond ->
        cond.loc
    | BufferOverflow cond ->
        cond.loc
    | CmdInjection cond ->
        cond.loc
    | DoubleFree cond ->
        cond.loc
    | UseAfterFree cond ->
        cond.loc


  let is_reported = function
    | UnInit cond ->
        cond.reported
    | IntOverflow cond ->
        cond.reported
    | IntUnderflow cond ->
        cond.reported
    | FormatString cond ->
        cond.reported
    | BufferOverflow cond ->
        cond.reported
    | CmdInjection cond ->
        cond.reported
    | DoubleFree cond ->
        cond.reported
    | UseAfterFree cond ->
        cond.reported


  let is_init = function UnInit cond -> Init.equal Init.Init cond.init | _ -> false

  let may_overflow = function
    | IntOverflow cond ->
        IntOverflow.is_top cond.size && UserInput.Elem.is_source cond.user_input_elem
    | _ ->
        false


  let may_underflow = function
    | IntUnderflow cond ->
        IntUnderflow.is_top cond.size && UserInput.Elem.is_source cond.user_input_elem
    | _ ->
        false


  let is_user_input = function
    | IntOverflow cond ->
        UserInput.Elem.is_source cond.user_input_elem
    | IntUnderflow cond ->
        UserInput.Elem.is_source cond.user_input_elem
    | FormatString cond ->
        UserInput.Elem.is_source cond.user_input_elem
    | BufferOverflow cond ->
        UserInput.Elem.is_source cond.user_input_elem
    | CmdInjection cond ->
        UserInput.Elem.is_source cond.user_input_elem
    | DoubleFree _ | UseAfterFree _ | UnInit _ ->
        false


  let extract_user_input cond =
    match cond with
    | IntOverflow cond ->
        Some cond.user_input_elem
    | IntUnderflow cond ->
        Some cond.user_input_elem
    | FormatString cond ->
        Some cond.user_input_elem
    | BufferOverflow cond ->
        Some cond.user_input_elem
    | CmdInjection cond ->
        Some cond.user_input_elem
    | DoubleFree _ | UseAfterFree _ | UnInit _ ->
        None


  let is_double_free = function DoubleFree cond -> Allocated.may_freed cond.allocated | _ -> false

  let is_use_after_free = function
    | UseAfterFree cond ->
        Allocated.may_freed cond.allocated
    | _ ->
        false


  let subst
      { Subst.subst_powloc
      ; subst_int_overflow
      ; subst_int_underflow
      ; subst_allocated
      ; subst_user_input
      ; subst_traces } mem = function
    | UnInit cond -> (
      match cond.absloc with
      | Loc l -> (
          let evals = subst_powloc l in
          if AbsLoc.PowLoc.is_bot evals then [UnInit cond]
          else
            match AbsLoc.PowLoc.min_elt_opt evals with
            | Some l ->
                let absloc = LocWithIdx.of_loc l in
                let init = Mem.find absloc mem |> Val.get_init in
                [UnInit {cond with absloc; init}]
            | None ->
                [UnInit cond] )
      | Idx (l, i) -> (
          let evals = subst_powloc l in
          if AbsLoc.PowLoc.is_bot evals then [UnInit cond]
          else
            match AbsLoc.PowLoc.min_elt_opt evals with
            | Some l ->
                let absloc = LocWithIdx.of_idx l i in
                let init = Mem.find absloc mem |> Val.get_init in
                [UnInit {cond with absloc; init}]
            | None ->
                [UnInit cond] ) )
    | IntOverflow cond ->
        let substed_user_input_list =
          UserInput.make_elem cond.user_input_elem |> subst_user_input |> UserInput.to_list
        in
        List.map substed_user_input_list ~f:(fun elem ->
            IntOverflow
              { cond with
                size= subst_int_overflow cond.size
              ; user_input_elem= elem
              ; traces= subst_traces cond.traces })
    | IntUnderflow cond ->
        let substed_user_input_list =
          UserInput.make_elem cond.user_input_elem |> subst_user_input |> UserInput.to_list
        in
        List.map substed_user_input_list ~f:(fun elem ->
            IntUnderflow
              { cond with
                size= subst_int_underflow cond.size
              ; user_input_elem= elem
              ; traces= subst_traces cond.traces })
    | FormatString cond ->
        let substed_user_input_list =
          UserInput.make_elem cond.user_input_elem |> subst_user_input |> UserInput.to_list
        in
        List.map substed_user_input_list ~f:(fun elem ->
            FormatString {cond with user_input_elem= elem; traces= subst_traces cond.traces})
    | BufferOverflow cond ->
        let substed_user_input_list =
          UserInput.make_elem cond.user_input_elem |> subst_user_input |> UserInput.to_list
        in
        List.map substed_user_input_list ~f:(fun elem ->
            BufferOverflow {cond with user_input_elem= elem; traces= subst_traces cond.traces})
    | CmdInjection cond ->
        let substed_user_input_list =
          UserInput.make_elem cond.user_input_elem |> subst_user_input |> UserInput.to_list
        in
        List.map substed_user_input_list ~f:(fun elem ->
            CmdInjection {cond with user_input_elem= elem; traces= subst_traces cond.traces})
    | DoubleFree cond ->
        [ DoubleFree
            {cond with allocated= subst_allocated cond.allocated; traces= subst_traces cond.traces}
        ]
    | UseAfterFree cond ->
        [ UseAfterFree
            {cond with allocated= subst_allocated cond.allocated; traces= subst_traces cond.traces}
        ]


  let pp fmt = function
    | UnInit cond ->
        F.fprintf fmt "{absloc: %a, init: %a, loc: %a, traces: %a}" LocWithIdx.pp cond.absloc
          Init.pp cond.init Location.pp cond.loc TraceSet.pp cond.traces
    | IntOverflow cond ->
        F.fprintf fmt "{user_input: %a, loc: %a, traces: %a}" UserInput.Elem.pp cond.user_input_elem
          Location.pp cond.loc TraceSet.pp cond.traces
    | IntUnderflow cond ->
        F.fprintf fmt "{user_input: %a, loc: %a, traces: %a}" UserInput.Elem.pp cond.user_input_elem
          Location.pp cond.loc TraceSet.pp cond.traces
    | FormatString cond ->
        F.fprintf fmt "{user_input: %a, loc: %a, traces: %a}" UserInput.Elem.pp cond.user_input_elem
          Location.pp cond.loc TraceSet.pp cond.traces
    | BufferOverflow cond ->
        F.fprintf fmt "{user_input: %a, loc: %a, traces: %a}" UserInput.Elem.pp cond.user_input_elem
          Location.pp cond.loc TraceSet.pp cond.traces
    | CmdInjection cond ->
        F.fprintf fmt "{user_input: %a, loc: %a, traces: %a}" UserInput.Elem.pp cond.user_input_elem
          Location.pp cond.loc TraceSet.pp cond.traces
    | DoubleFree cond ->
        F.fprintf fmt "{allocated: %a, loc: %a, traces: %a}" Allocated.pp cond.allocated Location.pp
          cond.loc TraceSet.pp cond.traces
    | UseAfterFree cond ->
        F.fprintf fmt "{allocated: %a, loc: %a, traces: %a}" Allocated.pp cond.allocated Location.pp
          cond.loc TraceSet.pp cond.traces
end

module CondSet = struct
  include AbstractDomain.FiniteSet (Cond)

  let subst eval_sym mem condset =
    fold
      (fun cond condset ->
        let new_condset = Cond.subst eval_sym mem cond |> of_list in
        union condset new_condset)
      condset empty


  let make_overflow (v : Val.t) loc =
    let user_input_list = UserInput.to_list v.user_input in
    List.fold user_input_list ~init:bottom ~f:(fun cs user_input_elem ->
        let traces =
          TraceSet.filter
            (fun tr ->
              match user_input_elem with
              | UserInput.Elem.Source (_, src_loc) ->
                  Trace.src_may_match src_loc tr
              | UserInput.Elem.Symbol _ ->
                  true)
            v.traces
        in
        add (Cond.make_overflow {v with traces} user_input_elem loc) cs)


  let make_underflow (v : Val.t) loc =
    let user_input_list = UserInput.to_list v.user_input in
    List.fold user_input_list ~init:bottom ~f:(fun cs user_input_elem ->
        let traces =
          TraceSet.filter
            (fun tr ->
              match user_input_elem with
              | UserInput.Elem.Source (_, src_loc) ->
                  Trace.src_may_match src_loc tr
              | UserInput.Elem.Symbol _ ->
                  true)
            v.traces
        in
        add (Cond.make_underflow {v with traces} user_input_elem loc) cs)


  let make_format (v : Val.t) loc =
    let user_input_list = UserInput.to_list v.user_input in
    List.fold user_input_list ~init:bottom ~f:(fun cs user_input_elem ->
        let traces =
          TraceSet.filter
            (fun tr ->
              match user_input_elem with
              | UserInput.Elem.Source (_, src_loc) ->
                  Trace.src_may_match src_loc tr
              | UserInput.Elem.Symbol _ ->
                  true)
            v.traces
        in
        add (Cond.make_format {v with traces} user_input_elem loc) cs)


  let make_buffer_overflow (v : Val.t) loc =
    let user_input_list = UserInput.to_list v.user_input in
    List.fold user_input_list ~init:bottom ~f:(fun cs user_input_elem ->
        let traces =
          TraceSet.filter
            (fun tr ->
              match user_input_elem with
              | UserInput.Elem.Source (_, src_loc) ->
                  Trace.src_may_match src_loc tr
              | UserInput.Elem.Symbol _ ->
                  true)
            v.traces
        in
        add (Cond.make_buffer_overflow {v with traces} user_input_elem loc) cs)


  let make_exec (v : Val.t) loc =
    let user_input_list = UserInput.to_list v.user_input in
    List.fold user_input_list ~init:bottom ~f:(fun cs user_input_elem ->
        let traces =
          TraceSet.filter
            (fun tr ->
              match user_input_elem with
              | UserInput.Elem.Source (_, src_loc) ->
                  Trace.src_may_match src_loc tr
              | UserInput.Elem.Symbol _ ->
                  true)
            v.traces
        in
        add (Cond.make_exec {v with traces} user_input_elem loc) cs)


  let make_double_free (v : Val.t) loc = add (Cond.make_double_free v loc) bottom

  let make_use_after_free (v : Val.t) loc = add (Cond.make_use_after_free v loc) bottom
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
