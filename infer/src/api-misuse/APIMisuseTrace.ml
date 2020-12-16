open! IStd
module F = Format

module Trace = struct
  type elem =
    | SymbolDecl of AbsLoc.Loc.t
    | Input of Location.t
    | BinOp of Location.t
    | Call of Location.t
    | Malloc of Location.t
    | Printf of Location.t
  [@@deriving compare]

  type t = elem list [@@deriving compare]

  let make_input loc = Input loc

  let make_binop loc = BinOp loc

  let make_call loc = Call loc

  let make_malloc loc = Malloc loc

  let make_symbol_decl l = SymbolDecl l

  let make_printf loc = Printf loc

  let append h t = h :: t

  let rec make_err_trace depth t tail =
    match t with
    | [] ->
        tail
    | Input l :: t ->
        let desc = "input" in
        Errlog.make_trace_element depth l desc [] :: tail |> make_err_trace depth t
    | BinOp l :: t ->
        let desc = "binop" in
        Errlog.make_trace_element depth l desc [] :: tail |> make_err_trace depth t
    | Call l :: t ->
        let desc = "call" in
        Errlog.make_trace_element (depth + 1) l desc [] :: tail |> make_err_trace depth t
    | Malloc l :: t ->
        let desc = "malloc" in
        Errlog.make_trace_element depth l desc [] :: tail |> make_err_trace depth t
    | Printf l :: t ->
        let desc = "printf" in
        Errlog.make_trace_element depth l desc [] :: tail |> make_err_trace depth t
    | SymbolDecl _ :: t ->
        make_err_trace depth t tail


  let concat t1 t2 = t1 @ t2

  let pp_elem fmt = function
    | Input l ->
        F.fprintf fmt "Input (%a)" Location.pp l
    | BinOp l ->
        F.fprintf fmt "BinOp (%a)" Location.pp l
    | Call l ->
        F.fprintf fmt "Call (%a)" Location.pp l
    | Malloc l ->
        F.fprintf fmt "Malloc (%a)" Location.pp l
    | Printf l ->
        F.fprintf fmt "Printf (%a)" Location.pp l
    | SymbolDecl l ->
        F.fprintf fmt "Symbol (%a)" AbsLoc.Loc.pp l


  let pp fmt trace =
    F.fprintf fmt "[" ;
    List.iter ~f:(fun e -> F.fprintf fmt "%a, " pp_elem e) trace ;
    F.fprintf fmt "]"
end

module Set = struct
  include AbstractDomain.FiniteSet (Trace)

  (* TODO: heuristic. *)
  let join x y = if cardinal x + cardinal y > 100 then x else join x y

  let append h set = map (Trace.append h) set

  let concat set1 set2 =
    if is_empty set1 then set2
    else if is_empty set2 then set1
    else fold (fun t1 set -> fold (fun t2 set -> add (Trace.concat t1 t2) set) set2 set) set1 empty


  let widen ~prev ~next ~num_iters = if num_iters > 2 then prev else join prev next

  let make_err_trace set =
    fold
      (fun tr s -> Trace.make_err_trace 0 tr [] |> Fun.flip Errlog.LTRSet.add s)
      set Errlog.LTRSet.empty
end

include Trace
