open! IStd
open AbsLoc
module F = Format

module Trace = struct
  type elem =
    | SymbolDecl of AbsLoc.Loc.t
    | Input of Procname.t * Location.t
    | BinOp of Binop.t * Location.t
    | Call of Procname.t * Location.t
    | Malloc of Location.t
    | Printf of Location.t
    | Sprintf of Location.t
  [@@deriving compare]

  type t = elem list [@@deriving compare]

  let append h t = h :: t

  let concat t1 t2 = t1 @ t2

  let make_singleton elem = [elem]

  let make_input pname loc = Input (pname, loc)

  let make_binop binop loc = BinOp (binop, loc)

  let make_call pname loc = Call (pname, loc)

  let make_malloc loc = Malloc loc

  let make_symbol_decl l = SymbolDecl l

  let make_printf loc = Printf loc

  let make_spritnf loc = Sprintf loc

  let of_symbol s = SymbolDecl (Allocsite.make_symbol s |> Loc.of_allocsite)

  let make_err_trace t =
    let rec make_err_trace_rec depth t tail =
      match t with
      | [] ->
          tail
      | Input (pname, l) :: t ->
          let desc = String.concat ~sep:" " ["input"; Procname.to_string pname] in
          Errlog.make_trace_element depth l desc [] :: tail |> make_err_trace_rec depth t
      | BinOp (b, l) :: t ->
          let desc = String.concat ~sep:" " ["binop"; Binop.str Pp.text b] in
          Errlog.make_trace_element depth l desc [] :: tail |> make_err_trace_rec depth t
      | Call (pname, l) :: t ->
          let desc = String.concat ~sep:" " ["call"; Procname.to_string pname] in
          Errlog.make_trace_element (depth + 1) l desc [] :: tail |> make_err_trace_rec depth t
      | Malloc l :: t ->
          let desc = "malloc" in
          Errlog.make_trace_element depth l desc [] :: tail |> make_err_trace_rec depth t
      | Printf l :: t ->
          let desc = "printf" in
          Errlog.make_trace_element depth l desc [] :: tail |> make_err_trace_rec depth t
      | Sprintf l :: t ->
          let desc = "sprintf" in
          Errlog.make_trace_element depth l desc [] :: tail |> make_err_trace_rec depth t
      | SymbolDecl _ :: t ->
          make_err_trace_rec depth t tail
    in
    make_err_trace_rec 0 t []


  let last_elem t = List.last t

  let src_may_match src_loc tr =
    match last_elem tr with
    | Some tr_elem -> (
      match tr_elem with
      | SymbolDecl _ ->
          true
      | Input (_, input_loc) ->
          Location.equal src_loc input_loc
      | _ ->
          false )
    | None ->
        false


  let pp_elem fmt = function
    | Input (_, l) ->
        F.fprintf fmt "Input (%a)" Location.pp l
    | BinOp (_, l) ->
        F.fprintf fmt "BinOp (%a)" Location.pp l
    | Call (_, l) ->
        F.fprintf fmt "Call (%a)" Location.pp l
    | Malloc l ->
        F.fprintf fmt "Malloc (%a)" Location.pp l
    | Printf l ->
        F.fprintf fmt "Printf (%a)" Location.pp l
    | Sprintf l ->
        F.fprintf fmt "Sprintf (%a)" Location.pp l
    | SymbolDecl l ->
        F.fprintf fmt "Symbol (%a)" AbsLoc.Loc.pp l


  let pp fmt t =
    F.fprintf fmt "[" ;
    List.iter ~f:(fun e -> F.fprintf fmt "%a, " pp_elem e) t ;
    F.fprintf fmt "]"
end

module Set = struct
  include AbstractDomain.FiniteSet (Trace)

  (* TODO: heuristic. *)
  let join x y = if cardinal x + cardinal y > 50 then x else join x y

  let append h set = map (Trace.append h) set

  let concat set1 set2 =
    if is_empty set1 then set2
    else if is_empty set2 then set1
    else fold (fun t1 set -> fold (fun t2 set -> add (Trace.concat t1 t2) set) set2 set) set1 empty


  let widen ~prev ~next ~num_iters = if num_iters > 2 then prev else join prev next

  let make_err_trace set =
    fold
      (fun tr s -> Trace.make_err_trace tr |> Fun.flip Errlog.LTRSet.add s)
      set Errlog.LTRSet.empty
end

let subset_match_src src_loc ltr_set =
  match ltr_set with
  | Some s ->
      Some
        (Errlog.LTRSet.filter
           (fun trace ->
             match List.hd trace with
             | Some input_elem ->
                 Location.equal src_loc input_elem.lt_loc
             | None ->
                 false)
           s)
  | None ->
      None


include Trace
