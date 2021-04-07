open! IStd
open AbsLoc
module F = Format

module Trace = struct
  type elem =
    | SymbolDecl of AbsLoc.Loc.t
    | Input of Procname.t * Location.t
    | Store of Exp.t * Exp.t * Location.t
    | Prune of Exp.t * Location.t
    | Call of Procname.t * Location.t
    | IntOverflow of Procname.t * Exp.t * Location.t
    | FormatString of Procname.t * Exp.t * Location.t
    | IntUnderflow of Procname.t * Exp.t * Location.t
    | CmdInjection of Procname.t * Exp.t * Location.t
    | BufferOverflow of Procname.t * Exp.t * Location.t
  [@@deriving compare, yojson_of]

  type t = elem list [@@deriving compare]

  let append h t = h :: t

  let concat t1 t2 = t1 @ t2

  let make_singleton elem = [elem]

  let make_input pname loc = Input (pname, loc)

  let make_store e1 e2 loc = Store (e1, e2, loc)

  let make_prune e loc = Prune (e, loc)

  let make_call pname loc = Call (pname, loc)

  let make_int_overflow pname e loc = IntOverflow (pname, e, loc)

  let make_int_underflow pname e loc = IntUnderflow (pname, e, loc)

  let make_symbol_decl l = SymbolDecl l

  let make_format_string pname e loc = FormatString (pname, e, loc)

  let make_cmd_injection pname e loc = CmdInjection (pname, e, loc)

  let make_buffer_overflow pname e loc = CmdInjection (pname, e, loc)

  let of_symbol s = SymbolDecl (Allocsite.make_symbol s |> Loc.of_allocsite)

  let make_err_trace t =
    let rec make_err_trace_rec depth t tail =
      let sep = ", " in
      match t with
      | [] ->
          tail
      | Input (pname, l) :: t ->
          let desc = String.concat ~sep ["input"; Procname.to_string pname] in
          let feature = `List [`String "Input"; `String (Procname.to_string pname)] in
          Errlog.make_trace_element ~feature depth l desc [] :: tail |> make_err_trace_rec depth t
      | Store (e1, e2, l) :: t ->
          let desc = String.concat ~sep ["store"; Exp.to_string e1; Exp.to_string e2] in
          let feature = `List [`String "Store"; Exp.yojson_of_t e1; Exp.yojson_of_t e2] in
          Errlog.make_trace_element ~feature depth l desc [] :: tail |> make_err_trace_rec depth t
      | Prune (e, l) :: t ->
          let desc = String.concat ~sep ["prune"; Exp.to_string e] in
          let feature = `List [`String "Prune"; Exp.yojson_of_t e] in
          Errlog.make_trace_element ~feature depth l desc [] :: tail |> make_err_trace_rec depth t
      | Call (pname, l) :: t ->
          let desc = String.concat ~sep ["call"; Procname.to_string pname] in
          let feature = `List [`String "Call"; `String (Procname.to_string pname)] in
          Errlog.make_trace_element ~feature (depth + 1) l desc [] :: tail
          |> make_err_trace_rec depth t
      | IntOverflow (pname, e, l) :: t ->
          let desc =
            String.concat ~sep ["int_overflow"; Procname.to_string pname; Exp.to_string e]
          in
          let feature =
            `List [`String "IntOverflow"; `String (Procname.to_string pname); Exp.yojson_of_t e]
          in
          Errlog.make_trace_element ~feature depth l desc [] :: tail |> make_err_trace_rec depth t
      | IntUnderflow (pname, e, l) :: t ->
          let desc =
            String.concat ~sep ["int_underflow"; Procname.to_string pname; Exp.to_string e]
          in
          let feature =
            `List [`String "IntUnderflow"; `String (Procname.to_string pname); Exp.yojson_of_t e]
          in
          Errlog.make_trace_element ~feature (depth + 1) l desc [] :: tail
          |> make_err_trace_rec depth t
      | FormatString (pname, e, l) :: t ->
          let desc =
            String.concat ~sep ["format_string"; Procname.to_string pname; Exp.to_string e]
          in
          let feature =
            `List [`String "FormatString"; `String (Procname.to_string pname); Exp.yojson_of_t e]
          in
          Errlog.make_trace_element ~feature depth l desc [] :: tail |> make_err_trace_rec depth t
      | CmdInjection (pname, e, l) :: t ->
          let desc =
            String.concat ~sep ["cmd_injection"; Procname.to_string pname; Exp.to_string e]
          in
          let feature =
            `List [`String "CmdInjection"; `String (Procname.to_string pname); Exp.yojson_of_t e]
          in
          Errlog.make_trace_element ~feature depth l desc [] :: tail |> make_err_trace_rec depth t
      | BufferOverflow (pname, e, l) :: t ->
          let desc =
            String.concat ~sep ["buffer_overflow"; Procname.to_string pname; Exp.to_string e]
          in
          let feature =
            `List [`String "BufferOverflow"; `String (Procname.to_string pname); Exp.yojson_of_t e]
          in
          Errlog.make_trace_element ~feature depth l desc [] :: tail |> make_err_trace_rec depth t
      | SymbolDecl _ :: t ->
          make_err_trace_rec depth t tail
    in
    make_err_trace_rec 0 t []


  let last_elem t = List.last t

  let src_may_match src_loc tr =
    List.exists tr ~f:(fun tr_elem ->
        match tr_elem with
        | SymbolDecl _ ->
            true
        | Input (_, input_loc) ->
            Location.equal src_loc input_loc
        | _ ->
            false)


  let pp_elem fmt = function
    | Input (_, l) ->
        F.fprintf fmt "Input (%a)" Location.pp l
    | Store (_, _, l) ->
        F.fprintf fmt "Store (%a)" Location.pp l
    | Prune (_, l) ->
        F.fprintf fmt "PruneBinop (%a)" Location.pp l
    | Call (_, l) ->
        F.fprintf fmt "Call (%a)" Location.pp l
    | IntOverflow (_, _, l) ->
        F.fprintf fmt "IntOverflow (%a)" Location.pp l
    | IntUnderflow (_, _, l) ->
        F.fprintf fmt "IntUnderflow (%a)" Location.pp l
    | FormatString (_, _, l) ->
        F.fprintf fmt "FormatString (%a)" Location.pp l
    | CmdInjection (_, _, l) ->
        F.fprintf fmt "CmdInjection (%a)" Location.pp l
    | BufferOverflow (_, _, l) ->
        F.fprintf fmt "BufferOverflow (%a)" Location.pp l
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

  let add tr t = if cardinal t >= 50 then t else add tr t

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
             List.exists
               ~f:(fun input_elem ->
                 (* input may be at the second position, because of bin op *)
                 Location.equal src_loc input_elem.Errlog.lt_loc)
               trace)
           s)
  | None ->
      None


include Trace
