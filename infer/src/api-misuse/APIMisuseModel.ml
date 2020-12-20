module L = Logging
module CFG = ProcCfg.NormalOneInstrPerNode
module BoDomain = BufferOverrunDomain
module BoSemantics = BufferOverrunSemantics
module Dom = APIMisuseDomain
module Sem = APIMisuseSemantics
module Trace = APIMisuseTrace

type model_env =
  { pname: Procname.t
  ; node: CFG.Node.t
  ; node_hash: int
  ; bo_mem_opt: BoDomain.Mem.t AbstractInterpreter.State.t option
  ; location: Location.t }

open AbsLoc

type exec_fun = model_env -> ret:Ident.t * Typ.t -> APIMisuseDomain.Mem.t -> APIMisuseDomain.Mem.t

type check_fun = model_env -> Dom.Mem.t -> Dom.CondSet.t -> Dom.CondSet.t

type model = {exec: exec_fun; check: check_fun}

let empty_exec_fun _ ~ret:_ mem = mem

let empty_check_fun _ _ condset = condset

let empty = {exec= empty_exec_fun; check= empty_check_fun}

let fread buffer =
  let exec {node; bo_mem_opt; location} ~ret:_ mem =
    match bo_mem_opt with
    | Some bomem ->
        let locs = BoSemantics.eval_locs buffer bomem.pre in
        PowLoc.fold
          (fun l mem ->
            let traces = [Trace.make_input location] |> Trace.Set.singleton in
            let v = Dom.UserInput.make node location |> Dom.Val.of_user_input ~traces in
            let loc = Dom.LocWithIdx.of_loc l in
            let mem = Dom.Mem.add loc v mem in
            Dom.Mem.fold
              (fun l' _ mem ->
                match l' with
                | Loc field when Loc.is_field_of ~loc:l ~field_loc:field ->
                    Dom.Mem.add l' v mem
                | _ ->
                    mem)
              mem mem)
          locs mem
    | _ ->
        mem
  in
  {exec; check= empty_check_fun}


let getc _ =
  let exec {node; location} ~ret mem =
    let id, _ = ret in
    let traces = [Trace.make_input location] |> Trace.Set.singleton in
    let v = Dom.UserInput.make node location |> Dom.Val.of_user_input ~traces in
    let loc = Dom.LocWithIdx.of_loc (Loc.of_id id) in
    Dom.Mem.add loc v mem
  in
  {exec; check= empty_check_fun}


let malloc size =
  let exec {bo_mem_opt} ~ret:_ (mem : Sem.Mem.t) =
    match bo_mem_opt with
    | Some bomem ->
        (* not only the return variable but also all fields in case of struct *)
        BoDomain.Mem.fold
          ~f:(fun l v mem ->
            match BoDomain.Mem.find_opt l bomem.pre with
            | None ->
                let loc = Dom.LocWithIdx.of_loc l in
                let array_locs = BoDomain.Val.get_array_locs v in
                let pow_locs = BoDomain.Val.get_pow_loc v in
                let v =
                  AbsLoc.PowLoc.join array_locs pow_locs
                  |> Dom.PowLocWithIdx.of_pow_loc |> Dom.Val.of_pow_loc
                in
                Dom.Mem.add loc v mem
            | Some _ ->
                mem)
          bomem.post mem
    | _ ->
        mem
  in
  let check {location} mem condset =
    let v = Sem.eval size location mem in
    let traces = Trace.Set.append (Trace.make_malloc location) v.Dom.Val.traces in
    Dom.CondSet.add (Dom.Cond.make_overflow {v with traces} location) condset
  in
  {exec; check}


let calloc n size =
  let malloc_size = Exp.BinOp (Binop.Mult (Some Typ.IUInt), n, size) in
  malloc malloc_size


let strdup str =
  let exec {location} ~ret mem =
    let id, _ = ret in
    let v = Sem.eval str location mem in
    let loc = Dom.LocWithIdx.of_loc (Loc.of_id id) in
    Dom.Mem.add loc v mem
  in
  {exec; check= empty_check_fun}


let printf str =
  let check {location} mem condset =
    let v = Sem.eval str location mem in
    let v_powloc = v |> Dom.Val.get_powloc in
    let user_input_val =
      Dom.PowLocWithIdx.fold
        (fun loc v -> Dom.Val.join v (Dom.Mem.find loc mem))
        v_powloc Dom.Val.bottom
    in
    let traces = Trace.Set.append (Trace.make_printf location) v.Dom.Val.traces in
    Dom.CondSet.add (Dom.Cond.make_format {v with traces} user_input_val location) condset
  in
  {exec= empty_exec_fun; check}


let vsnprintf _ _ str = printf str

module StdMap = struct
  let allocate_map pname node_hash pvar mem =
    let allocsite =
      Allocsite.make pname ~node_hash ~inst_num:0 ~dimension:1 ~path:None
        ~represents_multiple_values:false
    in
    let loc = Loc.of_pvar pvar |> Dom.LocWithIdx.of_loc in
    let v =
      Loc.of_allocsite allocsite |> Dom.LocWithIdx.of_loc |> Dom.PowLocWithIdx.singleton
      |> Dom.Val.of_pow_loc
    in
    Dom.Mem.add loc v mem


  let constructor exp =
    let exec {pname; node_hash} ~ret:_ mem =
      match exp with
      | Exp.Lvar v ->
          allocate_map pname node_hash v mem
      | _ ->
          L.user_warning "Invalid argument of std::map" ;
          mem
    in
    {exec; check= empty_check_fun}


  let copy_constructor exp other =
    let exec {pname; node_hash} ~ret:_ mem =
      match exp with
      | Exp.Lvar v ->
          allocate_map pname node_hash v mem (* TODO: copy contents*)
      | _ ->
          L.user_warning "Invalid argument of std::map" ;
          mem
    in
    let check {location} mem condset =
      let locs = Sem.eval other location mem |> Dom.Val.get_powloc in
      Dom.PowLocWithIdx.fold
        (fun l condset ->
          match l with
          | Dom.LocWithIdx.Idx (_, _) ->
              let init = Dom.Mem.find l mem |> Dom.Val.get_init in
              if Dom.Init.equal init Dom.Init.Init |> not then
                Dom.CondSet.add (Dom.Cond.make_uninit l Dom.Init.UnInit location) condset
              else condset
          | _ ->
              condset)
        locs condset
    in
    L.d_printfln_escaped "Map.copy_constructor" ;
    {exec; check}


  let at map_exp idx =
    let eval_maploc map_exp mem =
      match map_exp with
      | Exp.Lvar v ->
          Loc.of_pvar v |> Dom.LocWithIdx.of_loc |> Fun.flip Dom.Mem.find mem |> Dom.Val.get_powloc
      | Exp.Var id ->
          Loc.of_id id |> Dom.LocWithIdx.of_loc |> Fun.flip Dom.Mem.find mem |> Dom.Val.get_powloc
      | _ ->
          L.die Die.InternalError "Unreachable"
    in
    let exec {bo_mem_opt; location} ~ret mem =
      match (map_exp, bo_mem_opt) with
      | Exp.Lvar _, Some bomem | Exp.Var _, Some bomem ->
          let idx_itv_val =
            BoSemantics.eval_locs idx bomem.post
            |> Fun.flip BoDomain.Mem.find_set bomem.pre
            |> BoDomain.Val.get_itv |> Dom.Idx.of_itv
          in
          let idx_str_val = Sem.eval idx location mem |> Dom.Val.get_str |> Dom.Idx.of_str in
          let idx_val = Dom.Idx.join idx_itv_val idx_str_val in
          let retloc = fst ret |> Loc.of_id |> Dom.LocWithIdx.of_loc in
          let maploc = eval_maploc map_exp mem in
          let v =
            Dom.PowLocWithIdx.map (Fun.flip Dom.LocWithIdx.append_idx idx_val) maploc
            |> Dom.Val.of_pow_loc
          in
          Dom.Mem.add retloc v mem
      | _, _ ->
          mem
    in
    L.d_printfln_escaped "Map.at" ;
    {exec; check= empty_check_fun}
end

module BasicString = struct
  let constructor allocator s =
    let exec {bo_mem_opt} ~ret:(id, _) mem =
      match s with
      | Exp.Const (Const.Cstr s) ->
          let allocator_locs = Sem.eval_locs allocator bo_mem_opt mem in
          let loc = id |> Loc.of_id |> Dom.LocWithIdx.of_loc in
          let v = s |> Dom.Str.make |> Dom.Val.of_str in
          let mem = Dom.Mem.add loc v mem in
          Dom.PowLocWithIdx.fold (fun l mem -> Dom.Mem.add l v mem) allocator_locs mem
      | _ ->
          mem
    in
    {exec; check= empty_check_fun}


  let check_uninit exp mem location condset =
    let locs =
      Sem.eval exp location mem |> Dom.Val.get_powloc
      |> Dom.PowLocWithIdx.filter (function Dom.LocWithIdx.Idx (_, _) -> true | _ -> false)
    in
    if Dom.PowLocWithIdx.is_empty locs then condset
    else
      let v =
        Dom.PowLocWithIdx.fold (fun l v -> Dom.Mem.find l mem |> Dom.Val.join v) locs Dom.Val.bottom
        |> Dom.Val.get_init
      in
      if Dom.Init.equal v Dom.Init.Init |> not then
        let absloc = Dom.PowLocWithIdx.choose locs in
        Dom.CondSet.add (Dom.Cond.make_uninit absloc Dom.Init.UnInit location) condset
      else condset


  let assign lv rv =
    let exec {bo_mem_opt; location} ~ret:_ mem =
      let locs = Sem.eval_locs lv bo_mem_opt mem in
      let v = Sem.eval rv location mem in
      Dom.PowLocWithIdx.fold (fun l mem -> Dom.Mem.add l v mem) locs mem
    in
    let check {location} mem condset = check_uninit rv mem location condset in
    {exec; check}


  let copy_constructor _ src =
    let check {location} mem condset = check_uninit src mem location condset in
    {empty with check}


  let plus_equal exp =
    let check {location} mem condset = check_uninit exp mem location condset in
    {empty with check}
end

let dispatch : Tenv.t -> Procname.t -> unit ProcnameDispatcher.Call.FuncArg.t list -> 'a =
  let open ProcnameDispatcher.Call in
  let char_typ = Typ.mk (Typ.Tint Typ.IChar) in
  let char_ptr = Typ.mk (Typ.Tptr (char_typ, Pk_pointer)) in
  make_dispatcher
    [ -"std" &:: "map" < any_typ &+...>:: "operator[]" $ capt_exp $+ capt_exp $--> StdMap.at
    ; -"std" &:: "map" < any_typ &+...>:: "map" $ capt_exp
      $+ capt_exp_of_typ (-"std" &:: "map")
      $--> StdMap.copy_constructor
    ; -"std" &:: "map" < any_typ &+...>:: "map" $ capt_exp $+? any_arg $+? any_arg $+? any_arg
      $--> StdMap.constructor
    ; -"std" &:: "basic_string" < any_typ &+...>:: "basic_string" $ capt_exp
      $+ capt_exp_of_prim_typ char_ptr $+ any_arg $--> BasicString.constructor
    ; -"std" &:: "basic_string" < any_typ &+...>:: "basic_string" $ capt_exp
      $+ capt_exp_of_typ (-"std" &:: "basic_string")
      $--> BasicString.copy_constructor
    ; -"std" &:: "basic_string" < any_typ &+...>:: "operator=" $ capt_exp $+ capt_exp
      $--> BasicString.assign
    ; -"std" &:: "basic_string" < any_typ &+...>:: "operator+=" $ capt_exp $+? any_arg $+? any_arg
      $--> BasicString.plus_equal
    ; -"std" &:: "basic_string" < any_typ &+ any_typ &+ any_typ >:: "basic_string" &::.*--> empty
    ; -"std" &:: "basic_string" < any_typ &+...>:: "basic_string" &::.*--> empty
    ; -"fread" <>$ capt_exp $+...$--> fread
    ; -"malloc" <>$ capt_exp $--> malloc
    ; -"g_malloc" <>$ capt_exp $--> malloc
    ; -"__new_array" <>$ capt_exp $--> malloc
    ; -"calloc" <>$ capt_exp $+ capt_exp $+...$--> calloc
    ; -"printf" <>$ capt_exp $--> printf
    ; -"vsnprintf" <>$ capt_exp $+ capt_exp $+ capt_exp $+...$--> vsnprintf
    ; -"_IO_getc" <>$ capt_exp $--> getc
    ; -"fgetc" <>$ capt_exp $--> getc
    ; -"strdup" <>$ capt_exp $--> strdup ]
