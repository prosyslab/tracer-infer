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
    let locs = Sem.eval_locs buffer bo_mem_opt mem in
    Dom.PowLocWithIdx.fold
      (fun loc mem ->
        let traces = [Trace.make_input location] |> Trace.Set.singleton in
        let v = Dom.UserInput.make node location |> Dom.Val.of_user_input ~traces in
        let mem = Dom.Mem.add loc v mem in
        let l = Dom.LocWithIdx.to_loc loc in
        Dom.Mem.fold
          (fun l' _ mem ->
            match l' with
            | Loc field when Loc.is_field_of ~loc:l ~field_loc:field ->
                Dom.Mem.add l' v mem
            | _ ->
                mem)
          mem mem)
      locs mem
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


let getenv _ = {exec= empty_exec_fun; check= empty_check_fun}

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
  let check {location; bo_mem_opt} mem condset =
    let v = Sem.eval size location bo_mem_opt mem in
    let traces = Trace.Set.append (Trace.make_malloc location) v.Dom.Val.traces in
    Dom.CondSet.add (Dom.Cond.make_overflow {v with traces} location) condset
  in
  {exec; check}


let calloc n size =
  let malloc_size = Exp.BinOp (Binop.Mult (Some Typ.IUInt), n, size) in
  malloc malloc_size


let strdup str =
  let exec {location; bo_mem_opt} ~ret mem =
    let id, _ = ret in
    let v = Sem.eval str location bo_mem_opt mem in
    let loc = Dom.LocWithIdx.of_loc (Loc.of_id id) in
    Dom.Mem.add loc v mem
  in
  {exec; check= empty_check_fun}


let strcpy dst src =
  let exec {bo_mem_opt} ~ret:_ mem =
    let src_locs = Sem.eval_locs src bo_mem_opt mem in
    let src_deref_v =
      Dom.PowLocWithIdx.fold
        (fun loc v -> Dom.Mem.find loc mem |> Dom.Val.join v)
        src_locs Dom.Val.bottom
    in
    let dst_locs = Sem.eval_locs dst bo_mem_opt mem in
    Dom.PowLocWithIdx.fold (fun loc m -> Dom.Mem.add loc src_deref_v m) dst_locs mem
  in
  {exec; check= empty_check_fun}


let strtok src =
  let exec {location; bo_mem_opt} ~ret mem =
    let v = Sem.eval src location bo_mem_opt mem in
    let retloc = fst ret |> Loc.of_id |> Dom.LocWithIdx.of_loc in
    Dom.Mem.add retloc v mem
  in
  {exec; check= empty_check_fun}


let printf str =
  let check {location; bo_mem_opt} mem condset =
    let v = Sem.eval str location bo_mem_opt mem in
    let v_powloc = v |> Dom.Val.get_powloc in
    let user_input_val =
      Dom.PowLocWithIdx.fold
        (fun loc v -> Dom.Val.join v (Dom.Mem.find_on_demand loc mem))
        v_powloc Dom.Val.bottom
    in
    Dom.CondSet.add (Dom.Cond.make_format user_input_val location) condset
  in
  {exec= empty_exec_fun; check}


let sprintf _ str = printf str

let vsnprintf _ _ str = printf str

let infer_print exp =
  let exec {location; bo_mem_opt} ~ret:_ mem =
    let v = Sem.eval exp location bo_mem_opt mem in
    L.(debug Analysis Quiet)
      "__infer_print__(%a) @@ %a: %a\n" Exp.pp exp Location.pp location Dom.Val.pp v ;
    mem
  in
  {exec; check= empty_check_fun}


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
    let check {location; bo_mem_opt} mem condset =
      let locs = Sem.eval other location bo_mem_opt mem |> Dom.Val.get_powloc in
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
          let idx_str_val =
            Sem.eval idx location bo_mem_opt mem |> Dom.Val.get_str |> Dom.Idx.of_str
          in
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


  let check_uninit exp bo_mem_opt mem location condset =
    let locs =
      Sem.eval exp location bo_mem_opt mem
      |> Dom.Val.get_powloc
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
      let v = Sem.eval rv location bo_mem_opt mem in
      Dom.PowLocWithIdx.fold (fun l mem -> Dom.Mem.add l v mem) locs mem
    in
    let check {bo_mem_opt; location} mem condset =
      check_uninit rv bo_mem_opt mem location condset
    in
    {exec; check}


  let copy_constructor _ src =
    let check {bo_mem_opt; location} mem condset =
      check_uninit src bo_mem_opt mem location condset
    in
    {empty with check}


  let plus_equal exp =
    let check {bo_mem_opt; location} mem condset =
      check_uninit exp bo_mem_opt mem location condset
    in
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
    ; -"fgets" <>$ capt_exp $+...$--> fread
    ; -"malloc" <>$ capt_exp $--> malloc
    ; -"g_malloc" <>$ capt_exp $--> malloc
    ; -"__new_array" <>$ capt_exp $--> malloc
    ; -"calloc" <>$ capt_exp $+ capt_exp $+...$--> calloc
    ; -"printf" <>$ capt_exp $+...$--> printf
    ; -"sprintf" <>$ capt_exp $+ capt_exp $+...$--> sprintf
    ; -"vsprintf" <>$ capt_exp $+ capt_exp $+...$--> sprintf
    ; -"vsnprintf" <>$ capt_exp $+ capt_exp $+ capt_exp $+...$--> vsnprintf
    ; -"_IO_getc" <>$ capt_exp $--> getc
    ; -"getenv" <>$ capt_exp $--> getenv
    ; -"fgetc" <>$ capt_exp $--> getc
    ; -"strtok" <>$ capt_exp $+...$--> strtok
    ; -"strdup" <>$ capt_exp $--> strdup
    ; -"strcpy" <>$ capt_exp $+ capt_exp $+...$--> strcpy
    ; -"memcpy" <>$ capt_exp $+ capt_exp $+...$--> strcpy
    ; -"__infer_print__" <>$ capt_exp $--> infer_print ]
