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

let fread pname buffer =
  let exec {node; bo_mem_opt; location} ~ret:_ mem =
    let locs = Sem.eval_locs buffer bo_mem_opt mem in
    Dom.PowLocWithIdx.fold
      (fun loc mem ->
        let traces =
          Trace.make_input (Procname.from_string_c_fun pname) location
          |> Trace.make_singleton |> Trace.Set.singleton
        in
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


let slurp_read _ buffer = fread "slurp_read" buffer

let fscanf _ _ args =
  let exec fscanf_model_env ~ret mem =
    match args with
    | _ :: _ ->
        List.fold args ~init:mem ~f:(fun m ProcnameDispatcher.Call.FuncArg.{exp} ->
            let fread_model = fread "fscanf" exp in
            fread_model.exec fscanf_model_env ~ret m)
    | _ ->
        mem
  in
  {exec; check= empty_check_fun}


let g_byte_array_append array data =
  let exec {bo_mem_opt; location} ~ret:_ mem =
    let data_v = Sem.eval data location bo_mem_opt mem in
    let v =
      Dom.PowLocWithIdx.fold
        (fun l v -> Dom.Mem.find l mem |> Dom.Val.join v)
        data_v.powloc Dom.Val.bottom
    in
    let g_byte_array_name = Typ.CStruct (QualifiedCppName.of_qual_string "GByteArray") in
    let g_byte_array_type = Typ.mk (Typ.Tstruct g_byte_array_name) in
    let data_field = Fieldname.make g_byte_array_name "data" in
    let data_field_exp = Exp.Lfield (array, data_field, g_byte_array_type) in
    let data_field_exp_locs = Sem.eval_locs data_field_exp bo_mem_opt mem in
    let icns_block_header_name = Typ.CStruct (QualifiedCppName.of_qual_string "IcnsBlockHeader") in
    let size_field = Fieldname.make icns_block_header_name "size" in
    Dom.PowLocWithIdx.fold
      (fun l m ->
        let size_field_loc = Dom.LocWithIdx.append_field size_field l in
        Dom.Mem.weak_update size_field_loc v m)
      data_field_exp_locs mem
  in
  {exec; check= empty_check_fun}


let recv _ buffer = fread "recv" buffer

let recvfrom pname _ buffer = fread pname buffer

let bswap_16 exp =
  let exec {bo_mem_opt; location} ~ret mem =
    let id, _ = ret in
    let loc = Dom.LocWithIdx.of_loc (Loc.of_id id) in
    let v = Sem.eval exp location bo_mem_opt mem in
    Dom.Mem.add loc v mem
  in
  {exec; check= empty_check_fun}


let getc _ =
  let exec {node; location} ~ret mem =
    let id, _ = ret in
    let traces =
      Trace.make_input (Procname.from_string_c_fun "getc") location
      |> Trace.make_singleton |> Trace.Set.singleton
    in
    let v = Dom.UserInput.make node location |> Dom.Val.of_user_input ~traces in
    let loc = Dom.LocWithIdx.of_loc (Loc.of_id id) in
    Dom.Mem.add loc v mem
  in
  {exec; check= empty_check_fun}


let getenv _ =
  let exec {node; bo_mem_opt; location} ~ret:(ret_id, _) mem =
    let traces =
      Trace.make_input (Procname.from_string_c_fun "getenv") location
      |> Trace.make_singleton |> Trace.Set.singleton
    in
    let user_input_v = Dom.UserInput.make node location |> Dom.Val.of_user_input ~traces in
    let ret_loc = Loc.of_id ret_id in
    let getenv_locs =
      ( match bo_mem_opt with
      | Some bo_mem ->
          BufferOverrunDomain.Mem.find_stack ret_loc bo_mem.post
          |> BufferOverrunDomain.Val.get_all_locs
      | None ->
          PowLoc.bot )
      |> Dom.PowLocWithIdx.of_pow_loc
    in
    Dom.Mem.add (Dom.LocWithIdx.of_loc ret_loc) (Dom.Val.of_pow_loc getenv_locs) mem
    |> Dom.PowLocWithIdx.fold (fun loc mem -> Dom.Mem.add loc user_input_v mem) getenv_locs
  in
  {exec; check= empty_check_fun}


let malloc pname size =
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
    let v =
      Sem.eval size location bo_mem_opt mem
      |> Dom.Val.append_trace_elem
           (Trace.make_int_overflow (Procname.from_string_c_fun pname) size location)
    in
    Dom.CondSet.union (Dom.CondSet.make_overflow v location) condset
  in
  {exec; check}


let realloc _ size = malloc "realloc" size

let calloc n size =
  let malloc_size = Exp.BinOp (Binop.Mult (Some Typ.IUInt), n, size) in
  malloc "calloc" malloc_size


let strdup str =
  let exec {location; bo_mem_opt} ~ret mem =
    let id, _ = ret in
    let v = Sem.eval str location bo_mem_opt mem in
    let powloc = Dom.Val.get_powloc v in
    let new_mem =
      Dom.PowLocWithIdx.fold
        (fun l m ->
          let new_v = Dom.Val.append_libcall (Dom.Mem.find l m) "strdup" location in
          Dom.Mem.update l new_v m)
        powloc mem
    in
    let loc = Dom.LocWithIdx.of_loc (Loc.of_id id) in
    Dom.Mem.add loc v new_mem
  in
  {exec; check= empty_check_fun}


let strcpy dst src =
  let exec {bo_mem_opt; location} ~ret:_ mem =
    let src_locs = Sem.eval_locs src bo_mem_opt mem in
    let src_deref_v =
      Dom.PowLocWithIdx.fold
        (fun loc v -> Dom.Mem.find loc mem |> Dom.Val.join v)
        src_locs Dom.Val.bottom
    in
    let dst_locs = Sem.eval_locs dst bo_mem_opt mem in
    Dom.PowLocWithIdx.fold
      (fun loc m ->
        let new_v = Dom.Val.append_libcall src_deref_v "strcpy" location in
        Dom.Mem.add loc new_v m)
      dst_locs mem
  in
  {exec; check= empty_check_fun}


let memcpy pname dst src len =
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
  let check {location; bo_mem_opt} mem condset =
    let v =
      Sem.eval len location bo_mem_opt mem
      |> Dom.Val.append_trace_elem
           (Trace.make_int_underflow (Procname.from_string_c_fun pname) len location)
    in
    Dom.CondSet.union (Dom.CondSet.make_underflow v location) condset
  in
  {exec; check}


let memset pname _ _ len =
  let check {location; bo_mem_opt} mem condset =
    let v =
      Sem.eval len location bo_mem_opt mem
      |> Dom.Val.append_trace_elem
           (Trace.make_int_underflow (Procname.from_string_c_fun pname) len location)
    in
    Dom.CondSet.union (Dom.CondSet.make_underflow v location) condset
  in
  {exec= empty_exec_fun; check}


let strtok src =
  let exec {location; bo_mem_opt} ~ret mem =
    let v = Sem.eval src location bo_mem_opt mem in
    let powloc = Dom.Val.get_powloc v in
    let new_mem =
      Dom.PowLocWithIdx.fold
        (fun l m ->
          let new_v = Dom.Val.append_libcall (Dom.Mem.find l m) "strtok" location in
          Dom.Mem.update l new_v m)
        powloc mem
    in
    let retloc = fst ret |> Loc.of_id |> Dom.LocWithIdx.of_loc in
    Dom.Mem.add retloc v new_mem
  in
  {exec; check= empty_check_fun}


let strcmp s1 s2 =
  let exec {location; bo_mem_opt} ~ret:_ mem =
    let add_libcall s m =
      let locs = Sem.eval s location bo_mem_opt mem |> Dom.Val.get_powloc in
      Dom.PowLocWithIdx.fold
        (fun loc acc_m ->
          let v = Dom.Mem.find loc acc_m in
          Dom.Mem.update loc (Dom.Val.append_libcall v "strcmp" location) acc_m)
        locs m
    in
    add_libcall s1 mem |> add_libcall s2
  in
  {exec; check= empty_check_fun}


let printf pname str =
  let check {location; bo_mem_opt} mem condset =
    let v = Sem.eval str location bo_mem_opt mem in
    let v_powloc = v |> Dom.Val.get_powloc in
    let user_input_val =
      Dom.PowLocWithIdx.fold
        (fun loc v -> Dom.Val.join v (Dom.Mem.find_on_demand loc mem))
        v_powloc Dom.Val.bottom
      |> Dom.Val.append_trace_elem
           (Trace.make_format_string (Procname.from_string_c_fun pname) str location)
    in
    Dom.CondSet.union (Dom.CondSet.make_format user_input_val location) condset
  in
  {exec= empty_exec_fun; check}


let sprintf pname target str args =
  let printf_model = printf pname str in
  let exec {location; bo_mem_opt} ~ret mem =
    match args with
    | _ :: _ ->
        let target_val = Sem.eval target location bo_mem_opt mem in
        let locs = Dom.Val.get_powloc target_val in
        let v = Dom.Mem.find_set locs mem in
        let v =
          List.fold args
            ~f:(fun v ProcnameDispatcher.Call.FuncArg.{exp} ->
              let ploc = Sem.eval exp location bo_mem_opt mem |> Dom.Val.get_powloc in
              let v' =
                Dom.PowLocWithIdx.fold
                  (fun loc v -> Dom.Val.join v (Dom.Mem.find_on_demand loc mem))
                  ploc Dom.Val.bottom
              in
              Dom.Val.join v v')
            ~init:v
        in
        let retloc = fst ret |> Loc.of_id |> Dom.LocWithIdx.of_loc in
        Dom.PowLocWithIdx.fold (fun l m -> Dom.Mem.add l v m) locs mem
        |> Dom.Mem.add retloc target_val
    | _ ->
        mem
  in
  let check ({location; bo_mem_opt} as env) mem condset =
    List.fold args
      ~f:(fun cdset ProcnameDispatcher.Call.FuncArg.{exp} ->
        let sprintf_trace_elem =
          Trace.make_buffer_overflow (Procname.from_string_c_fun pname) exp location
        in
        let v =
          Sem.eval exp env.location bo_mem_opt mem |> Dom.Val.append_trace_elem sprintf_trace_elem
        in
        let v_powloc = v |> Dom.Val.get_powloc in
        let deref_user_input_v =
          Dom.PowLocWithIdx.fold
            (fun loc v -> Dom.Val.join v (Dom.Mem.find_on_demand loc mem))
            v_powloc Dom.Val.bottom
          |> Dom.Val.append_trace_elem sprintf_trace_elem
        in
        Dom.CondSet.union (Dom.CondSet.make_buffer_overflow v env.location) cdset
        |> Dom.CondSet.union (Dom.CondSet.make_buffer_overflow deref_user_input_v env.location))
      ~init:condset
    |> printf_model.check env mem
  in
  {exec; check}


let snprintf pname _ _ str args = sprintf pname Exp.null str args

let fprintf pname _ str = printf pname str

let vfprintf = fprintf "vfprintf"

let sscanf _ source _ args =
  let exec {location; bo_mem_opt} ~ret:_ mem =
    let source_val = Sem.eval source location bo_mem_opt mem in
    List.fold args
      ~f:(fun mem ProcnameDispatcher.Call.FuncArg.{exp} ->
        let ploc = Sem.eval_locs exp bo_mem_opt mem in
        Dom.PowLocWithIdx.fold
          (fun loc mem ->
            let v = Dom.Val.join (Dom.Mem.find_on_demand loc mem) source_val in
            Dom.Mem.add loc v mem)
          ploc mem)
      ~init:mem
  in
  {exec; check= empty_check_fun}


let gnutls_x509_crt_get_subject_alt_name _ _ ret_addr =
  let exec {node; location; bo_mem_opt} ~ret:_ mem =
    let locs = Sem.eval_locs ret_addr bo_mem_opt mem in
    Dom.PowLocWithIdx.fold
      (fun loc mem ->
        let traces =
          Trace.make_input
            (Procname.from_string_c_fun "gnutls_x509_crt_get_subject_alt_name")
            location
          |> Trace.make_singleton |> Trace.Set.singleton
        in
        let user_input_v = Dom.UserInput.make node location |> Dom.Val.of_user_input ~traces in
        let mem = Dom.Mem.add loc user_input_v mem in
        let l = Dom.LocWithIdx.to_loc loc in
        Dom.Mem.fold
          (fun l' _ mem ->
            match l' with
            | Loc field when Loc.is_field_of ~loc:l ~field_loc:field ->
                Dom.Mem.add l' user_input_v mem
            | _ ->
                mem)
          mem mem)
      locs mem
  in
  {exec; check= empty_check_fun}


let readdir _ =
  let exec {pname; node; node_hash; location} ~ret:(ret_id, _) mem =
    let traces =
      Trace.make_input (Procname.from_string_c_fun "readdir") location
      |> Trace.make_singleton |> Trace.Set.singleton
    in
    let user_input_v = Dom.UserInput.make node location |> Dom.Val.of_user_input ~traces in
    let ret_loc = ret_id |> Loc.of_id |> Dom.LocWithIdx.of_loc in
    let struct_allocsite =
      Allocsite.make pname ~node_hash ~inst_num:0 ~dimension:1 ~path:None
        ~represents_multiple_values:false
    in
    let struct_loc = Loc.of_allocsite struct_allocsite |> Dom.LocWithIdx.of_loc in
    let struct_powloc = Dom.PowLocWithIdx.singleton struct_loc in
    let dirent_type_name =
      if
        SourceFile.has_extension location.file ~ext:"c"
        || SourceFile.has_extension location.file ~ext:"h"
      then Typ.Name.C.from_qual_name (QualifiedCppName.of_qual_string "dirent")
      else Typ.Name.Cpp.from_qual_name Typ.NoTemplate (QualifiedCppName.of_qual_string "dirent")
    in
    let d_name_field = Fieldname.make dirent_type_name "d_name" in
    let d_name_loc = Dom.LocWithIdx.append_field d_name_field struct_loc in
    let d_name_allocsite =
      Allocsite.make pname ~node_hash ~inst_num:1 ~dimension:1 ~path:None
        ~represents_multiple_values:false
    in
    let d_name_allocsite_loc = Loc.of_allocsite d_name_allocsite |> Dom.LocWithIdx.of_loc in
    let d_name_allocsite_powloc = Dom.PowLocWithIdx.singleton d_name_allocsite_loc in
    Dom.Mem.add ret_loc (Dom.Val.of_pow_loc struct_powloc) mem
    |> Dom.Mem.add d_name_loc (Dom.Val.of_pow_loc d_name_allocsite_powloc)
    |> Dom.Mem.add d_name_allocsite_loc user_input_v
  in
  {exec; check= empty_check_fun}


let getopt _ _ _ =
  let exec {node; node_hash; location} ~ret:_ mem =
    let traces =
      Trace.make_input (Procname.from_string_c_fun "getopt") location
      |> Trace.make_singleton |> Trace.Set.singleton
    in
    let user_input_v = Dom.UserInput.make node location |> Dom.Val.of_user_input ~traces in
    let optarg_pvar = Pvar.mk_global (Mangled.from_string "optarg") in
    let optarg_loc = Loc.of_pvar optarg_pvar |> Dom.LocWithIdx.of_loc in
    let new_allocsite =
      Allocsite.make
        (Procname.from_string_c_fun "getopt")
        ~node_hash ~inst_num:0 ~dimension:1 ~path:None ~represents_multiple_values:false
    in
    let alloc_loc = new_allocsite |> Loc.of_allocsite |> Dom.LocWithIdx.of_loc in
    let alloc_powloc = [alloc_loc] |> Dom.PowLocWithIdx.of_list in
    Dom.Mem.add optarg_loc (Dom.Val.of_pow_loc alloc_powloc) mem
    |> Dom.Mem.add alloc_loc user_input_v
  in
  {exec; check= empty_check_fun}


let atoi str =
  let exec {bo_mem_opt; location} ~ret mem =
    let ret_id, ret_typ = ret in
    let ret_loc = ret_id |> Loc.of_id |> Dom.LocWithIdx.of_loc in
    let str_v = Sem.eval str location bo_mem_opt mem in
    let ret_v =
      Dom.PowLocWithIdx.fold
        (fun l v -> Dom.Mem.find_on_demand ~typ:ret_typ l mem |> Dom.Val.join v)
        (Dom.Val.get_powloc str_v) Dom.Val.bottom
    in
    Dom.Mem.add ret_loc ret_v mem
  in
  {exec; check= empty_check_fun}


let system pname str =
  let check {location; bo_mem_opt} mem condset =
    let v = Sem.eval str location bo_mem_opt mem in
    let v_powloc = v |> Dom.Val.get_powloc in
    let user_input_val =
      Dom.PowLocWithIdx.fold
        (fun loc v -> Dom.Val.join v (Dom.Mem.find_on_demand loc mem))
        v_powloc Dom.Val.bottom
      |> Dom.Val.append_trace_elem
           (Trace.make_cmd_injection (Procname.from_string_c_fun pname) str location)
    in
    Dom.CondSet.union (Dom.CondSet.make_exec user_input_val location) condset
  in
  {exec= empty_exec_fun; check}


let execl pname str args =
  let system_model = system pname str in
  let check ({location; bo_mem_opt} as env) mem condset =
    List.fold args
      ~f:(fun condset ProcnameDispatcher.Call.FuncArg.{exp} ->
        let v = Sem.eval exp location bo_mem_opt mem in
        let v_powloc = v |> Dom.Val.get_powloc in
        let user_input_val =
          Dom.PowLocWithIdx.fold
            (fun loc v -> Dom.Val.join v (Dom.Mem.find_on_demand loc mem))
            v_powloc Dom.Val.bottom
          |> Dom.Val.append_trace_elem
               (Trace.make_cmd_injection (Procname.from_string_c_fun pname) exp location)
        in
        Dom.CondSet.union (Dom.CondSet.make_exec user_input_val location) condset)
      ~init:condset
    |> system_model.check env mem
  in
  {exec= empty_exec_fun; check}


let execve pname str argv =
  let system_model = system pname str in
  let check ({location; bo_mem_opt} as env) mem condset =
    let v = Sem.eval argv location bo_mem_opt mem in
    let v_powloc = v |> Dom.Val.get_powloc in
    let v = Dom.Mem.find_set v_powloc mem in
    let v_powloc = v |> Dom.Val.get_powloc in
    let user_input_val =
      Dom.PowLocWithIdx.fold
        (fun loc v -> Dom.Val.join v (Dom.Mem.find_on_demand loc mem))
        v_powloc Dom.Val.bottom
      |> Dom.Val.append_trace_elem
           (Trace.make_cmd_injection (Procname.from_string_c_fun pname) argv location)
    in
    Dom.CondSet.union (Dom.CondSet.make_exec user_input_val location) condset
    |> system_model.check env mem
  in
  {exec= empty_exec_fun; check}


let infer_print exp =
  let exec {location; bo_mem_opt} ~ret:_ mem =
    let v = Sem.eval exp location bo_mem_opt mem in
    L.(debug Analysis Verbose)
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

let check_overflow_underflow pname n =
  let check {location; bo_mem_opt} mem condset =
    let v = Sem.eval n location bo_mem_opt mem in
    let overflow_v =
      Dom.Val.append_trace_elem
        (Trace.make_int_overflow (Procname.from_string_c_fun pname) n location)
        v
    in
    let underflow_v =
      Dom.Val.append_trace_elem
        (Trace.make_int_underflow (Procname.from_string_c_fun pname) n location)
        v
    in
    condset
    |> Dom.CondSet.union (Dom.CondSet.make_overflow overflow_v location)
    |> Dom.CondSet.union (Dom.CondSet.make_underflow underflow_v location)
  in
  {exec= empty_exec_fun; check}


(* Functions for juliet testcases *)
let print_hex_char_line = check_overflow_underflow "printHexCharLine"

let print_int_line = check_overflow_underflow "printIntLine"

let print_unsigned_line = check_overflow_underflow "printUnsignedLine"

let dispatch : Tenv.t -> Procname.t -> unit ProcnameDispatcher.Call.FuncArg.t list -> 'a =
  let open ProcnameDispatcher.Call in
  let char_typ = Typ.mk (Typ.Tint Typ.IChar) in
  let char_ptr = Typ.mk (Typ.Tptr (char_typ, Pk_pointer)) in
  let base_models =
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
    ; -"fread" <>$ capt_exp $+...$--> fread "fread"
    ; -"fscanf" <>$ capt_exp $+ capt_exp $++$--> fscanf
    ; -"slurp_read" <>$ capt_exp $+ capt_exp $+...$--> slurp_read
    ; -"g_byte_array_append" <>$ capt_exp $+ capt_exp $+...$--> g_byte_array_append
    ; -"fgets" <>$ capt_exp $+...$--> fread "fgets"
    ; -"recv" <>$ capt_exp $+ capt_exp $+...$--> recv
    ; -"recvfrom" <>$ capt_exp $+ capt_exp $+...$--> recvfrom "recvfrom"
    ; -"malloc" <>$ capt_exp $--> malloc "malloc"
    ; -"g_malloc" <>$ capt_exp $--> malloc "g_malloc"
    ; -"__new_array" <>$ capt_exp $--> malloc "__new_array"
    ; -"realloc" <>$ capt_exp $+ capt_exp $+...$--> realloc
    ; -"calloc" <>$ capt_exp $+ capt_exp $+...$--> calloc
    ; -"printf" <>$ capt_exp $+...$--> printf "printf"
    ; -"vprintf" <>$ capt_exp $+...$--> printf "vprintf"
    ; -"sprintf" <>$ capt_exp $+ capt_exp $++$--> sprintf "sprintf"
    ; -"snprintf" <>$ capt_exp $+ capt_exp $+ capt_exp $++$--> snprintf "snprintf"
    ; -"vsprintf" <>$ capt_exp $+ capt_exp $++$--> sprintf "vsprintf"
    ; -"vsnprintf" <>$ capt_exp $+ capt_exp $+ capt_exp $++$--> snprintf "vsnprintf"
    ; -"fprintf" <>$ capt_exp $+ capt_exp $+...$--> fprintf "fprintf"
    ; -"vfprintf" <>$ capt_exp $+ capt_exp $+...$--> vfprintf
    ; -"bswap_16" <>$ capt_exp $--> bswap_16
    ; -"__bswap_16" <>$ capt_exp $--> bswap_16
    ; -"getc" <>$ capt_exp $--> getc
    ; -"_IO_getc" <>$ capt_exp $--> getc
    ; -"getenv" <>$ capt_exp $--> getenv
    ; -"fgetc" <>$ capt_exp $--> getc
    ; -"sscanf" <>$ capt_exp $+ capt_exp $++$--> sscanf "sscanf"
    ; -"strtok" <>$ capt_exp $+...$--> strtok
    ; -"strdup" <>$ capt_exp $--> strdup
    ; -"strcpy" <>$ capt_exp $+ capt_exp $+...$--> strcpy
    ; -"strcmp" <>$ capt_exp $+ capt_exp $+...$--> strcmp
    ; -"memcpy" <>$ capt_exp $+ capt_exp $+ capt_exp $+...$--> memcpy "memcpy"
    ; -"memset" <>$ capt_exp $+ capt_exp $+ capt_exp $+...$--> memset "memset"
    ; -"gnutls_x509_crt_get_subject_alt_name"
      <>$ capt_exp $+ capt_exp $+ capt_exp $+...$--> gnutls_x509_crt_get_subject_alt_name
    ; -"readdir" <>$ capt_exp $--> readdir
    ; -"getopt" <>$ capt_exp $+ capt_exp $+ capt_exp $+...$--> getopt
    ; -"atoi" <>$ capt_exp $--> atoi
    ; -"system" <>$ capt_exp $--> system "system"
    ; -"popen" <>$ capt_exp $+...$--> system "popen"
    ; -"execl" <>$ capt_exp $++$--> execl "execl"
    ; -"execv" <>$ capt_exp $+...$--> system "execv"
    ; -"execle" <>$ capt_exp $+...$--> system "execle"
    ; -"execve" <>$ capt_exp $+ capt_exp $+...$--> execve "execve"
    ; -"execlp" <>$ capt_exp $+...$--> system "execlp"
    ; -"execvp" <>$ capt_exp $+...$--> system "execvp"
    ; -"__infer_print__" <>$ capt_exp $--> infer_print ]
  in
  let juliet_models =
    [ -"printHexCharLine" <>$ capt_exp $--> print_hex_char_line
    ; -"printIntLine" <>$ capt_exp $--> print_int_line
    ; -"printUnsignedLine" <>$ capt_exp $--> print_unsigned_line ]
  in
  let models = if Config.juliet then List.append juliet_models base_models else base_models in
  make_dispatcher models
