module L = Logging
module CFG = ProcCfg.NormalOneInstrPerNode
module BoDomain = BufferOverrunDomain
module BoSemantics = BufferOverrunSemantics
module Dom = APIMisuseDomain
module Sem = APIMisuseSemantics

type model_env =
  { pname: Procname.t
  ; node: CFG.Node.t
  ; node_hash: int
  ; bo_mem_opt: BoDomain.Mem.t AbstractInterpreter.State.t option
  ; location: Location.t }

open ProcnameDispatcher.Call.FuncArg
open AbsLoc

type exec_fun = model_env -> ret:Ident.t * Typ.t -> APIMisuseDomain.Mem.t -> APIMisuseDomain.Mem.t

type check_fun = model_env -> Dom.Mem.t -> Dom.CondSet.t -> Dom.CondSet.t

type model = {exec: exec_fun; check: check_fun}

let empty_exec_fun _ ~ret:_ mem = mem

let empty_check_fun _ _ condset = condset

let empty = {exec= empty_exec_fun; check= empty_check_fun}

let constructor _ {exp} =
  let exec {pname; node_hash} ~ret:_ mem =
    match exp with
    | Exp.Lvar v ->
        let allocsite =
          Allocsite.make pname ~node_hash ~inst_num:0 ~dimension:1 ~path:None
            ~represents_multiple_values:false
        in
        let loc = Loc.of_pvar v |> Dom.LocWithIdx.of_loc in
        let v =
          Loc.of_allocsite allocsite |> Dom.LocWithIdx.of_loc |> Dom.PowLocWithIdx.singleton
          |> Dom.Val.of_pow_loc
        in
        Dom.Mem.add loc v mem
    | _ ->
        L.user_warning "Invalid argument of std::map" ;
        mem
  in
  {exec; check= empty_check_fun}


let at _ {exp= map_exp} {exp= idx} =
  let eval_maploc map_exp mem =
    match map_exp with
    | Exp.Lvar v ->
        Loc.of_pvar v |> Dom.LocWithIdx.of_loc |> Fun.flip Dom.Mem.find mem |> Dom.Val.get_powloc
    | Exp.Var id ->
        Loc.of_id id |> Dom.LocWithIdx.of_loc |> Fun.flip Dom.Mem.find mem |> Dom.Val.get_powloc
    | _ ->
        L.die Die.InternalError "Unreachable"
  in
  let exec {bo_mem_opt} ~ret mem =
    match (map_exp, bo_mem_opt) with
    | Exp.Lvar _, Some bomem | Exp.Var _, Some bomem ->
        let idx_val =
          BoSemantics.eval_locs idx bomem.post
          |> Fun.flip BoDomain.Mem.find_set bomem.pre
          |> BoDomain.Val.get_itv
        in
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
  {exec; check= empty_check_fun}


let fread buffer =
  let exec {node; bo_mem_opt; location} ~ret:_ mem =
    match (buffer, bo_mem_opt) with
    | Exp.Lvar _, Some bomem | Exp.Var _, Some bomem ->
        BoSemantics.eval_locs buffer bomem.pre
        |> Fun.flip
             (PowLoc.fold (fun l mem ->
                  let v = Dom.UserInput.make node location |> Dom.Val.of_user_input in
                  let loc = Dom.LocWithIdx.of_loc l in
                  Dom.Mem.add loc v mem ))
             mem
    | _, _ ->
        mem
  in
  {exec; check= empty_check_fun}


let malloc size =
  let check {location} mem condset =
    let v = Sem.eval size mem in
    Dom.CondSet.add (Dom.Cond.make_overflow v location) condset
  in
  {empty with check}


let dispatch : Tenv.t -> Procname.t -> unit ProcnameDispatcher.Call.FuncArg.t list -> 'a =
  let open ProcnameDispatcher.Call in
  make_dispatcher
    [ -"std" &:: "map" < capt_all >:: "operator[]" $ capt_arg $+ capt_arg $!--> at
    ; -"std" &:: "map" < capt_all >:: "map" $ capt_arg $+? any_arg $+? any_arg $+? any_arg
      $!--> constructor
    ; -"fread" <>$ capt_exp $+...$--> fread
    ; -"malloc" <>$ capt_exp $--> malloc ]
