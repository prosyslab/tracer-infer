(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module L = Logging

type t =
  { proc_name: Procname.t
  ; proc_location: Location.t
  ; err_key: Errlog.err_key
  ; err_data: Errlog.err_data }
[@@deriving compare]

(** Wrapper of an issue that compares all parts except the procname *)
type err_data_ = Errlog.err_data

(* no derived compare for err_data; just compare the locations *)
let compare_err_data_ (err_data1 : Errlog.err_data) (err_data2 : Errlog.err_data) =
  Errlog.compare_err_data err_data1 err_data2


type proc_name_ = Procname.t

(* ignore proc name *)
let compare_proc_name_ _ _ = 0

type t_ignore_duplicates = t =
  {proc_name: proc_name_; proc_location: Location.t; err_key: Errlog.err_key; err_data: err_data_}
[@@deriving compare]

(* If two issues are identical except for their procnames, they are probably duplicate reports on
     two different instantiations of the same template. We don't want to spam users by reporting
     identical warning on the same line. Accomplish this by sorting without regard to procname, then
     de-duplicating. *)
let sort_filter_issues issues =
  let issues' =
    (* FIXME(T54950303) replace use of filtering with deduplicate *)
    let compare = if Config.filtering then compare_t_ignore_duplicates else compare in
    List.dedup_and_sort ~compare issues
  in
  ( if Config.developer_mode then
    let num_pruned_issues = List.length issues - List.length issues' in
    if num_pruned_issues > 0 then
      L.user_warning "Note: pruned %d duplicate issues@\n" num_pruned_issues ) ;
  issues'
