(* preprocesses *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module Delta = LTS.Delta
module States = LTS.States

val remove_unreachables : HFS.t -> HFS.t
val generate_onces : HFS.t -> Id.t list
val generate_nonrecs : HFS.t -> Id.t list
val generate_kernels : HFS.t -> Id.IdSet.t * Id.IdSet.t LHS.t
val generate_fmap : HFS.t -> (Id.t list * HFS.formula) LHS.t
val generate_priorities : HFS.t -> int LHS.t
