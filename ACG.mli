(* Abstract Configuration Graph *)

type formula =
    | Or of Enc.elt list
    | And of Enc.elt list
    | Box of Id.t * Enc.elt
    | Diamond of Id.t * Enc.elt
    | App of Id.t * ((Enc.elt list) list)
module LHS = Id.IdMap
module RHS = Id.IdMap
module IdSet = Id.IdSet
module States = LTS.States
module FmlSet : Set.S with type elt = Enc.elt
module FmlSet2 : Set.S with type elt = formula
module FmlsSet : Set.S with type elt = Enc.elt list
module FmlMap : X.Map.S with type key = Enc.elt
module FmlMap2 : X.Map.S with type key = formula
module FmlsMap : X.Map.S with type key = Enc.elt list

(* ACG: (nodes, flows, rev_flows) *)
type t = States.t FmlMap2.t * FmlSet.t RHS.t * Id.t list list FmlsMap.t

val construct : Enc.t -> LTS.t -> t
