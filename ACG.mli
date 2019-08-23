(* Abstract Configuration Graph *)

type formula =
    | Or of HFS.formula list
    | And of HFS.formula list
    | Box of Id.t * HFS.formula
    | Diamond of Id.t * HFS.formula
    | App of Id.t * ((HFS.formula list) list)
module LHS = Id.IdMap
module RHS = Id.IdMap
module IdSet = Id.IdSet
module States = LTS.States
module FmlSet : Set.S with type elt = HFS.formula
module FmlSet2 : Set.S with type elt = formula
module FmlsSet : Set.S with type elt = HFS.formula list
module FmlMap : X.Map.S with type key = HFS.formula
module FmlMap2 : X.Map.S with type key = formula
module FmlsMap : X.Map.S with type key = HFS.formula list
type t = States.t FmlMap2.t * FmlSet.t RHS.t * Id.t list list FmlsMap.t

val construct : HFS.t -> LTS.t -> t
