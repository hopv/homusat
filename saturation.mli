(* saturation loop *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module IdMap = Id.IdMap
module IdSet = Id.IdSet
module States = LTS.States
module FmlsSet = ACG.FmlsSet
module FmlsMap = ACG.FmlsMap
module Tau = Types.Tau
module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta
module Epsilon = Types.Epsilon

exception Over_loop

val saturate : Enc.t -> LTS.t -> IdSet.t -> IdSet.t LHS.t -> Flow.t ->
               Theta.t Epsilon.t IdMap.t
