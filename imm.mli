(* optimization for immediate winning positions *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module BVs = Id.IdSet
module States = LTS.States
module Delta = LTS.Delta
module ToProps = Id.IdSet
module Tau = Types.Tau
module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta
module Epsilon = Types.Epsilon

val optimize : Id.t -> Theta.t Epsilon.t -> Sigma.t LHS.t -> Theta.t Epsilon.t LHS.t -> Theta.t Epsilon.t * Sigma.t LHS.t * Theta.t Epsilon.t LHS.t
