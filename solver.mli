(* simple parity game solver *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module Tau = Types.Tau
module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta
module Epsilon = Types.Epsilon

val solve : HFS.t -> LTS.t -> Theta.t Epsilon.t LHS.t -> bool
