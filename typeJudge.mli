(* type judgments for lhs variables *)

module Env = Id.IdMap
module Delta = LTS.Delta
module States = LTS.States
module Tau = Types.Tau
module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta
module Epsilon = Types.Epsilon

val reset_memo : unit -> unit
val reset_hoge : Id.t -> unit
val type_envs : States.t Delta.t -> Sigma.t Env.t -> Sigma.t Env.t -> Sigma.t Env.t -> Id.t -> Enc.elt -> Tau.t -> Theta.t
