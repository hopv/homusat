(* Type checks for argument formulas *)

module Env = Id.IdMap
module Delta = LTS.Delta
module States = LTS.States
module Tau = Types.Tau
module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta

val reset_memo : unit -> unit
val reset_hoge : Enc.elt -> unit
val types : States.t -> States.t Delta.t -> Sigma.t Env.t -> Sigma.t Env.t -> Enc.elt -> Sigma.t
