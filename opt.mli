(* Optimization through removal of unnecessary types *)

module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta

val normalize_sigmass : Sigma.t list list -> Sigma.t list list
val normalize_theta : Theta.t -> Theta.t
val prod_thetas : Theta.t -> Theta.t -> Theta.t
val merge_thetas : Theta.t -> Theta.t -> Theta.t
