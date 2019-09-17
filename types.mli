(* intersection types *)

module Sigma : X.Set.S with type elt = int
module Tau : sig
    type t = int
    type raw = Sigma.t list * LTS.state
    val encode : raw -> t
    val decode : t -> raw
end
(* type environment *)
module Gamma = Id.IdMap
(* set of type environments *)
module Theta : X.Set.S with type elt = Sigma.t Gamma.t
(* map from tau to something *)
module Epsilon : X.Map.S with type key = int

val register_states : LTS.t -> unit
val is_prop : Tau.t -> bool
val codom : Tau.t -> LTS.state
val drop : Tau.t -> Tau.t -> Tau.t
val annot : 'a list -> Tau.t -> ('a * Sigma.t) list
val strongest_type : HFS.simple_type -> LTS.state -> Tau.t
val string_of_tau : Tau.t -> string
val string_of_sigma : Sigma.t -> string
val string_of_gamma : Sigma.t Gamma.t -> string
val merge_gammas : Sigma.t Gamma.t -> Sigma.t Gamma.t -> Sigma.t Gamma.t
val prod_thetas : Theta.t -> Theta.t -> Theta.t
val merge_epsilons : Theta.t Epsilon.t -> Theta.t Epsilon.t -> Theta.t Epsilon.t
val normalize_gamma : Sigma.t Gamma.t -> Sigma.t Gamma.t
val subtype : Tau.t -> Tau.t -> bool
