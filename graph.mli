(* Basic graph algorithms for parity game solving *)

module LHS = Id.IdMap
module Tau = Types.Tau
module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta
module Epsilon = Types.Epsilon
module IntMap : X.Map.S with type key = int
module Vertex : sig type t = Id.t * Tau.t end
module VS : Set.S with type elt = Vertex.t
module Adj : X.Map.S with type key = Vertex.t

type t = VS.t list Adj.t * Vertex.t
val print : t -> unit

val construct : HFS.t -> LTS.t -> Theta.t Epsilon.t LHS.t -> t
val generate_radj : VS.t list Adj.t -> VS.t Adj.t
val generate_partition : int LHS.t -> VS.t list Adj.t -> (int * VS.t) list
val contains_v0 : t -> bool
