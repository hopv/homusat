(* Labeled Transition System *)

type state = int
type label = Id.t

type transition = state * label * state

module States : X.Set.S with type elt = state
module Actions : X.Set.S with type elt = label
module Delta : X.Map.S with type key = state * label

(* LTS: (Q, A, \delta, q_{0}) *)
type t = States.t * Actions.t * (States.t Delta.t) * state

val of_transitions : state option -> transition list -> t
val state_of_string : string -> state
val label_of_string : string -> label
val string_of_state : state -> string
val string_of_label : label -> string
val to_string : t -> string
