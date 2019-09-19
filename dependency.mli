(* Priority queue for the saturation loop *)

type element = Function of Id.t | Formulas of Enc.elt list

module Queue : sig
    type t
    type elt
    val init : Enc.t -> Flow.t -> t
    val is_empty : t -> bool
    val push_deps_func : Id.t -> t -> t
    val push_deps_formulas : Enc.elt list -> t -> t
    val min_elt : t -> elt
    val remove : elt -> t -> t
    val decode : elt -> element
end
