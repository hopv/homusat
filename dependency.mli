(* priority queue for saturation loop *)

type element = Function of Id.t | Formulas of HFS.formula list

module Queue : sig
    type t
    type elt
    val init : HFS.t -> Flow.t -> t
    val is_empty : t -> bool
    val push_deps_func : Id.t -> t -> t
    val push_deps_formulas : HFS.formula list -> t -> t
    val min_elt : t -> elt
    val remove : elt -> t -> t
    val decode : elt -> element
end
