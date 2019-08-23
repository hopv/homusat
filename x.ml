(* extended standard modules *)

module Set = struct
    module type S = sig
        include Set.S
        val of_list : elt list -> t
    end
    module type OrderedType = sig
        type t
        val compare : t -> t -> int
    end
    module Make (Ord : OrderedType) : S with type elt = Ord.t = struct
        include Set.Make (Ord)
        let of_list = fun xs ->
            let f = fun acc x -> add x acc in
            List.fold_left f empty xs
    end
end
module Map = struct
    module type S = sig
        include Map.S
        val find_default : 'a -> key -> 'a t -> 'a
    end
    module type OrderedType = sig
        type t
        val compare : t -> t -> int
    end
    module Make (Ord : OrderedType) : S with type key = Ord.t = struct
        include Map.Make (Ord)
        let find_default = fun default key map ->
            if mem key map then find key map
            else default
    end
end
