(* flow information *)

(* flows: X \mapsto { \phi | X <~ \phi } *)
(* rev_flows: \phi \mapsto { X | X <~ \phi } *)

(* for construction of type environments *)
(* fqmap: F \mapsto \bigcup { P | (F :: yss, P) is a node of ACG } *)
(* xqmap: X \mapsto \bigcup { P | (X :: yss, P) is a node of ACG } *)
(* aqmap: \phi mapsto \bigcup_{X <~ \phi} xqmap(X) *)
(* fbmap: F \mapsto [ (yss, P) | (F :: yss, P) is a node of ACG ] *)
(* fvmap: F \mapsto { X | X occurs in the body of F } *)
(* ffmap: F \mapsto { G | G occurs in the body of F } *)
(* avmap: \phi \mapsto { X | X occurs in \phi } *)
(* almap: \phi \mapsto { F | F occurs in \phi } *)
(* parents: \phi \mapsto F : F is the parent of \phi *)

(* for propagation of type information *)
(* llmap: F \mapsto { G | F occurs in the body of G } *)
(* lamap: F \mapsto { \phi | F occurs in \phi } *)
(* rlmap: X \mapsto F, where X is an argument of F *)
(* ramap: X \mapsto { \phi | X occurs in \phi } *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module IdSet = Id.IdSet
module States = LTS.States
module FmlSet = ACG.FmlSet
module FmlMap = ACG.FmlMap
module FmlsSet = ACG.FmlsSet
module FmlsMap = ACG.FmlsMap

type t

val generate_flow_info :
    HFS.t -> LTS.t -> t

val get_fqmap : t -> States.t LHS.t
val get_aqmap : t -> States.t FmlMap.t
val get_rev_flows : t -> IdSet.t FmlsMap.t
val get_bindings : Id.t -> t -> (HFS.formula list list * States.t) list
val get_contexts : HFS.formula list -> t -> (HFS.formula list list) list
val get_parent : HFS.formula list -> t -> Id.t
val get_children : Id.t -> t -> IdSet.t
val get_siblings : HFS.formula list -> t -> IdSet.t
val get_dep_lhs : Id.t -> t -> IdSet.t * FmlsSet.t
val get_dep_rhs : Id.t -> t -> IdSet.t * FmlsSet.t
val print : t -> unit
