(* Hierarchical Function System *)

(* simple types *)
type simple_type =
    | Prop
    | Arrow of simple_type * simple_type

val string_of_simple_type : simple_type -> string

(* formulas without fixpoint operators and lambda abstractions *)
type formula =
    (* | Var of Id.t *)
    (* bare variables are expressed as empty applications *)
    | Or of formula list
    | And of formula list
    | Box of LTS.label * formula
    | Diamond of LTS.label * formula
    | App of Id.t * (formula list)

val string_of_formula : formula -> string

(* fixpoint operators *)
type fp = Mu | Nu

val string_of_fp : fp -> string

(* function arguments *)
type argument = Id.t * simple_type

val string_of_arg : argument -> string
val string_of_args : argument list -> string

(* functions in HFS *)
type func = fp * Id.t * simple_type * (argument list) * formula

val string_of_func : func -> string

(* HFS *)
type t = func list

val to_string : t -> string
