(* (Extended) HES *)

type simple_type =
    | Prop
    | TyVar of int
    | Arrow of simple_type * simple_type

val gen_type : unit -> simple_type (* Generate a fresh type variable *)
val string_of_simple_type : simple_type -> string

(* HFL formulas *)
type formula =
    | True of Position.t
    | False of Position.t
    | Var of Id.t * Position.t
    | Or of formula * formula
    | And of formula * formula
    | Box of LTS.label * formula * Position.t
    | Diamond of LTS.label * formula * Position.t
    | App of formula * formula
    | Abs of (Id.t * Position.t) * simple_type * formula * Position.t
    | Mu of (Id.t * Position.t) * simple_type * formula * Position.t
    | Nu of (Id.t * Position.t) * simple_type * formula * Position.t

val string_of_formula : formula -> string

(* fixpoint operators *)
type fp = Mu | Nu

val string_of_fp : fp -> string

(* Equations in HES *)
type equation = fp * (Id.t * Position.t) * simple_type * formula

(* (Extended) HES *)
type t = equation list

val to_string : t -> string
