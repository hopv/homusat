(* (extended) HES *)

(* simple types *)
type simple_type =
    | Prop
    | TyVar of int
    | Arrow of simple_type * simple_type

(* generate a fresh type variable *)
let gen_type =
    let counter = ref 0 in
    fun () ->
    let i = !counter in
    counter := !counter + 1;
    TyVar (i)

let rec string_of_simple_type = fun t ->
    match t with
    | Prop -> "o"
    | TyVar (i) -> "'t" ^ (string_of_int i)
    | Arrow (l, r) ->
        let sl = string_of_simple_type l in
        let sr = string_of_simple_type r in
        match l with
        | Arrow _ -> "(" ^ sl ^ ") -> " ^ sr
        | _ -> sl ^ " -> " ^ sr

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

let rec string_of_formula = fun fml ->
    let string_of_operand_or = fun x ->
        match x with
        | True (_) | False (_) | Var (_, _)
        | Box (_, _, _) | Diamond (_, _, _)
        | App (_, _) | Or (_, _) -> string_of_formula x
        | _ -> "(" ^ (string_of_formula x) ^ ")"
    in
    let string_of_operand_and = fun x ->
        match x with
        | True (_) | False (_) | Var (_, _)
        | Box (_, _, _) | Diamond (_, _, _)
        | App (_, _) | And (_, _) -> string_of_formula x
        | _ -> "(" ^ (string_of_formula x) ^ ")"
    in
    let string_of_operand_modal = fun x ->
        match x with
        | True (_) | False (_) | Var (_, _)
        | Box (_, _, _) | Diamond (_, _, _) -> string_of_formula x
        | _ -> "(" ^ (string_of_formula x) ^ ")"
    in
    let string_of_operand_app = fun x ->
        match x with
        | True (_) | False (_) | Var (_, _)
        | Box (_, _, _) | Diamond (_, _, _)
        | App (_, _) -> string_of_formula x
        | _ -> "(" ^ (string_of_formula x) ^ ")"
    in
    match fml with
    | True (_) -> "\\true"
    | False (_) -> "\\false"
    | Var (x, _) -> Id.to_string x
    | Or (l, r) ->
        let sl = string_of_operand_or l in
        let sr = string_of_operand_or r in
        sl ^ " \\lor " ^ sr
    | And (l, r) ->
        let sl = string_of_operand_and l in
        let sr = string_of_operand_and r in
        sl ^ " \\land " ^ sr
    | Box (a, x, _) ->
        let sa = Id.to_string a in
        let sx = string_of_operand_modal x in
        "[" ^ sa ^ "]" ^ sx
    | Diamond (a, x, _) ->
        let sa = Id.to_string a in
        let sx = string_of_operand_modal x in
        "<" ^ sa ^ ">" ^ sx
    | App (l, r) ->
        let sl = string_of_operand_app l in
        let sr = string_of_operand_modal r in
        sl ^ " " ^ sr
    | Abs ((x, _), t, body, _) ->
        let sx = Id.to_string x in
        let st = string_of_simple_type t in
        let sbody = string_of_formula body in
        "\\lambda " ^ sx ^ " : " ^ st ^ ". " ^ sbody
    | Mu ((x, _), t, body, _) ->
        let sx = Id.to_string x in
        let st = string_of_simple_type t in
        let sbody = string_of_formula body in
        "\\mu " ^ sx ^ " : " ^ st ^ ". " ^ sbody
    | Nu ((x, _), t, body, _) ->
        let sx = Id.to_string x in
        let st = string_of_simple_type t in
        let sbody = string_of_formula body in
        "\\nu " ^ sx ^ " : " ^ st ^ ". " ^ sbody

(* fixed-point operators *)
type fp = Mu | Nu

let string_of_fp = fun fp ->
    match fp with
    | Mu -> "\\mu"
    | Nu -> "\\nu"

(* equations in HES *)
type equation = fp * (Id.t * Position.t) * simple_type * formula

let string_of_equation = fun eq ->
    let (fp, (x, _), t, fml) = eq in
    let sx = Id.to_string x in
    let st = string_of_simple_type t in
    let sfml = string_of_formula fml in
    let seq = "=_" ^ (string_of_fp fp) in
    sx ^ " : " ^ st ^ " " ^ seq ^ " " ^ sfml

(* (extended) HES *)
type t = equation list

let to_string = fun eqs ->
    String.concat ";\n" (List.map string_of_equation eqs) ^ ";"
