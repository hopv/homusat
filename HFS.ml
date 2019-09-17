(* Hierarchical Function System *)

type simple_type =
    | Prop
    | Arrow of simple_type * simple_type

let rec string_of_simple_type = fun t ->
    match t with
    | Prop -> "o"
    | Arrow (l, r) ->
        let sl = string_of_simple_type l in
        let sr = string_of_simple_type r in
        match l with
        | Arrow (_) -> "(" ^ sl ^ ") -> " ^ sr
        | _ -> sl ^ " -> " ^ sr

(* Formulas without fixed-point operators and lambda abstractions *)
type formula =
    (* Bare variables are expressed as empty applications *)
    | Or of formula list
    | And of formula list
    | Box of LTS.label * formula
    | Diamond of LTS.label * formula
    | App of Id.t * (formula list)

let rec string_of_formula = fun fml ->
    let string_of_operand_modal = fun x ->
        match x with
        | Box (_, _) | Diamond (_, _)
        | Or ([]) | And ([])
        | App (_, []) -> string_of_formula x
        | _ -> "(" ^ (string_of_formula x) ^ ")"
    in
    let rec string_of_operand_app = fun x ->
        match x with
        | App (l, r) ->
            let sl = Id.to_string l in
            if r = [] then sl
            else
                let ls = X.List.map string_of_operand_app r in
                let sr = String.concat " " ls in
                "(" ^ sl ^ " " ^ sr ^ ")"
        | Or (xs) | And (xs) ->
            if xs = [] then string_of_formula x
            else "(" ^ (string_of_formula x) ^ ")"
        | _ -> string_of_formula x
    in
    match fml with
    | Or (xs) ->
        if xs = [] then "\\false"
        else
            let ls = X.List.map string_of_formula xs in
            String.concat " \\lor " ls
    | And (xs) ->
        if xs = [] then "\\true"
        else
            let ls = X.List.map string_of_formula xs in
            String.concat " \\land " ls
    | Box (a, x) ->
        let sa = Id.to_string a in
        let sx = string_of_operand_modal x in
        "[" ^ sa ^ "]" ^ sx
    | Diamond (a, x) ->
        let sa = Id.to_string a in
        let sx = string_of_operand_modal x in
        "<" ^ sa ^ ">" ^ sx
    | App (l, r) ->
        let sl = Id.to_string l in
        if r = [] then sl
        else
            let ls = X.List.map string_of_operand_app r in
            let sr = String.concat " " ls in
            sl ^ " " ^ sr

(* Fixed-point operators *)
type fp = Mu | Nu

let string_of_fp = fun fp ->
    match fp with
    | Mu -> "\\mu"
    | Nu -> "\\nu"

type argument = Id.t * simple_type

let string_of_arg = fun (x, t) -> Id.to_string x

let string_of_args = fun args ->
    String.concat " " (X.List.map string_of_arg args)

(* Functions in HFS *)
type func = fp * Id.t * simple_type * (argument list) * formula

let string_of_func = fun func ->
    let (fp, x, t, args, body) = func in
    let sfp = string_of_fp fp in
    let sx = Id.to_string x in
    let sbody = string_of_formula body in
    if args = [] then
        sx ^ " =_" ^ sfp ^ " " ^ sbody
    else
        let sargs = string_of_args args in
        sx ^ " " ^ sargs ^ " =_" ^ sfp ^ " " ^ sbody

(* HFS *)
type t = func list

let to_string = fun funcs ->
    String.concat ";\n" (X.List.map string_of_func funcs) ^ ";"
