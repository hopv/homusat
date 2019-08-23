(* Analysis of an input file *)

module LHS = Id.IdMap
module Delta = LTS.Delta
module States = LTS.States

let rec ord = fun t ->
    match t with
    | HFS.Prop -> 0
    | HFS.Arrow (x, y) ->
        let x = ord x in
        let y = ord y in
        max (x + 1) y

let get_order = fun funcs ->
    let f = fun acc func ->
        let (_, _, t, _, _) = func in
        max acc (ord t)
    in
    List.fold_left f 0 funcs

let get_arity = fun funcs ->
    let f = fun acc func ->
        let (_, _, _, args, _) = func in
        max acc (List.length args)
    in
    List.fold_left f 0 funcs

let get_priority = fun funcs ->
    let f = fun x p (acc_min, acc_max) ->
        (min p acc_min, max p acc_max)
    in
    let priorities = Preproc.generate_priorities funcs in
    if LHS.is_empty priorities then (0, 0)
    else
        let n = List.length funcs in
        LHS.fold f priorities (n + 1, 0)

(* number of variables, logical connectives, and modal operators *)
(* note that X \lor Y \lor Z is treated as \lor X Y Z for simplicity *)
let rec calc_size = fun acc fml ->
    match fml with
    | HFS.Or (xs) | HFS.And (xs) ->
        List.fold_left calc_size (acc + 1) xs
    | HFS.Box (a, x) | HFS.Diamond (a, x) ->
        calc_size (acc + 1) x
    | HFS.App (x, ys) ->
        List.fold_left calc_size (acc + 1) ys

let get_size = fun funcs ->
    let f = fun acc func ->
        let (_, _, _, _, fml) = func in
        calc_size acc fml
    in
    List.fold_left f 0 funcs

let analyze = fun funcs lts ->
    let size = get_size funcs in
    print_endline ("size of HES: " ^ (string_of_int size));
    let order = get_order funcs in
    print_endline ("maximum order: " ^ (string_of_int order));
    let arity = get_arity funcs in
    print_endline ("maximum arity: " ^ (string_of_int arity));
    let (p, q) = get_priority funcs in
    print_endline ("minimum priority: " ^ (string_of_int p));
    print_endline ("maximum priority: " ^ (string_of_int q));
    print_endline ("number of alternations: " ^ (string_of_int (q - p)));
(*
    let n = List.length funcs in
    print_endline ("number of formulas: " ^ (string_of_int n));
*)
    let (qs, _, _, _) = lts in
    let m = States.cardinal qs in
    print_endline ("number of LTS states: " ^ (string_of_int m))
