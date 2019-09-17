(* Abstract Configuration Graph *)

(*** Rough Sketch of Construction ***)
(*
0. Set (F_{1}, {q_{0}}) as the root
1. For each node (F \phi_{1} ... \phi_{\ell}, P), where an equation of the
   form F X_{1} ... X_{\ell} =_{\alpha} \psi_{F} is in the HES,
   1.0. Add bindings of the form X_{k} <~ \phi_{k}
   1.1. Add (\psi_{F}, P) as a child node (if there is already a node of the
        form (\psi_{F}, P'), then update it to (\psi_{F}, P \cup P')
2. For each node (X \phi_{1} ... \phi_{\ell}, P), where X is a rhs variable,
   add (\phi' \phi_{1} ... \phi_{\ell}, P) as a child node for each \phi'
   such that X <~ \phi'
3. For each node (op \phi_{1} ... \phi_{\ell}, P), where op is an operator,
   calculate the set of possible states P_{k} for each k and add (\phi_{k},
   P_{k}) as a child node
4. Argument formulas that are applied simultaneously and thus share a common
   context are treated inseparately
*)

module LHS = Id.IdMap
module RHS = Id.IdMap
module IdSet = Id.IdSet
module States = LTS.States
module Delta = LTS.Delta

type formula =
    | Or of Enc.elt list
    | And of Enc.elt list
    | Box of Id.t * Enc.elt
    | Diamond of Id.t * Enc.elt
    | App of Id.t * ((Enc.elt list) list)

module FmlSet = Set.Make (struct
    type t = Enc.elt
    let compare : t -> t -> int = compare
end)

module FmlSet2 = Set.Make (struct
    type t = formula
    let compare : t -> t -> int = compare
end)

module FmlsSet = Set.Make (struct
    type t = Enc.elt list
    let compare : t -> t -> int = compare
end)

module FmlMap = X.Map.Make (struct
    type t = Enc.elt
    let compare : t -> t -> int = compare
end)

module FmlMap2 = X.Map.Make (struct
    type t = formula
    let compare : t -> t -> int = compare
end)

module FmlsMap = X.Map.Make (struct
    type t = Enc.elt list
    let compare : t -> t -> int = compare
end)

(* ACG: (nodes, flows, rev_flows) *)
type t = States.t FmlMap2.t * FmlSet.t RHS.t * Id.t list list FmlsMap.t

let convert = fun fml ->
    match Enc.decode fml with
    | Enc.Or (xs) -> Or (xs)
    | Enc.And (xs) -> And (xs)
    | Enc.Box (a, x) -> Box (a, x)
    | Enc.Diamond (a, x) -> Diamond (a, x)
    | Enc.App (x, ys) ->
        if ys = [] then App (x, [])
        else App (x, [ys])

let push = fun fml qs queue ->
    let ps = FmlMap2.find_default States.empty fml queue in
    let qs = States.union ps qs in
    FmlMap2.add fml qs queue

let initial_node = fun funcs lts ->
    let (_, x, _, _, _) = List.hd funcs in
    let (_, _, _, q0) = lts in
    (App (x, []), States.singleton q0)

(* the set of states reachable through a modal operator *)
let next_states = fun delta qs a ->
    let f = fun delta a q acc ->
        let qs = Delta.find_default States.empty (q, a) delta in
        States.union qs acc
    in
    States.fold (f delta a) qs States.empty

(* append zss as additional arguments to the formula fml *)
let append_args = fun fml zss ->
    match Enc.decode fml with
    | Enc.App (x, ys) ->
        if ys = [] then App (x, zss)
        else App (x, ys :: zss)
    | _ -> (* assert (zss = []); *) convert fml

(* push (phi :: yss, qs) for each phi such that x <~ phi *)
let push_flows = fun x yss qs flows queue ->
    let f = fun yss qs z queue ->
        let z = append_args z yss in
        push z qs queue
    in
    let zs = RHS.find_default FmlSet.empty x flows in
    FmlSet.fold (f yss qs) zs queue

(* update an old node *)
let update_node = fun fmap delta
                      queue nodes flows rev_flows xnodes fml qs ->
    let qs' = FmlMap2.find fml nodes in
    let qs_diff = States.diff qs qs' in
    if States.is_empty qs_diff then
        (queue, nodes, flows, rev_flows, xnodes)
    else
        let nodes = FmlMap2.add fml (States.union qs_diff qs') nodes in
        match fml with
        | Or (xs)
        | And (xs) ->
            let f = fun qs queue x -> push (convert x) qs queue in
            let queue = List.fold_left (f qs_diff) queue xs in
            (queue, nodes, flows, rev_flows, xnodes)
        | Box (a, x)
        | Diamond (a, x) ->
            let qs_next = next_states delta qs_diff a in
            let queue = push (convert x) qs_next queue in
            (queue, nodes, flows, rev_flows, xnodes)
        | App (x, yss) ->
            if LHS.mem x fmap then
                let (_, body) = LHS.find x fmap in
                let queue = push body qs_diff queue in
                (queue, nodes, flows, rev_flows, xnodes)
            else (* x is a rhs variable *)
                let queue = push_flows x yss qs_diff flows queue in
                (queue, nodes, flows, rev_flows, xnodes)

(* push (y :: zss, qs) for each node of the form (x zss, qs) *)
let push_xnodes = fun x y nodes xnodes queue ->
    let f = fun y nodes z queue ->
        match z with
        | App (x, zss) ->
            let y = append_args y zss in
            let qs = FmlMap2.find z nodes in
            push y qs queue
        | _ -> assert false
    in
    let zs = RHS.find_default FmlSet2.empty x xnodes in
    FmlSet2.fold (f y nodes) zs queue

let split_xs = fun xs ys ->
    let rec f = fun xs ys acc ->
        match (xs, ys) with
        | (_, []) -> (List.rev acc, xs)
        | ([], _) -> assert false
        | (x :: xs, y :: ys) -> f xs ys (x :: acc)
    in
    f xs ys []

(* add bindings of the form x <~ y *)
let rec update_flows = fun xs yss queue nodes flows rev_flows xnodes ->
    let f = fun nodes xnodes (queue, flows) x y ->
        let zs = RHS.find_default FmlSet.empty x flows in
        let zs = FmlSet.add y zs in
        let flows = RHS.add x zs flows in
        let queue = push_xnodes x y nodes xnodes queue in
        (queue, flows)
    in
    match yss with
    | [] -> (queue, flows, rev_flows)
    | ys :: yss ->
        let (xs, next_xs) = split_xs xs ys in
        let f = f nodes xnodes in
        let (queue, flows) = List.fold_left2 f (queue, flows) xs ys in
        let xss = FmlsMap.find_default [] ys rev_flows in
        let rev_flows = FmlsMap.add ys (xs :: xss) rev_flows in
        update_flows next_xs yss queue nodes flows rev_flows xnodes

(* fml is of the form App (x, yss) *)
let update_xnodes = fun x fml xnodes ->
    let zs = RHS.find_default FmlSet2.empty x xnodes in
    let zs = FmlSet2.add fml zs in
    RHS.add x zs xnodes

(* expand a new node *)
let expand_node = fun fmap delta
                      queue nodes flows rev_flows xnodes fml qs ->
    let nodes = FmlMap2.add fml qs nodes in
    match fml with
    | Or (xs)
    | And (xs) ->
        let f = fun qs queue x -> push (convert x) qs queue in
        let queue = List.fold_left (f qs) queue xs in
        (queue, nodes, flows, rev_flows, xnodes)
    | Box (a, x)
    | Diamond (a, x) ->
        let qs_next = next_states delta qs a in
        let queue = push (convert x) qs_next queue in
        (queue, nodes, flows, rev_flows, xnodes)
    | App (x, yss) ->
        if LHS.mem x fmap then
            let (args, body) = LHS.find x fmap in
            let (queue, flows, rev_flows) =
                update_flows args yss queue nodes flows rev_flows xnodes
            in
            let queue = push body qs queue in
            (queue, nodes, flows, rev_flows, xnodes)
        else (* x is a rhs variable *)
            let queue = push_flows x yss qs flows queue in
            let xnodes = update_xnodes x fml xnodes in
            (queue, nodes, flows, rev_flows, xnodes)

(* main loop *)
let rec expand = fun fmap delta queue nodes flows rev_flows xnodes ->
    Profile.check_time_out "model checking" !Flags.time_out;
    if FmlMap2.is_empty queue then
        (nodes, flows, rev_flows)
    else
        let (fml, qs) = FmlMap2.min_binding queue in
        let queue = FmlMap2.remove fml queue in
        let (queue, nodes, flows, rev_flows, xnodes) =
            if FmlMap2.mem fml nodes then
                update_node fmap delta
                            queue nodes flows rev_flows xnodes fml qs
            else
                expand_node fmap delta
                            queue nodes flows rev_flows xnodes fml qs
        in
        expand fmap delta queue nodes flows rev_flows xnodes

let initial_set = fun funcs lts ->
    let nodes = FmlMap2.empty in
    let flows = RHS.empty in
    let rev_flows = FmlsMap.empty in
    let xnodes = RHS.empty in
    let (fml, qs) = initial_node funcs lts in
    let queue = FmlMap2.singleton fml qs in
    (queue, nodes, flows, rev_flows, xnodes)

let generate_fmap = fun funcs ->
    let f = fun acc func ->
        let (_, x, _, args, fml) = func in
        let args = X.List.map fst args in
        let fml = convert fml in
        LHS.add x (args, fml) acc
    in
    List.fold_left f LHS.empty funcs

let construct = fun funcs lts ->
    let fmap = generate_fmap funcs in
    let (_, _, delta, _) = lts in
    let (queue, nodes, flows, rev_flows, xnodes) = initial_set funcs lts in
    expand fmap delta queue nodes flows rev_flows xnodes
