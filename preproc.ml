(* Preprocesses *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module IdSet = Id.IdSet
module States = LTS.States
module Delta = LTS.Delta

(* Get all variables occurring in a formula *)
let get_xs = fun fml ->
    let rec f = fun xs fml ->
        match fml with
        | HFS.Or (ys)
        | HFS.And (ys) ->
            List.fold_left f xs ys
        | HFS.Box (_, x)
        | HFS.Diamond (_, x) -> f xs x
        | HFS.App (x, ys) ->
            let xs = IdSet.add x xs in
            List.fold_left f xs ys
    in
    f IdSet.empty fml

(* Get the set of all lhs variables *)
let get_lhs = fun funcs ->
    let f = fun acc func ->
        let (_, x, _, _, _) = func in
        IdSet.add x acc
    in
    List.fold_left f IdSet.empty funcs

(* F \mapsto { G | G occurs in the body of F } *)
let generate_adj = fun funcs ->
    let f = fun lhs acc func ->
        let (_, x, _, _, fml) = func in
        let ys = get_xs fml in
        let ys = IdSet.inter lhs ys in
        LHS.add x ys acc
    in
    let lhs = get_lhs funcs in
    List.fold_left (f lhs) LHS.empty funcs

(* Ordinary DFS *)
let rec dfs = fun adj x visited ->
    if IdSet.mem x visited then visited
    else
        let visited = IdSet.add x visited in
        let ys = LHS.find_default IdSet.empty x adj in
        IdSet.fold (dfs adj) ys visited

(* Remove the functions unreachable from the initial symbol *)
let remove_unreachables = fun funcs ->
    let f = fun reachables acc func ->
        let (_, x, _, _, _) = func in
        if IdSet.mem x reachables then
            func :: acc
        else acc
    in
    let (_, x, _, _, _) = List.hd funcs in
    let adj = generate_adj funcs in
    let reachables = dfs adj x IdSet.empty in
    List.rev (List.fold_left (f reachables) [] funcs)

(* DFS + sort *)
let rec dfs_aux = fun adj x (visited, acc) ->
    if IdSet.mem x visited then (visited, acc)
    else
        let visited = IdSet.add x visited in
        let ys = LHS.find_default IdSet.empty x adj in
        let (visited, acc) = IdSet.fold (dfs_aux adj) ys (visited, acc) in
        (visited, x :: acc)

(* DFS on the reversed graph + scc *)
let rec rdfs_aux = fun radj x (visited, acc) ->
    if IdSet.mem x visited then (visited, acc)
    else
        let visited = IdSet.add x visited in
        let acc = IdSet.add x acc in
        let ys = LHS.find_default IdSet.empty x radj in
        IdSet.fold (rdfs_aux radj) ys (visited, acc)

(* Reversed adjacency list *)
let generate_radj = fun adj ->
    let f = fun x ys acc ->
        let g = fun x y acc ->
            let xs = LHS.find_default IdSet.empty y acc in
            let xs = IdSet.add x xs in
            LHS.add y xs acc
        in
        IdSet.fold (g x) ys acc
    in
    LHS.fold f adj LHS.empty

(* SCC decomposition + topological sort *)
let scc_decomposition = fun xs adj ->
    let f = fun radj (visited, acc) x ->
        if IdSet.mem x visited then (visited, acc)
        else
            let (visited, scc) = rdfs_aux radj x (visited, IdSet.empty) in
            (visited, scc :: acc)
    in
    let (_, sorted) = IdSet.fold (dfs_aux adj) xs (IdSet.empty, []) in
    let radj = generate_radj adj in
    let (_, sccs) = List.fold_left (f radj) (IdSet.empty, []) sorted in
    List.rev sccs

(* Topologically sorted list of the non-recursive functions *)
let generate_nonrecs = fun funcs ->
    let f = fun adj acc scc ->
        if IdSet.cardinal scc = 1 then
            let x = IdSet.choose scc in
            let ys = LHS.find_default IdSet.empty x adj in
            if IdSet.mem x ys then acc (* Self-loop *)
            else x :: acc
        else acc
    in
    let lhs = get_lhs funcs in
    let adj = generate_adj funcs in
    let sccs = scc_decomposition lhs adj in
    List.rev (List.fold_left (f adj) [] sccs)

(* Count how many times each function is called *)
let rec count_calls_fml = fun acc fml ->
    match fml with
    | HFS.Or (xs)
    | HFS.And (xs) ->
        List.fold_left count_calls_fml acc xs
    | HFS.Box (a, x)
    | HFS.Diamond (a, x) ->
        count_calls_fml acc x
    | HFS.App (x, ys) ->
        let n = LHS.find_default 0 x acc in
        let acc = LHS.add x (n + 1) acc in
        List.fold_left count_calls_fml acc ys

let count_calls_func = fun acc func ->
    let (_, _, _, _, fml) = func in
    count_calls_fml acc fml

(* Topologically sorted list of the functions called only once *)
let generate_onces = fun funcs ->
    let f = fun calls acc x ->
        if LHS.mem x calls then
            let n = LHS.find x calls in
            if n = 1 then x :: acc
            else acc
        else acc
    in
    let nonrecs = generate_nonrecs funcs in
    let calls = List.fold_left count_calls_func LHS.empty funcs in
    List.rev (List.fold_left (f calls) [] nonrecs)

(* Remove the edges connected to x *)
let restrict_adj = fun adj x ->
    let f = fun x y zs acc ->
        if IdSet.mem x zs then
            let zs = IdSet.remove x zs in
            LHS.add y zs acc
        else acc
    in
    let adj = LHS.remove x adj in
    LHS.fold (f x) adj adj

(* Kernel variable \mapsto its descendants *)
(* Kernel variable: A variable recursive even when the vertices are res- *)
(*                  tricted to those that have lower or equal priorities *)
let generate_kernels = fun adj funcs ->
    let f = fun (adj, kernels) func ->
        let (_, x, _, _, _) = func in
        let ys = LHS.find x adj in
        let descendants = IdSet.fold (dfs adj) ys IdSet.empty in
        let adj = restrict_adj adj x in
        if IdSet.mem x descendants then
            let kernels = LHS.add x descendants kernels in
            (adj, kernels)
        else (adj, kernels)
    in
    let (_, kernels) = List.fold_left f (adj, LHS.empty) funcs in
    kernels

(* Kernel nu-variable \mapsto descendants *)
let generate_kernel_nus = fun adj funcs ->
    let f = fun kernels func ->
        let (fp, x, _, _, _) = func in
        if fp = HFS.Mu then LHS.remove x kernels
        else kernels
    in
    let kernels = generate_kernels adj funcs in
    List.fold_left f kernels funcs

(* F \mapsto { G kernel | F calls G and F is a descendant of G } *)
let generate_dep_kernels = fun adj kernels funcs ->
    let f = fun adj kernels acc func ->
        let g = fun kernels x y acc ->
            if LHS.mem y kernels then
                let descendants = LHS.find y kernels in
                if IdSet.mem x descendants then
                    IdSet.add y acc
                else acc
            else acc
        in
        let (_, x, _, _, _) = func in
        let ys = LHS.find x adj in
        let deps = IdSet.fold (g kernels x) ys IdSet.empty in
        LHS.add x deps acc
    in
    List.fold_left (f adj kernels) LHS.empty funcs

(* F kernel \mapsto its priority *)
let generate_priorities = fun funcs ->
    let f = fun kernels (i, acc) func ->
        let (fp, x, _, _, _) = func in
        if LHS.mem x kernels then
            match fp with
            | HFS.Nu ->
                let i = if i mod 2 = 0 then i else i + 1 in
                (i, LHS.add x i acc)
            | HFS.Mu ->
                let i = if i mod 2 = 0 then i + 1 else i in
                (i, LHS.add x i acc)
        else (* (i, LHS.add x 0 acc) *) (i, acc)
    in
    let adj = generate_adj funcs in
    let kernels = generate_kernels adj funcs in
    let seed = (0, LHS.empty) in
    let rfuncs = List.rev funcs in
    let (_, priorities) = List.fold_left (f kernels) seed rfuncs in
    priorities

let generate_kernels = fun funcs ->
    let adj = generate_adj funcs in
    let kernels = generate_kernel_nus adj funcs in
    let dep_kernels = generate_dep_kernels adj kernels funcs in
    let f = fun kernel descendants acc -> IdSet.add kernel acc in
    let kernels = LHS.fold f kernels IdSet.empty in
    (kernels, dep_kernels)
