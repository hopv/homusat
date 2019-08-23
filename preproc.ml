(* preprocesses *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module IdSet = Id.IdSet
module States = LTS.States
module Delta = LTS.Delta

(* get all variables occurring in fml *)
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

(* the set of lhs variables *)
let get_parents = fun funcs ->
    let f = fun acc func ->
        let (_, x, _, _, _) = func in
        IdSet.add x acc
    in
    List.fold_left f IdSet.empty funcs

(* F \mapsto { G | G occurs in the body of F } *)
let generate_childrens = fun funcs ->
    let f = fun parents acc func ->
        let (_, x, _, _, fml) = func in
        let xs = get_xs fml in
        let children = IdSet.inter xs parents in
        LHS.add x children acc
    in
    let parents = get_parents funcs in
    List.fold_left (f parents) LHS.empty funcs

(* normal DFS *)
let rec dfs = fun adj x visited ->
    if IdSet.mem x visited then visited
    else
        let visited = IdSet.add x visited in
        let ys = LHS.find_default IdSet.empty x adj in
        IdSet.fold (dfs adj) ys visited

(* remove variables unreachable from initial symbol *)
let remove_unreachables = fun funcs ->
    let f = fun reachables acc func ->
        let (_, x, _, _, _) = func in
        if IdSet.mem x reachables then
            func :: acc
        else acc
    in
    let (_, x, _, _, _) = List.hd funcs in
    let childrens = generate_childrens funcs in
    let reachables = dfs childrens x IdSet.empty in
    List.rev (List.fold_left (f reachables) [] funcs)

(* DFS + sort *)
let rec dfs_aux = fun adj x (visited, acc) ->
    if IdSet.mem x visited then (visited, acc)
    else
        let visited = IdSet.add x visited in
        let ys = LHS.find_default IdSet.empty x adj in
        let (visited, acc) = IdSet.fold (dfs_aux adj) ys (visited, acc) in
        (visited, x :: acc)

(* DFS on reversed graph + scc *)
let rec rdfs_aux = fun radj x (visited, acc) ->
    if IdSet.mem x visited then (visited, acc)
    else
        let visited = IdSet.add x visited in
        let acc = IdSet.add x acc in
        let ys = LHS.find_default IdSet.empty x radj in
        IdSet.fold (rdfs_aux radj) ys (visited, acc)

(* reversed adjacency list *)
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
    sccs

(* topological sort of non-recursive functions *)
let topsort_nonrecs = fun nonrecs childrens ->
    let f = fun nonrecs childrens x acc ->
        let children = LHS.find_default IdSet.empty x childrens in
        let children = IdSet.inter nonrecs children in
        LHS.add x children acc
    in
    let adj = IdSet.fold (f nonrecs childrens) nonrecs LHS.empty in
    let (_, sorted) = IdSet.fold (dfs_aux adj) nonrecs (IdSet.empty, []) in
    sorted

(* topologically sorted list of non-recursive functions *)
let generate_nonrecs = fun funcs ->
    let f = fun childrens acc scc ->
        if IdSet.cardinal scc = 1 then
            let x = IdSet.choose scc in
            let ys = LHS.find_default IdSet.empty x childrens in
            if IdSet.mem x ys then acc (* self-loop *)
            else IdSet.add x acc
        else acc
    in
    let parents = get_parents funcs in
    let childrens = generate_childrens funcs in
    let sccs = scc_decomposition parents childrens in
    let nonrecs = List.fold_left (f childrens) IdSet.empty sccs in
    topsort_nonrecs nonrecs childrens

(* count how many times each function is called *)
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

(* topologically sorted list of functions called only once *)
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

(* remove edges connected with x *)
let restrict_childrens = fun childrens x ->
    let f = fun x y children acc ->
        if IdSet.mem x children then
            let children = IdSet.remove x children in
            LHS.add y children acc
        else acc
    in
    let childrens = LHS.remove x childrens in
    LHS.fold (f x) childrens childrens

(* kernel variable \mapsto descendants *)
(* kernel variable: recursive even when the vertices are restricted *)
(*                  to those that have lower or equal priorities *)
let generate_kernels = fun childrens funcs ->
    let f = fun (childrens, kernels) func ->
        let (fp, x, sort, args, body) = func in
        let children = LHS.find x childrens in
        let descendants = IdSet.fold (dfs childrens) children IdSet.empty in
        let childrens = restrict_childrens childrens x in
        if IdSet.mem x descendants then
            let kernels = LHS.add x descendants kernels in
            (childrens, kernels)
        else (childrens, kernels)
    in
    let seed = (childrens, LHS.empty) in
    let (_, kernels) = List.fold_left f seed funcs in
    kernels

(* kernel nu-variable \mapsto descendants *)
let generate_kernel_nus = fun childrens funcs ->
    let f = fun kernels func ->
        let (fp, x, sort, args, body) = func in
        if fp = HFS.Mu then LHS.remove x kernels
        else kernels
    in
    let kernels = generate_kernels childrens funcs in
    List.fold_left f kernels funcs

(* F -> { kernel G | F calls G and F is a descendant of G } *)
let generate_dep_kernels = fun childrens kernels funcs ->
    let f = fun childrens kernels acc func ->
        let g = fun x kernels child acc ->
            if LHS.mem child kernels then
                let descendants = LHS.find child kernels in
                if IdSet.mem x descendants then
                    IdSet.add child acc
                else acc
            else acc
        in
        let (fp, x, sort, args, body) = func in
        let children = LHS.find x childrens in
        let deps = IdSet.fold (g x kernels) children IdSet.empty in
        LHS.add x deps acc
    in
    List.fold_left (f childrens kernels) LHS.empty funcs

(* fmap: x \mapsto (args, body) *)
let generate_fmap = fun funcs ->
    let f = fun acc func ->
        let (_, x, _, args, fml) = func in
        let rargs = List.rev_map fst args in
        LHS.add x (List.rev rargs, fml) acc
    in
    List.fold_left f LHS.empty funcs

(* priorities for functions *)
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
    let childrens = generate_childrens funcs in
    let kernels = generate_kernels childrens funcs in
    let seed = (0, LHS.empty) in
    let rfuncs = List.rev funcs in
    let (_, priorities) = List.fold_left (f kernels) seed rfuncs in
    priorities

let generate_kernels = fun funcs ->
    let childrens = generate_childrens funcs in
    let kernels = generate_kernel_nus childrens funcs in
    let dep_kernels = generate_dep_kernels childrens kernels funcs in
    let f = fun kernel descendants acc -> IdSet.add kernel acc in
    let kernels = LHS.fold f kernels IdSet.empty in
    (kernels, dep_kernels)
