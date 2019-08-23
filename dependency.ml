(* priority queue for saturation loop *)
(* based on scc decomposition of dependency graph *)

module IdSet = Id.IdSet
module IdMap = Id.IdMap
module FmlsSet = ACG.FmlsSet
module FmlsMap = ACG.FmlsMap

(* IntSet and IntMap can be replaced with arrays or hash tables *)
module IntSet = Set.Make (struct
   type t = int
   let compare : t -> t -> int = compare
end)
module IntMap = X.Map.Make (struct
   type t = int
   let compare : t -> t -> int = compare
end)

type element = Function of Id.t | Formulas of HFS.formula list

(* DFS + sort *)
let rec dfs_aux = fun adj x (visited, acc) ->
    if IntSet.mem x visited then (visited, acc)
    else
        let visited = IntSet.add x visited in
        let ys = IntMap.find_default IntSet.empty x adj in
        let (visited, acc) =
            IntSet.fold (dfs_aux adj) ys (visited, acc)
        in
        (visited, x :: acc)

(* DFS on reversed graph + scc *)
let rec rdfs_aux = fun radj x (visited, acc) ->
    if IntSet.mem x visited then (visited, acc)
    else
        let visited = IntSet.add x visited in
        let acc = IntSet.add x acc in
        let ys = IntMap.find_default IntSet.empty x radj in
        IntSet.fold (rdfs_aux radj) ys (visited, acc)

(* reversed adjacency list *)
let generate_radj = fun adj ->
    let f = fun x ys acc ->
        let g = fun x y acc ->
            let xs = IntMap.find_default IntSet.empty y acc in
            let xs = IntSet.add x xs in
            IntMap.add y xs acc
        in
        IntSet.fold (g x) ys acc
    in
    IntMap.fold f adj IntMap.empty

let scc_decomposition = fun xs adj ->
    let f = fun radj (visited, acc) x ->
        if IntSet.mem x visited then (visited, acc)
        else
            let (visited, scc) = rdfs_aux radj x (visited, IntSet.empty) in
            (visited, scc :: acc)
    in
    let (_, sorted) = IntSet.fold (dfs_aux adj) xs (IntSet.empty, []) in
    let radj = generate_radj adj in
    let (_, sccs) = List.fold_left (f radj) (IntSet.empty, []) sorted in
    sccs

(* map : x -> scc id, rmap : scc id -> xs *)
let encode_sccs = fun sccs ->
    let f = fun (id, map, rmap) scc ->
        let g = fun id x (map, rmap) ->
            let map = IntMap.add x id map in
            let xs = IntMap.find_default IntSet.empty id rmap in
            let xs = IntSet.add x xs in
            let rmap = IntMap.add id xs rmap in
            (map, rmap)
        in
        let (map, rmap) = IntSet.fold (g id) scc (map, rmap) in
        (id + 1, map, rmap)
    in
    let seed = (0, IntMap.empty, IntMap.empty) in
    let (_, map, rmap) = List.fold_left f seed sccs in
    (map, rmap)

(* topgraph: DAG consisting of sccs *)
let construct_topgraph = fun adj sccs ->
    let f = fun adj map (vs, es) scc ->
        let g = fun adj map x (vs, es) ->
            let h = fun map y acc ->
                let y = IntMap.find y map in
                IntSet.add y acc
            in
            let ys = IntMap.find x adj in
            let x = IntMap.find x map in
            let zs = IntMap.find_default IntSet.empty x es in
            let zs = IntSet.fold (h map) ys zs in
            let vs = IntSet.add x vs in
            let es = IntMap.add x zs es in
            (vs, es)
        in
        IntSet.fold (g adj map) scc (vs, es)
    in
    let (map, rmap) = encode_sccs sccs in
    let seed = (IntSet.empty, IntMap.empty) in
    let (vs, es) = List.fold_left (f adj map) seed sccs in
    (vs, es, rmap)

(* scc + topological sort on topgraph *)
let topsort_sccs = fun xs adj ->
    let f = fun rmap acc id ->
        let scc = IntMap.find id rmap in
        scc :: acc
    in
    let sccs = scc_decomposition xs adj in
    let (xs, adj, rmap) = construct_topgraph adj sccs in
    let (_, sorted) = IntSet.fold (dfs_aux adj) xs (IntSet.empty, []) in
    List.rev (List.fold_left (f rmap) [] sorted)

module Queue = struct

    module EltSet = Set.Make (struct
        type t = element
        let compare : t -> t -> int = compare
    end)
    module EltMap = X.Map.Make (struct
       type t = element
       let compare : t -> t -> int = compare
    end)

    let counter = ref 0
    let vs = ref IntSet.empty
    let adj = ref IntMap.empty
    let encoder = ref EltMap.empty
    let decoder = ref IntMap.empty
    let weights = ref IntMap.empty
    let priorities = ref IntMap.empty

    module Pool = Set.Make (struct
        type t = int
        let compare : t -> t -> int = fun x y ->
            let px = IntMap.find x !priorities in
            let py = IntMap.find y !priorities in
            let cp = compare px py in
            if cp = 0 then (* compare x y *)
                let wx = IntMap.find x !weights in
                let wy = IntMap.find y !weights in
                let cw = compare wx wy in
                if cw = 0 then compare x y
                else cw
            else cp
    end)
    type elt = int
    type t = Pool.t

    let add_element = fun elt ->
        encoder := EltMap.add elt !counter !encoder;
        decoder := IntMap.add !counter elt !decoder;
        vs := IntSet.add !counter !vs;
        adj := IntMap.add !counter IntSet.empty !adj;
        (* weights := IntMap.add !counter !counter !weights; *)
        counter := !counter + 1

    let add_funcs = fun funcs ->
        let f = fun func ->
            let (_, x, _, _, _) = func in
            let x = Function (x) in
            add_element x
        in
        List.iter f funcs

    let add_formulas = fun flow_info ->
        let f = fun ys xs ->
            let ys = Formulas (ys) in
            add_element ys
        in
        let rev_flows = Flow.get_rev_flows flow_info in
        FmlsMap.iter f rev_flows

    let add_dep_x_element = fun x elt ->
        let y = EltMap.find elt !encoder in
        let ys = IntMap.find x !adj in
        let ys = IntSet.add y ys in
        adj := IntMap.add x ys !adj

    let add_dep_x_func = fun x y ->
        let y = Function (y) in
        add_dep_x_element x y

    let add_dep_x_formulas = fun x zs ->
        let zs = Formulas (zs) in
        add_dep_x_element x zs

    let add_dep_func = fun flow_info func ->
        let (_, x, _, _, _) = func in
        let (ys, zss) = Flow.get_dep_lhs x flow_info in
        let x = Function (x) in
        let x = EltMap.find x !encoder in
        IdSet.iter (add_dep_x_func x) ys;
        FmlsSet.iter (add_dep_x_formulas x) zss

    let add_dep_funcs = fun funcs flow_info ->
        List.iter (add_dep_func flow_info) funcs

    let add_dep_x_var = fun flow_info x var ->
        let (ys, zss) = Flow.get_dep_rhs var flow_info in
        IdSet.iter (add_dep_x_func x) ys;
        FmlsSet.iter (add_dep_x_formulas x) zss

    let add_dep_formulas = fun flow_info ->
        let f = fun ys xs ->
            let ys = Formulas (ys) in
            let ys = EltMap.find ys !encoder in
            IdSet.iter (add_dep_x_var flow_info ys) xs
        in
        let rev_flows = Flow.get_rev_flows flow_info in
        FmlsMap.iter f rev_flows

    let add_priorities = fun sccs ->
        let rec f = fun p sccs ->
            let g = fun p x ->
                priorities := IntMap.add x p !priorities
            in
            match sccs with
            | [] -> ()
            | scc :: sccs ->
                IntSet.iter (g p) scc;
                f (p + 1) sccs
        in
        f 0 sccs

    let print_sccs = fun sccs ->
        let f = fun scc ->
            let g = fun x acc ->
                match IntMap.find x !decoder with
                | Function (x) -> Id.to_string x :: acc
                | Formulas (ys) ->
                    let ls = List.rev_map HFS.string_of_formula ys in
                    ("[" ^ (String.concat "; " (List.rev ls)) ^ "]") :: acc
            in
            let ls = IntSet.fold g scc [] in
            let str = "{" ^ (String.concat ", " (List.rev ls)) ^ "}" in
            print_endline str
        in
        print_endline "%DEP_SCCS";
        List.iter f sccs

    let push = let cnt = ref 0 in (* for weights *) fun x queue ->
        let queue =
            if IntMap.mem x !weights && Pool.mem x queue then
                Pool.remove x queue
            else queue
        in
        weights := IntMap.add x !cnt !weights;
        cnt := !cnt + 1;
        Pool.add x queue

    let initial_pool = fun xs ->
        let f = fun x acc -> push x acc in
        IntSet.fold f xs Pool.empty

    let init = fun funcs flow_info ->
        add_funcs funcs;
        add_formulas flow_info;
        add_dep_funcs funcs flow_info;
        add_dep_formulas flow_info;
        let sccs = topsort_sccs !vs !adj in
        (* Log.exec 2 (fun () -> print_sccs sccs); *)
        add_priorities sccs;
        initial_pool !vs

    let is_empty = Pool.is_empty

    let push_deps_element = fun elt queue ->
        let x = EltMap.find elt !encoder in
        let deps = IntMap.find x !adj in
        IntSet.fold push deps queue

    let push_deps_func = fun x queue ->
        let x = Function (x) in
        push_deps_element x queue

    let push_deps_formulas = fun ys queue ->
        let ys = Formulas (ys) in
        push_deps_element ys queue

    let min_elt = Pool.min_elt

    let remove = Pool.remove

    let decode = fun elt -> IntMap.find elt !decoder

end
