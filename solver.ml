(* simple parity game solver *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module Tau = Types.Tau
module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta
module Epsilon = Types.Epsilon
module VS = Graph.VS
module Adj = Graph.Adj

(* { w | (v, w) \in radj, v \in vs } *)
let initial_candids = fun radj vs ->
    let f = fun radj v acc ->
        let ws = Adj.find_default VS.empty v radj in
        VS.union ws acc
    in
    VS.fold (f radj) vs VS.empty

(* generic function for attractor *)
let rec attr_base = fun func adj radj removed acc vs ->
    let f = fun func adj radj removed candid new_vs ->
        let wss = Adj.find_default [] candid adj in
        if func removed wss then
            VS.add candid new_vs
        else new_vs
    in
    let acc = VS.union vs acc in
    let removed = VS.union vs removed in
    let candids = initial_candids radj vs in
    let candids = VS.diff candids removed in
    let new_vs = VS.fold (f func adj radj removed) candids VS.empty in
    if VS.is_empty new_vs then acc
    else attr_base func adj radj removed acc new_vs

let attractable_nu = fun removed wss ->
    let supset = fun vs1 vs2 ->
        VS.subset vs2 vs1
    in
    List.exists (supset removed) wss

let attractable_mu = fun removed wss ->
    let intersects = fun vs1 vs2 ->
        not (VS.is_empty (VS.inter vs1 vs2))
    in
    List.for_all (intersects removed) wss

let attr_nu = fun adj radj removed vs ->
   attr_base attractable_nu adj radj removed VS.empty vs

let attr_mu = fun adj radj removed vs ->
   attr_base attractable_mu adj radj removed VS.empty vs

let attr = fun adj radj removed i us ->
    let vs = VS.diff us removed in
    if i mod 2 = 0 then attr_nu adj radj removed vs
    else attr_mu adj radj removed vs

(* generic function for generate *)
let generate_base = fun func adj ->
    let f = fun func v wss acc ->
        if func wss then VS.add v acc
        else acc
    in
    Adj.fold (f func) adj VS.empty

let generate_dead_ends = fun adj ->
    let is_empty = fun wss -> wss = [] in
    generate_base is_empty adj

let generate_live_ends = fun adj ->
    let contains_empty = fun wss -> List.exists VS.is_empty wss in
    generate_base contains_empty adj

(* generic function for remove *)
let remove_base = fun func adj radj vs ->
    let f = fun func vs candid acc ->
        let wss = Adj.find_default [] candid acc in
        let wss = func vs wss in
        Adj.add candid wss acc
    in
    let adj = VS.fold Adj.remove vs adj in
    let candids = initial_candids radj vs in
    let candids = VS.diff candids vs in
    VS.fold (f func vs) candids adj

let remove_dead_ends = fun adj radj vs ->
    let remove_if_intersects = fun vs wss ->
        let f = fun vs acc ws ->
            if VS.is_empty (VS.inter vs ws) then
                ws :: acc
            else acc
        in
        List.fold_left (f vs) [] wss
    in
    remove_base remove_if_intersects adj radj vs

let remove_live_ends = fun adj radj vs ->
    let take_diff = fun vs wss ->
        let f = fun vs ws -> VS.diff ws vs in
        List.rev_map (f vs) wss
    in
    remove_base take_diff adj radj vs

(* generic function for shrink *)
let shrink_base = fun generate attr remove graph ->
    let (adj, v0) = graph in
    let radj = Graph.generate_radj adj in
    let vs = generate adj in
    let vs = attr adj radj VS.empty vs in
    let adj = remove adj radj vs in
    (adj, v0)

let shrink_mu = fun graph ->
    shrink_base generate_dead_ends attr_mu remove_dead_ends graph

let shrink_nu = fun graph ->
    shrink_base generate_live_ends attr_nu remove_live_ends graph

(* Zielonka's algorithm *)
(* return winning nodes for the current player to the left *)
let rec zielonka = fun adj radj partition removed ->
    match partition with
    | [] -> (VS.empty, VS.empty)
    | (i, us) :: partition' when partition' = [] ->
        (VS.diff us removed, VS.empty)
    | (i, us) :: partition' when VS.subset us removed ->
        let (ls, ws) = zielonka adj radj partition' removed in
        (ws, ls)
    | (i, us) :: partition' ->
        let us = attr adj radj removed i us in
        let removed' = VS.union us removed in
        let (ls, ws) = zielonka adj radj partition' removed' in
        if VS.is_empty ls then (VS.union us ws, VS.empty)
        else
            let us = attr adj radj removed (i + 1) ls in
            let removed = VS.union us removed in
            let (ws, ls) = zielonka adj radj partition removed in
            (ws, VS.union us ls)

(* entrance for Zielonka's algorithm *)
let zielonka = fun funcs graph ->
    let (adj, v0) = graph in
    let radj = Graph.generate_radj adj in
    let priorities = Preproc.generate_priorities funcs in
    let partition = Graph.generate_partition priorities adj in
    let (win, _) = zielonka adj radj partition VS.empty in
    VS.mem v0 win

let solve = fun funcs lts tj ->
    let graph = Graph.construct funcs lts tj in
    let graph = shrink_mu graph in
    if Graph.contains_v0 graph then
        let graph = shrink_nu graph in
        if Graph.contains_v0 graph then
            zielonka funcs graph
        else true
    else false
