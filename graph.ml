(* basic graph algorithms for parity game solving *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module Tau = Types.Tau
module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta
module Epsilon = Types.Epsilon

(* can be replaced with an array or a hash table *)
module IntMap = X.Map.Make (struct
    type t = int
    let compare : t -> t -> int = compare
end)
module Vertex = struct
    type t = Id.t * Tau.t
    let compare : t -> t -> int =
        fun (x1, i1) (x2, i2) ->
        let cx = compare x1 x2 in
        if cx = 0 then compare i1 i2
        else cx
    let to_string = fun (x, i) ->
        let sx = Id.to_string x in
        let st = Types.string_of_tau i in
        sx ^ " : " ^ st
end
module VS = Set.Make (Vertex)
module Adj = X.Map.Make (Vertex)

type t = VS.t list Adj.t * Vertex.t

let string_of_vs = fun vs ->
    let f = fun v acc -> Vertex.to_string v :: acc in
    let ls = VS.fold f vs [] in
    "[" ^ (String.concat "; " (List.rev ls)) ^ "]"

let string_of_vss = fun vss ->
    let ls = X.List.map string_of_vs vss in
    "[" ^ (String.concat "; " ls) ^ "]"

let print = fun graph ->
    let f = fun v vss ->
        let sv = Vertex.to_string v in
        let svss = string_of_vss vss in
        print_endline (sv ^ " => " ^ svss)
    in
    let (adj, v0) = graph in
    let card = Adj.cardinal adj in
    let sc = string_of_int card in
    print_endline ("cardinal: " ^ sc);
    let sv0 = Vertex.to_string v0 in
    print_endline ("initial vertex: " ^ sv0);
    Adj.iter f adj

let gamma_to_vs = fun gamma ->
    let f = fun x sigma acc ->
        let g = fun x tau acc -> VS.add (x, tau) acc in
        Sigma.fold (g x) sigma acc
    in
    Gamma.fold f gamma VS.empty

let theta_to_vss = fun theta ->
    let f = fun gamma acc ->
        let vs = gamma_to_vs gamma in
        vs :: acc
    in
    Theta.fold f theta []

let vss_to_vs = fun vss ->
    let vs = List.fold_left VS.union VS.empty vss in
    VS.elements vs

(* add vertices reachable from (x, tau) *)
let rec add_vertex = fun tj adj (x, tau) ->
    if Adj.mem (x, tau) adj then adj
    else
        let epsilon = LHS.find_default Epsilon.empty x tj in
        let theta = Epsilon.find_default Theta.empty tau epsilon in
        let vss = theta_to_vss theta in
        let adj = Adj.add (x, tau) vss adj in
        let vs = vss_to_vs vss in
        List.fold_left (add_vertex tj) adj vs

let initial_vertex = fun funcs lts ->
    let (_, x, _, _, _) = List.hd funcs in
    let (_, _, _, q0) = lts in
    let tau = Tau.encode ([], q0) in
    (x, tau)

let construct = fun funcs lts tj ->
    let v0 = initial_vertex funcs lts in
    let adj = add_vertex tj Adj.empty v0 in
    (adj, v0)

(* include vertices unreachable from the initial vertex *)
let construct_all = fun funcs lts tj ->
    let f = fun x epsilon adj ->
        let g = fun x tau theta adj ->
            let vss = theta_to_vss theta in
            Adj.add (x, tau) vss adj
        in
        Epsilon.fold (g x) epsilon adj
    in
    let v0 = initial_vertex funcs lts in
    let adj = LHS.fold f tj Adj.empty in
    (adj, v0)

let generate_radj = fun adj ->
    let f = fun v wss acc ->
        let g = fun v acc w ->
            let vs = Adj.find_default VS.empty w acc in
            let vs = VS.add v vs in
            Adj.add w vs acc
        in
        let ws = vss_to_vs wss in
        List.fold_left (g v) acc ws
    in
    Adj.fold f adj Adj.empty

(* make the maximum priority even, and *)
(* fill the list so that for each step the priority decreases by one *)
(* at first the partiion is increasingly ordered and not filled *)
let fill_partition = fun partition ->
    let rec fill = fun i partition acc ->
        match partition with
        | [] -> acc
        | (j, us) :: partition' ->
            if i = j then
                let acc = (j, us) :: acc in
                fill (i + 1) partition' acc
            else
                let acc = (i, VS.empty) :: acc in
                fill (i + 1) partition acc
    in
    let partition = fill 0 partition [] in
    let max_priority = List.length partition - 1 in
    if max_priority mod 2 = 0 then partition
    else (max_priority + 1, VS.empty) :: partition

(* make a partition of vertices according to their priorities *)
(* they are ordered so that the head has an even priority, and *)
(* the successor always has the priority of its predecessor minus one *)
let generate_partition = fun priorities adj ->
    let f = fun priorities (x, tau) vss acc ->
        let i = LHS.find_default 0 x priorities in
        let vs = IntMap.find_default VS.empty i acc in
        let vs = VS.add (x, tau) vs in
        IntMap.add i vs acc
    in
    let map = Adj.fold (f priorities) adj IntMap.empty in
    let partition = IntMap.bindings map in (* increasing and not filled *)
    fill_partition partition

(* check if the graph contains the initial vertex *)
let contains_v0 = fun graph ->
    let (adj, v0) = graph in
    Adj.mem v0 adj
