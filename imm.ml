(* optimization for immediate winning positions *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module BVs = Id.IdSet
module States = LTS.States
module Delta = LTS.Delta
module ToProps = Id.IdSet
module Tau = Types.Tau
module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta
module Epsilon = Types.Epsilon

(* remove _ |- tau from epsilon if x : tau is a winning node *)
let remove_imms_rhs = fun x winning_nodes epsilon ->
    let f = fun tau (new_imms, epsilon) ->
        if Epsilon.mem tau epsilon then
            let new_imms = Sigma.add tau new_imms in
            let epsilon = Epsilon.remove tau epsilon in
            (new_imms, epsilon)
        else (new_imms, epsilon)
    in
    let sigma = LHS.find_default Sigma.empty x winning_nodes in
    let seed = (Sigma.empty, epsilon) in
    Sigma.fold f sigma seed

(* for each x : sigma \in gamma, subtract winning nodes of x from sigma *)
let remove_imms_gamma = fun winning_nodes gamma ->
    let f = fun winning_nodes x sigma gamma ->
        if LHS.mem x winning_nodes then
            let to_sub = LHS.find x winning_nodes in
            let sigma = Sigma.diff sigma to_sub in
            if Sigma.is_empty sigma then (* x can be removed *)
                Gamma.remove x gamma
            else Gamma.add x sigma gamma
        else gamma
    in
    Gamma.fold (f winning_nodes) gamma gamma

(* for each theta |- tau in epsilon, apply remove_imms_gamma to theta *)
let remove_imms_lhs = fun winning_nodes epsilon ->
    let f = fun winning_nodes tau theta (new_imms, epsilon) ->
        let theta = Theta.map (remove_imms_gamma winning_nodes) theta in
        if Theta.mem Gamma.empty theta then (* \emptyset |- tau *)
            let new_imms = Sigma.add tau new_imms in
            let epsilon = Epsilon.remove tau epsilon in
            (new_imms, epsilon)
         else (new_imms, Epsilon.add tau theta epsilon)
    in
    let seed = (Sigma.empty, epsilon) in
    Epsilon.fold (f winning_nodes) epsilon seed

(* remove winning nodes from the both sides of epsilon *)
let remove_winning_nodes_epsilon = fun x winning_nodes epsilon ->
    let (old_imms, epsilon) = remove_imms_rhs x winning_nodes epsilon in
    let (new_imms, epsilon) = remove_imms_lhs winning_nodes epsilon in
    (new_imms, epsilon)

(* remove _ |- x : tau from tj if x : tau is a winning node *)
let remove_winning_nodes_rhs = fun winning_nodes tj ->
    let f = fun x sigma tj ->
        if LHS.mem x tj then
            let epsilon = LHS.find x tj in
            let epsilon = Sigma.fold Epsilon.remove sigma epsilon in
            if Epsilon.is_empty epsilon then LHS.remove x tj
            else LHS.add x epsilon tj
        else tj
    in
    LHS.fold f winning_nodes tj

let merge_winning_nodes = fun winning_nodes1 winning_nodes2 ->
    let f = fun x sigma1 sigma2 -> Some (Sigma.union sigma1 sigma2) in
    LHS.union f winning_nodes1 winning_nodes2

let imms_to_winning_nodes = fun x imms ->
    if Sigma.is_empty imms then LHS.empty
    else LHS.singleton x imms

let rec loop = (* new_winning_nodes is unprocessed *)
    fun x epsilon imms winning_nodes tj new_winning_nodes ->
    if LHS.is_empty new_winning_nodes then
        (epsilon, imms, winning_nodes, tj)
    else
        let (new_imms, epsilon) =
            remove_winning_nodes_epsilon x new_winning_nodes epsilon
        in
        let tj = remove_winning_nodes_rhs new_winning_nodes tj in
        let imms = Sigma.union imms new_imms in
        let winning_nodes =
            merge_winning_nodes winning_nodes new_winning_nodes
        in
        let new_winning_nodes = imms_to_winning_nodes x new_imms in
        loop x epsilon imms winning_nodes tj new_winning_nodes

let add_imms_to_epsilon = fun imms epsilon ->
    let f = fun tau epsilon ->
        let theta = Theta.singleton Gamma.empty in
        Epsilon.add tau theta epsilon
    in
    Sigma.fold f imms epsilon

let optimize = fun x epsilon winning_nodes tj ->
    if !Flags.noopt_mode then (epsilon, winning_nodes, tj) else
    let (old_imms, epsilon) = remove_imms_rhs x winning_nodes epsilon in
    let (new_imms, epsilon) = remove_imms_lhs winning_nodes epsilon in
    let new_winning_nodes = imms_to_winning_nodes x new_imms in
    let (epsilon, new_imms, winning_nodes, tj) =
        loop x epsilon new_imms winning_nodes tj new_winning_nodes
    in
    let imms = Sigma.union old_imms new_imms in
    let epsilon = add_imms_to_epsilon imms epsilon in
    (epsilon, winning_nodes, tj)
