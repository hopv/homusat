(* optimization through removal of unnecessary types *)

module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta

let normalize_sigma = fun sigma ->
    let suptype = fun tau1 tau2 -> Types.subtype tau2 tau1 in
    let not_subtype = fun tau1 tau2 -> not (Types.subtype tau1 tau2) in
    let f = fun tau acc ->
        if Sigma.exists (suptype tau) acc then acc
        else Sigma.add tau (Sigma.filter (not_subtype tau) acc)
    in
    Sigma.fold f sigma Sigma.empty

let normalize_gamma = fun gamma ->
    Gamma.map normalize_sigma gamma

module IntSet = Set.Make (struct
    type t = int
    let compare : t -> t -> int = compare
end)
module IntMap = X.Map.Make (struct
    type t = int
    let compare : t -> t -> int = compare
end)
module IntIntMap = X.Map.Make (struct
    type t = int * int
    let compare : t -> t -> int = compare
end)

(* Map.cardinal is slow *)
let counter = ref 0

(* convert sigma (the set of types for i-th argument) to int list *)
let sigma_to_is = fun i map rmap acc sigma ->
    let f = fun i tau (map, rmap, acc) ->
        if IntIntMap.mem (i, tau) map then
            let k = IntIntMap.find (i, tau) map in
            (map, rmap, k :: acc)
        else
            let k = !counter in
            let map = IntIntMap.add (i, tau) k map in
            let rmap = IntMap.add k (i, tau) rmap in
            counter := !counter + 1;
            (map, rmap, k :: acc)
    in
    Sigma.fold (f i) sigma (map, rmap, acc)

(* convert sigma list to int list *)
(* structure of sigmas is lost at this point (probably should be avoided) *)
let sigmas_to_is = fun map rmap sigmas ->
    let rec f = fun i map rmap sigmas acc ->
        match sigmas with
        | [] -> (map, rmap, acc)
        | sigma :: sigmas ->
            let (map, rmap, acc) = sigma_to_is i map rmap acc sigma in
            f (i + 1) map rmap sigmas acc
    in
    f 0 map rmap sigmas []

(* convert sigma list list to int list list *)
let sigmass_to_iss = fun sigmass ->
    let f = fun (map, rmap, acc) sigmas ->
        let (map, rmap, is) = sigmas_to_is map rmap sigmas in
        let is = List.sort compare is in (* necessary *)
        (map, rmap, is :: acc)
    in
    counter := 0;
    let map = IntIntMap.empty in
    let rmap = IntMap.empty in
    let (map, rmap, iss) = List.fold_left f (map, rmap, []) sigmass in
    (rmap, iss)

(* convert int list to a map from i to the set of types for i-th argument *)
let is_to_map = fun rmap is ->
    let f = fun rmap acc i ->
        let (j, tau) = IntMap.find i rmap in
        let sigma = IntMap.find_default Sigma.empty j acc in
        let sigma = Sigma.add tau sigma in
        IntMap.add j sigma acc
    in
    List.fold_left (f rmap) IntMap.empty is

(* concert map to sigma list *)
let map_to_sigmas = fun n map ->
    let rec f = fun i map acc ->
        if i < 0 then acc
        else
            let sigma = IntMap.find_default Sigma.empty i map in
            let acc = sigma :: acc in
            f (i - 1) map acc
    in
    f (n - 1) map []

(* convert int list to sigma list *)
let is_to_sigmas = fun n rmap is ->
    let map = is_to_map rmap is in
    map_to_sigmas n map

(* convert int list list to sigma list list *)
let iss_to_sigmass = fun n rmap iss ->
    List.rev_map (is_to_sigmas n rmap) iss

(* compare two sigma lists of the same length *)
let compare_sigmass = fun sigmas1 sigmas2 ->
    let rec compare_elementwise = fun sigmas1 sigmas2 ->
        match (sigmas1, sigmas2) with
        | ([], []) -> 0
        | (sigma1 :: sigmas1, sigma2 :: sigmas2) ->
           let cs = Sigma.compare sigma1 sigma2 in
           if cs = 0 then compare_elementwise sigmas1 sigmas2
           else cs
        | _ -> assert false
    in
    compare_elementwise sigmas1 sigmas2

(* this function often becomes a bottleneck of the whole process *)
let normalize_sigmass = fun sigmass ->
    if sigmass = [] then []
    else
        let n = List.length (List.hd sigmass) in
        let (rmap, iss) = sigmass_to_iss sigmass in
        let iss = AMS.all_maximal_sets iss in
        let sigmass = iss_to_sigmass n rmap iss in
        List.sort compare_sigmass sigmass (* sort the result *)

(* convert gamma to int list *)
let gamma_to_is = fun map rmap gamma ->
    let f = fun x sigma (map, rmap, acc) ->
        let g = fun x tau (map, rmap, acc) ->
            if IntIntMap.mem (x, tau) map then
                let k = IntIntMap.find (x, tau) map in
                (map, rmap, k :: acc)
            else
                let k = !counter in
                let map = IntIntMap.add (x, tau) k map in
                let rmap = IntMap.add k (x, tau) rmap in
                counter := !counter + 1;
                (map, rmap, k :: acc)
        in
        Sigma.fold (g x) sigma (map, rmap, acc)
    in
    Gamma.fold f gamma (map, rmap, [])

(* convert theta to int list list *)
let theta_to_iss = fun theta ->
    let f = fun gamma (map, rmap, acc) ->
        let (map, rmap, is) = gamma_to_is map rmap gamma in
        let is = List.sort compare is in (* necessary *)
        (map, rmap, is :: acc)
    in
    counter := 0;
    let map = IntIntMap.empty in
    let rmap = IntMap.empty in
    let (map, rmap, iss) = Theta.fold f theta (map, rmap, []) in
    (rmap, iss)

(* convert int list to gamma *)
let is_to_gamma = fun rmap is ->
    let f = fun rmap acc i ->
        let (x, tau) = IntMap.find i rmap in
        let sigma = Gamma.find_default Sigma.empty x acc in
        let sigma = Sigma.add tau sigma in
        Gamma.add x sigma acc
    in
    List.fold_left (f rmap) Gamma.empty is

(* convert int list list to theta *)
let iss_to_theta = fun rmap iss ->
    let f = fun rmap acc is ->
        let gamma = is_to_gamma rmap is in
        Theta.add gamma acc
    in
    List.fold_left (f rmap) Theta.empty iss

(* this function also can be a bottleneck of whole process *)
let normalize_theta = fun theta ->
    let theta = Theta.map normalize_gamma theta in
    let (rmap, iss) = theta_to_iss theta in
    iss_to_theta rmap (AMS.all_minimal_sets iss)

(* take Cartesian product of thetas with optimization *)
let prod_thetas = fun theta1 theta2 ->
    if !Flags.noopt_mode then Types.prod_thetas theta1 theta2 else
    if 1 < Theta.cardinal theta1 && 1 < Theta.cardinal theta2 then
        let theta = Types.prod_thetas theta1 theta2 in
        normalize_theta theta
    else Types.prod_thetas theta1 theta2

(* take maximal sets instead of minimal sets (unused) *)
let normalize_tes = fun tes ->
    let (rmap, iss) = theta_to_iss tes in
    let iss = AMS.all_maximal_sets iss in
    iss_to_theta rmap iss
