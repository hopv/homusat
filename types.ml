(* intersection types *)

module States = LTS.States

module Sigma = Set.Make (struct
    type t = int
    let compare : t -> t -> int = compare
end)

module Tau = struct

    type t = int
    type raw = Sigma.t list * LTS.state
    (* int list * LTS.state can be used as an intermediate type *)

    module IntMap = X.Map.Make (struct
        type t = int
        let compare : t -> t -> int = compare
    end)
    module StateMap = X.Map.Make (struct
        type t = LTS.state
        let compare : t -> t -> int = compare
    end)
    module SigmaMap = X.Map.Make (Sigma)
    module SigmasMap = X.Map.Make (struct
        type t = Sigma.t list
        let compare : t -> t -> int =
            fun sigmas1 sigmas2 ->
            let rec cmp = fun sigmas1 sigmas2 ->
                match (sigmas1, sigmas2) with
                | ([], []) -> 0
                | (sigma1 :: sigmas1, sigma2 :: sigmas2) ->
                    let cs = Sigma.compare sigma1 sigma2 in
                    if cs = 0 then cmp sigmas1 sigmas2
                    else cs
                | _ -> assert false
            in
            let l1 = List.length sigmas1 in
            let l2 = List.length sigmas2 in
            let cl = compare l1 l2 in
            if cl = 0 then cmp sigmas1 sigmas2
            else cl
    end)

    let counter = ref 0
    let prop_thres = ref 0
    let map = ref StateMap.empty
    let rmap = ref IntMap.empty

    let register_states = fun lts ->
        let rec register_state = fun q ->
            let qmap = StateMap.find_default SigmasMap.empty q !map in
            let qmap = SigmasMap.add [] q qmap in
            map := StateMap.add q qmap !map;
            rmap := IntMap.add q ([], q) !rmap;
            counter := !counter + 1
        in
        let (qs, _, _, _) = lts in
        assert (!counter = 0);
        States.iter register_state qs;
        prop_thres := !counter

    let is_prop = fun i -> i < !prop_thres

    let decode = fun i ->
        if is_prop i then ([], i)
        else IntMap.find i !rmap

    (* subtype relation *)
    let rec subtype =
        let memo = Hashtbl.create 100000 in
        fun x y ->
            if x = y then true
            else if Hashtbl.mem memo (x, y) then
                Hashtbl.find memo (x, y)
            else if Hashtbl.mem memo (y, x) then
                let ret =
                    if Hashtbl.find memo (y, x) then false
                    else subtype_decode x y
                in
                Hashtbl.add memo (x, y) ret;
                ret
            else
                let ret = subtype_decode x y in
                Hashtbl.add memo (x, y) ret;
                ret
    and suptype = fun sigma1 sigma2 ->
        let f = fun sigma2 tau1 ->
            let g = fun tau1 tau2 -> subtype tau2 tau1 in
            Sigma.exists (g tau1) sigma2
        in
        Sigma.for_all (f sigma2) sigma1
    and subtype_decode = fun x y ->
        let rem_inters = fun sigmas1 sigmas2 ->
            let f = fun (sigmas1, sigmas2) sigma1 sigma2 ->
                let sigma3 = Sigma.inter sigma1 sigma2 in
                let sigma1 = Sigma.diff sigma1 sigma3 in
                let sigma2 = Sigma.diff sigma2 sigma3 in
                (sigma1 :: sigmas1, sigma2 :: sigmas2)
            in
            List.fold_left2 f ([], []) sigmas1 sigmas2
        in
        let (sigmas1, q1) = decode x in
        let (sigmas2, q2) = decode y in
        if q1 = q2 then
            let (sigmas1, sigmas2) = rem_inters sigmas1 sigmas2 in
            List.for_all2 suptype sigmas1 sigmas2
        else false

    let normalize_sigma = fun sigma ->
        let strict_suptype = fun i j -> i <> j && subtype j i in
        let f = fun i acc ->
            if Sigma.exists (strict_suptype i) acc then
                Sigma.remove i acc
            else acc
        in
        Sigma.fold f sigma sigma

    let normalize_sigmas = fun sigmas ->
        List.rev (List.rev_map normalize_sigma sigmas)

    (* encode tau to int after normalization *)
    let encode = fun tau ->
        let (sigmas, q) = tau in
        if sigmas = [] then q
        else
            let qmap = StateMap.find_default SigmasMap.empty q !map in
            if SigmasMap.mem sigmas qmap then
                SigmasMap.find sigmas qmap
            else
                let normalized = if !Flags.noopt_mode then sigmas
                                 else normalize_sigmas sigmas in
                if SigmasMap.mem normalized qmap then
                    let ret = SigmasMap.find normalized qmap in
                    let qmap = SigmasMap.add sigmas ret qmap in
                    map := StateMap.add q qmap !map;
                    ret
                else
                    let ret = !counter in
                    let qmap = SigmasMap.add sigmas ret qmap in
                    let qmap = SigmasMap.add normalized ret qmap in
                    map := StateMap.add q qmap !map;
                    rmap := IntMap.add ret (normalized, q) !rmap;
                    counter := !counter + 1;
                    ret

end

module Gamma = Id.IdMap
module Theta = Set.Make (struct
    type t = Sigma.t Gamma.t
    let compare = Gamma.compare Sigma.compare
end)
module Epsilon = X.Map.Make (struct
    type t = Tau.t
    let compare : t -> t -> int = compare
end)

let is_prop = Tau.is_prop
let register_states = Tau.register_states

(* get the return type of tau when n arguments are applied *)
let drop = (* this function is called repeatedly and should be fast *)
    let memo = Hashtbl.create 1000000 in
    let rec drop = fun i sigmas ->
        if i <= 0 then sigmas
        else match sigmas with
        | sigma :: sigmas -> drop (i - 1) sigmas
        | [] -> assert false
    in
    fun i n ->
    if n = 0 then i
    else if Hashtbl.mem memo (i, n) then
        Hashtbl.find memo (i, n)
    else
        let ret =
            let (sigmas, q) = Tau.decode i in
            let sigmas = drop n sigmas in
            Tau.encode (sigmas, q) (* normalization can be skipped *)
        in
        Hashtbl.add memo (i, n) ret;
        ret

(* final type of tau *)
let codom = fun i ->
    if is_prop i then i
    else let (_, q) = Tau.decode i in q

(* attach a set of intersection types to each argument *)
let annot = fun args i ->
    let rec annot = fun args sigmas acc ->
        match (args, sigmas) with
        | ([], _) -> acc (* List.rev acc *)
        | (arg :: args, sigma :: sigmas) ->
            let acc = (arg, sigma) :: acc in
            annot args sigmas acc
        | (_, []) -> assert false
    in
    if args = [] then []
    else
        let (sigmas, q) = Tau.decode i in
        annot args sigmas []

(* T -> ... -> T -> q *)
let strongest_type = fun sort q ->
    let rec ts = fun sort acc ->
        match sort with
        | HFS.Prop -> acc
        | HFS.Arrow (_, sort) ->
            let acc = Sigma.empty :: acc in
            ts sort acc
    in
    let sigmas = ts sort [] in
    let tau = (sigmas, q) in
    Tau.encode tau

let rec string_of_tau = fun i ->
    let string_of_sigma_aux = fun sigma ->
        let string_of_tau_aux = fun i ->
            let str = string_of_tau i in
            if is_prop i then str
            else "(" ^ str ^ ")"
        in
        let elems = Sigma.elements sigma in
        match elems with
        | [] -> "T"
        | [i] -> string_of_tau_aux i
        | _ ->
            let ls = List.rev_map string_of_tau elems in
            "{" ^ (String.concat ", " (List.rev ls)) ^ "}"
    in
    let (sigmas, q) = Tau.decode i in
    let sq = LTS.string_of_state q in
    if sigmas = [] then sq
    else
        let ls = List.rev_map string_of_sigma_aux sigmas in
        (String.concat " -> " (List.rev ls)) ^ " -> " ^ sq

let string_of_sigma = fun sigma ->
    let elems = Sigma.elements sigma in
    let ls = List.rev_map string_of_tau elems in
    "{" ^ (String.concat ", " (List.rev ls)) ^ "}"

let string_of_gamma = fun gamma ->
    let f = fun x sigma acc ->
        let g = fun sx tau acc ->
            let st = string_of_tau tau in
            let str = sx ^ " : " ^ st in
            str :: acc
        in
        let sx = Id.to_string x in
        Sigma.fold (g sx) sigma acc
    in
    let ls = Gamma.fold f gamma [] in
    String.concat ", " (List.rev ls)

let merge_gammas = fun gamma1 gamma2 ->
    let f = fun x sigma1 sigma2 ->
        Some (Sigma.union sigma1 sigma2)
    in
    Gamma.union f gamma1 gamma2

(* take Cartesian product of thetas *)
let prod_thetas = fun theta1 theta2 ->
    let add_merged = fun gamma1 gamma2 acc ->
        Profile.check_time_out "model checking" !Flags.time_out;
        let gamma = merge_gammas gamma1 gamma2 in
        Theta.add gamma acc
    in
    let f = fun theta gamma acc ->
        Theta.fold (add_merged gamma) theta acc
    in
    Theta.fold (f theta1) theta2 Theta.empty

(* normalization making use of subtyping relation (slow) *)
let merge_sigmas_with_subtype = fun sigma1 sigma2 ->
    let suptype = fun tau1 tau2 -> Tau.subtype tau2 tau1 in
    let not_subtype = fun tau1 tau2 -> not (Tau.subtype tau1 tau2) in
    let f = fun tau acc ->
        if Sigma.exists (suptype tau) acc then acc
        else Sigma.add tau (Sigma.filter (not_subtype tau) acc)
    in
    let sigma = Sigma.union sigma1 sigma2 in (* all elements are distinct *)
    Sigma.fold f sigma Sigma.empty

(* normalization making use of subtyping relation (slow) *)
let merge_gammas_with_subtype = fun gamma1 gamma2 ->
    let f = fun x sigma1 sigma2 ->
        Some (merge_sigmas_with_subtype sigma1 sigma2)
    in
    Gamma.union f gamma1 gamma2

(* normalization making use of subtyping relation (slow) *)
let prod_thetas_with_subtype = fun theta1 theta2 ->
    let add_merged = fun gamma1 gamma2 acc ->
        let gamma = merge_gammas_with_subtype gamma1 gamma2 in
        Theta.add gamma acc
    in
    let f = fun theta gamma acc ->
        Theta.fold (add_merged gamma) theta acc
    in
    Theta.fold (f theta1) theta2 Theta.empty

(* check if gamma1 is (as a set of type bindings) a superset of gamma2 *)
let weak_subenv = fun gamma1 gamma2 ->
    let f = fun gamma1 x sigma2 ->
        let sigma1 = Gamma.find_default Sigma.empty x gamma1 in
        Sigma.subset sigma2 sigma1
    in
    Gamma.for_all (f gamma1) gamma2

let merge_epsilons = fun epsilon1 epsilon2 ->
    let f = fun tau theta1 theta2 ->
        Some (Theta.union theta1 theta2)
    in
    Epsilon.union f epsilon1 epsilon2

let normalize_gamma = fun gamma ->
    Gamma.map Tau.normalize_sigma gamma

let subtype = Tau.subtype
