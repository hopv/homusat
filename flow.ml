(* Flow information *)

(* flows: X \mapsto { \phi | X <~ \phi } *)
(* rev_flows: \phi \mapsto { X | X <~ \phi } *)

(* fqmap: F \mapsto \bigcup { P | (F :: yss, P) is a node of ACG } *)
(* xqmap: X \mapsto \bigcup { P | (X :: yss, P) is a node of ACG } *)
(* aqmap: \phi mapsto \bigcup_{X <~ \phi} xqmap(X) *)
(* fbmap: F \mapsto [ (yss, P) | (F :: yss, P) is a node of ACG ] *)
(* ffmap: F \mapsto { G | G occurs in the body of F } *)
(* fvmap: F \mapsto { X | X occurs in the body of F } *)
(* abmap: \phi \mapsto [ yss | (par(\phi) :: yss, P) is a node of ACG ] *)
(* afmap: \phi \mapsto { F | F occurs in \phi } *)
(* avmap: \phi \mapsto { X | X occurs in \phi } *)
(* parent: \phi \mapsto F, where F is the parent of \phi *)
(* children: F \mapsto { X/G | X/G occurs in the body of F } *)
(* siblings: \phi \mapsto { X/G | X/G occurs in \phi } *)
(* llmap: F \mapsto { G | F occurs in the body of G } *)
(* lamap: F \mapsto { \phi | F occurs in \phi } *)
(* rlmap: X \mapsto F, where X is an argument of F *)
(* ramap: X \mapsto { \phi | X occurs in \phi } *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module IdSet = Id.IdSet
module IdMap = Id.IdMap
module States = LTS.States
module FmlSet = ACG.FmlSet
module FmlSet2 = ACG.FmlSet2
module FmlsSet = ACG.FmlsSet
module FmlMap = ACG.FmlMap
module FmlMap2 = ACG.FmlMap2
module FmlsMap = ACG.FmlsMap

type flows = FmlSet.t RHS.t
type rev_flows = IdSet.t FmlsMap.t
type fqmap = States.t LHS.t
type aqmap = States.t FmlMap.t
type fbmap = (Enc.elt list list * States.t) list LHS.t
type ffmap = IdSet.t LHS.t
type fvmap = IdSet.t LHS.t
type abmap = (Enc.elt list list) list FmlsMap.t
type afmap = IdSet.t FmlsMap.t
type avmap = IdSet.t FmlsMap.t
type parent = Id.t FmlsMap.t
type children = IdSet.t LHS.t
type siblings = IdSet.t FmlsMap.t
type llmap = IdSet.t LHS.t
type lamap = FmlsSet.t LHS.t
type rlmap = Id.t RHS.t
type ramap = FmlsSet.t RHS.t
type t = { flows : flows; rev_flows : rev_flows;
           fqmap : fqmap; aqmap : aqmap; fbmap : fbmap; abmap : abmap;
           parent : parent; children : children; siblings : siblings;
           llmap : llmap; lamap : lamap; rlmap : rlmap; ramap : ramap; }

(* Generate the set of lhs variables and the set of rhs variables *)
(* Might be better to define as a record type { lhs; rhs } *)
let generate_top_vars = fun funcs ->
    let f = fun (lhs, rhs) func ->
        let (_, x, _, args, _) = func in
        let lhs = IdSet.add x lhs in
        let g = fun rhs (y, t) -> IdSet.add y rhs in
        let rhs = List.fold_left g rhs args in
        (lhs, rhs)
    in
    List.fold_left f (IdSet.empty, IdSet.empty) funcs

(* Obtain the set of all variables occurring in a formula *)
let rec get_xs = fun xs fml ->
    match Enc.decode fml with
    | Enc.Or (ys)
    | Enc.And (ys) ->
        List.fold_left get_xs xs ys
    | Enc.Box (a, x)
    | Enc.Diamond (a, x) -> get_xs xs x
    | Enc.App (x, ys) ->
        let xs = IdSet.add x xs in
        List.fold_left get_xs xs ys

(* F/X \mapsto \bigcup { P | (F/X :: yss, P) is a node of ACG } *)
let generate_qmap = fun dom acg ->
    let f = fun dom fml qs acc ->
        match fml with
        | ACG.App (x, yss) when IdSet.mem x dom ->
            let ps = IdMap.find_default States.empty x acc in
            let ps = States.union ps qs in
            IdMap.add x ps acc
        | _ -> acc
    in
    let (nodes, _, _) = acg in
    FmlMap2.fold (f dom) nodes LHS.empty

(* fqmap: F \mapsto \bigcup { P | (F :: yss, P) is a node of ACG } *)
let generate_fqmap = fun top_vars acg ->
    let (lhs, _) = top_vars in generate_qmap lhs acg

(* xqmap: X \mapsto \bigcup { P | (X :: yss, P) is a node of ACG } *)
let generate_xqmap = fun top_vars acg ->
    let (_, rhs) = top_vars in generate_qmap rhs acg

(* aqmap: \phi mapsto \bigcup_{X <~ \phi} xqmap(X) *)
let generate_aqmap = fun top_vars acg ->
    let f = fun xqmap ys xss acc ->
        let g = fun xqmap ys acc xs ->
            let h = fun xqmap acc y x ->
                let ps = RHS.find_default States.empty x xqmap in
                let qs = FmlMap.find_default States.empty y acc in
                let qs = States.union ps qs in
                FmlMap.add y qs acc
            in
            List.fold_left2 (h xqmap) acc ys xs
        in
        List.fold_left (g xqmap ys) acc xss
    in
    let (_, _, rev_flows) = acg in
    let xqmap = generate_xqmap top_vars acg in
    FmlsMap.fold (f xqmap) rev_flows FmlMap.empty

(* fbmap: F \mapsto [ (yss, P) | (F :: yss, P) is a node of ACG ] *)
let generate_fbmap = fun top_vars acg ->
    let f = fun lhs fml qs acc ->
        match fml with
        | ACG.App (x, yss) when IdSet.mem x lhs ->
            let bindings = LHS.find_default [] x acc in
            let bindings = (yss, qs) :: bindings in
            LHS.add x bindings acc
        | _ -> acc
    in
    let (lhs, _) = top_vars in
    let (nodes, _, _) = acg in
    FmlMap2.fold (f lhs) nodes LHS.empty

(* F \mapsto { X/G | X/G occurs in the body of F } *)
let generate_fxmap = fun dom funcs ->
    let f = fun dom acc func ->
        let (_, x, _, _, body) = func in
        let xs = get_xs IdSet.empty body in
        let xs = IdSet.inter dom xs in
        LHS.add x xs acc
    in
    List.fold_left (f dom) LHS.empty funcs

(* ffmap: F \mapsto { G | G occurs in the body of F } *)
let generate_ffmap = fun top_vars funcs ->
    let (lhs, _) = top_vars in generate_fxmap lhs funcs

(* fvmap: F \mapsto { X | X occurs in the body of F } *)
let generate_fvmap = fun top_vars funcs ->
    let (_, rhs) = top_vars in generate_fxmap rhs funcs

(* Simplify ys -> xss to ys -> xs *)
let simplify_rev_flows = fun rev_flows ->
    let f = fun ys xss acc ->
        let g = fun acc xs ->
            let h = fun acc x -> IdSet.add x acc in
            List.fold_left h acc xs
        in
        let xs = List.fold_left g IdSet.empty xss in
        FmlsMap.add ys xs acc
    in
    FmlsMap.fold f rev_flows FmlsMap.empty

(* Exclude out unused formulas from rev_flows *)
let restrict_rev_flows = fun fvmap acg ->
    let f = fun x fvs acc -> IdSet.union fvs acc in
    let g = fun fvs ys zs acc ->
        let zs = IdSet.inter zs fvs in
        if IdSet.is_empty zs then acc (* Unused *)
        else FmlsMap.add ys zs acc
    in
    let (nodes, flows, rev_flows) = acg in
    let fvs = LHS.fold f fvmap IdSet.empty in
    let rev_flows = simplify_rev_flows rev_flows in
    let rev_flows = FmlsMap.fold (g fvs) rev_flows FmlsMap.empty in
    (nodes, flows, rev_flows)

(* The formula fml is a subformula of the body of par *)
let rec add_parent = fun par acc fml ->
    match Enc.decode fml with
    | Enc.Or (ys)
    | Enc.And (ys) ->
        List.fold_left (add_parent par) acc ys
    | Enc.Box (a, x)
    | Enc.Diamond (a, x) -> add_parent par acc x
    | Enc.App (x, ys) ->
        let acc = FmlsMap.add ys par acc in
        List.fold_left (add_parent par) acc ys

(* parent: \phi \mapsto F, where F is the parent of \phi *)
let generate_parent_unrestricted = fun funcs ->
    let f = fun acc func ->
        let (_, x, _, _, body) = func in
        add_parent x acc body
    in
    List.fold_left f FmlsMap.empty funcs

(* parent: \phi \mapsto F, where F is the parent of \phi *)
let generate_parent = fun acg funcs ->
    let f = fun ps ys zs acc ->
        let x = FmlsMap.find ys ps in
        FmlsMap.add ys x acc
    in
    let parent = generate_parent_unrestricted funcs in
    let (_, _, rev_flows) = acg in (* For restriction *)
    FmlsMap.fold (f parent) rev_flows FmlsMap.empty

(* children: F \mapsto { X/G | X/G occurs in the body of F } *)
let generate_children = fun funcs ->
    let f = fun acc func ->
        let (_, x, _, _, body) = func in
        let xs = get_xs IdSet.empty body in
        LHS.add x xs acc
    in
    List.fold_left f LHS.empty funcs

(* siblings: \phi \mapsto { X/G | X/G occurs in ys } *)
let generate_siblings = fun acg ->
    let f = fun ys zs acc ->
        let g = fun acc y -> get_xs acc y in
        let xs = List.fold_left g IdSet.empty ys in
        FmlsMap.add ys xs acc
    in
    let (_, _, rev_flows) = acg in
    FmlsMap.fold f rev_flows FmlsMap.empty

(* abmap: \phi \mapsto [ yss | (par(\phi) :: yss, qs) is a node of ACG } *)
let generate_abmap = fun top_vars acg fbmap parent ->
    let f = fun rhs fbmap parent ys zs acc ->
        let xs = List.fold_left get_xs IdSet.empty ys in
        let xs = IdSet.inter rhs xs in
        if IdSet.is_empty xs then (* Contains no rhs variable *)
            FmlsMap.add ys [] acc
        else
            let par = FmlsMap.find ys parent in
            let bindings = LHS.find_default [] par fbmap in
            let contexts = X.List.map fst bindings in
            FmlsMap.add ys contexts acc
    in
    let (_, rhs) = top_vars in
    let (_, _, rev_flows) = acg in
    FmlsMap.fold (f rhs fbmap parent) rev_flows FmlsMap.empty

(* \phi \mapsto { F/X | F/X occurs in \phi } *)
let generate_axmap = fun dom acg ->
    let f = fun dom ys zs acc ->
        let xs = List.fold_left get_xs IdSet.empty ys in
        let xs = IdSet.inter dom xs in
        FmlsMap.add ys xs acc
    in
    let (_, _, rev_flows) = acg in
    FmlsMap.fold (f dom) rev_flows FmlsMap.empty

(* afmap: \phi \mapsto { F | F occurs in \phi } *)
let generate_afmap = fun top_vars acg ->
    let (lhs, _) = top_vars in generate_axmap lhs acg

(* avmap: \phi \mapsto { X | X occurs in \phi } *)
let generate_avmap = fun top_vars acg ->
    let (rhs, _) = top_vars in generate_axmap rhs acg

(* llmap: F \mapsto { G | F occurs in the body of G } *)
let generate_llmap = fun top_vars funcs ->
    let f = fun lhs acc func ->
        let g = fun x y acc -> (* y occurs in the body of x *)
            let xs = LHS.find_default IdSet.empty y acc in
            let xs = IdSet.add x xs in
            LHS.add y xs acc
        in
        let (_, x, _, _, body) = func in
        let ys = get_xs IdSet.empty body in
        let ys = IdSet.inter lhs ys in
        IdSet.fold (g x) ys acc
    in
    let (lhs, _) = top_vars in
    List.fold_left (f lhs) LHS.empty funcs

(* rlmap: X \mapsto F, where X is an argument of F *)
let generate_rlmap = fun funcs ->
    let f = fun acc func ->
        let g = fun x acc (y, t) ->
            RHS.add y x acc
        in
        let (_, x, _, args, _) = func in
        List.fold_left (g x) acc args
    in
    List.fold_left f RHS.empty funcs

(* F/X \mapsto { \phi | F/X occurs in \phi } *)
let generate_xamap = fun dom acg ->
    let f = fun dom ys zs acc ->
        let g = fun ys x acc -> (* x occurs in ys *)
            let yss = IdMap.find_default FmlsSet.empty x acc in
            let yss = FmlsSet.add ys yss in
            IdMap.add x yss acc
        in
        let xs = List.fold_left get_xs IdSet.empty ys in
        let xs = IdSet.inter dom xs in
        IdSet.fold (g ys) xs acc
    in
    let (_, _, rev_flows) = acg in
    FmlsMap.fold (f dom) rev_flows IdMap.empty

(* lamap: F \mapsto { \phi | F occurs in \phi } *)
let generate_lamap = fun top_vars acg ->
    let (lhs, _) = top_vars in generate_xamap lhs acg

(* ramap: X \mapsto { \phi | X occurs in \phi } *)
let generate_ramap = fun top_vars acg ->
    let (_, rhs) = top_vars in generate_xamap rhs acg

let generate_flow_info = fun funcs lts ->
    let acg = ACG.construct funcs lts in
    let top_vars = generate_top_vars funcs in
    let fqmap = generate_fqmap top_vars acg in
    let aqmap = generate_aqmap top_vars acg in
    let fbmap = generate_fbmap top_vars acg in
    let fvmap = generate_fvmap top_vars funcs in
    let acg = restrict_rev_flows fvmap acg in
    let parent = generate_parent acg funcs in
    let children = generate_children funcs in
    let siblings = generate_siblings acg in
    let abmap = generate_abmap top_vars acg fbmap parent in
    let llmap = generate_llmap top_vars funcs in
    let lamap = generate_lamap top_vars acg in
    let rlmap = generate_rlmap funcs in
    let ramap = generate_ramap top_vars acg in
    let (_, flows, rev_flows) = acg in
    { flows : flows; rev_flows : rev_flows;
      fqmap : fqmap; aqmap : aqmap; fbmap : fbmap; abmap : abmap;
      parent : parent; children : children; siblings : siblings;
      llmap : llmap; lamap : lamap; rlmap : rlmap; ramap : ramap; }

let get_flows = fun flow_info -> flow_info.flows
let get_rev_flows = fun flow_info -> flow_info.rev_flows
let get_fqmap = fun flow_info -> flow_info.fqmap
let get_aqmap = fun flow_info -> flow_info.aqmap
let get_fbmap = fun flow_info -> flow_info.fbmap
let get_abmap = fun flow_info -> flow_info.abmap
let get_parent = fun flow_info -> flow_info.parent
let get_children = fun flow_info -> flow_info.children
let get_siblings = fun flow_info -> flow_info.siblings
let get_llmap = fun flow_info -> flow_info.llmap
let get_lamap = fun flow_info -> flow_info.lamap
let get_rlmap = fun flow_info -> flow_info.rlmap
let get_ramap = fun flow_info -> flow_info.ramap

(* Return binding list for the lhs variable x *)
let get_bindings = fun x flow_info ->
    let fbmap = get_fbmap flow_info in
    LHS.find_default [] x fbmap

(* Return binding list for the argument formula(s) ys *)
let get_contexts = fun ys flow_info ->
    let abmap = get_abmap flow_info in
    FmlsMap.find ys abmap

(* Return the parent of the formula(s) ys *)
let get_parent = fun ys flow_info ->
    let parent = get_parent flow_info in
    FmlsMap.find ys parent

(* Return the set of variables occurring in the body of x *)
let get_children = fun x flow_info ->
    let children = get_children flow_info in
    LHS.find x children

(* Return the set of variables occurring in the formula(s) ys *)
let get_siblings = fun ys flow_info ->
    let siblings = get_siblings flow_info in
    FmlsMap.find ys siblings

(* Destinations of the propagation from the lhs variable x *)
let get_dep_lhs = fun x flow_info ->
    let llmap = get_llmap flow_info in
    let lamap = get_lamap flow_info in
    let ys = LHS.find_default IdSet.empty x llmap in
    let zs = LHS.find_default FmlsSet.empty x lamap in
    (ys, zs)

(* Destinations of the propagation from the rhs variable x *)
let get_dep_rhs = fun x flow_info ->
    let rlmap = get_rlmap flow_info in
    let ramap = get_ramap flow_info in
    let y = RHS.find x rlmap in
    let zs = RHS.find_default FmlsSet.empty x ramap in
    (IdSet.singleton y, zs)

let string_of_formulas = fun xs ->
    let ls = X.List.map Enc.string_of_formula xs in
    "[" ^ (String.concat "; " ls) ^ "]"

let string_of_formulass = fun xss ->
    let ls = X.List.map string_of_formulas xss in
    "[" ^ (String.concat "; " ls) ^ "]"

let string_of_states = fun qs ->
    let f = fun q acc ->
        let sq = LTS.string_of_state q in
        sq :: acc
    in
    let ls = States.fold f qs [] in
    "{" ^ (String.concat ", " (List.rev ls)) ^ "}"

let print_binding = fun sx binding ->
    let (yss, qs) = binding in
    let syss = string_of_formulass yss in
    let sqs = string_of_states qs in
    print_endline (sx ^ " " ^ syss ^ " | " ^ sqs)

let print = fun flow_info ->
    let f = fun x bindings ->
        let sx = Id.to_string x in
        List.iter (print_binding sx) bindings
    in
    let fbmap = get_fbmap flow_info in
    LHS.iter f fbmap
