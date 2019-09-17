(* flow information *)

(* flows: X \mapsto { \phi | X <~ \phi } *)
(* rev_flows: \phi \mapsto { X | X <~ \phi } *)

(* for construction of type environments *)
(* fqmap: F \mapsto \bigcup { P | (F :: yss, P) is a node of ACG } *)
(* xqmap: X \mapsto \bigcup { P | (X :: yss, P) is a node of ACG } *)
(* aqmap: \phi mapsto \bigcup_{X <~ \phi} xqmap(X) *)
(* fbmap: F \mapsto [ (yss, P) | (F :: yss, P) is a node of ACG ] *)
(* fvmap: F \mapsto { X | X occurs in the body of F } *)
(* ffmap: F \mapsto { G | G occurs in the body of F } *)
(* abmap: \phi \mapsto [ yss | (par(\phi) :: yss, P) is a node of ACG ] *)
(* avmap: \phi \mapsto { X | X occurs in \phi } *)
(* afmap: \phi \mapsto { F | F occurs in \phi } *)
(* parents: \phi \mapsto F : F is the parent of \phi *)
(* childrens: F \mapsto { X/G | X/G occurs in the body of F } *)
(* siblings: \phi \mapsto { X/G | X/G occurs in \phi } *)
(* llmap: F \mapsto { G | F occurs in the body of G } *)
(* lamap: F \mapsto { \phi | F occurs in \phi } *)
(* rlmap: X \mapsto F, where X is an argument of F *)
(* ramap: X \mapsto { \phi | X occurs in \phi } *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module IdSet = Id.IdSet
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
type fvmap = IdSet.t LHS.t
type ffmap = IdSet.t LHS.t
type abmap = (Enc.elt list list) list FmlsMap.t
type avmap = IdSet.t FmlsMap.t
type afmap = IdSet.t FmlsMap.t
type parents = Id.t FmlsMap.t
type childrens = IdSet.t LHS.t
type siblings = IdSet.t FmlsMap.t
type llmap = IdSet.t LHS.t
type lamap = FmlsSet.t LHS.t
type rlmap = Id.t RHS.t
type ramap = FmlsSet.t RHS.t
type t = { flows : flows; rev_flows : rev_flows;
           fqmap : fqmap; aqmap : aqmap; fbmap : fbmap; abmap : abmap;
           parents : parents; childrens : childrens; siblings : siblings;
           llmap : llmap; lamap : lamap; rlmap : rlmap; ramap : ramap; }

(* generate the set of lhs variables and the set of rhs variables *)
let generate_top_vars = fun funcs ->
    let f = fun (lhs, rhs) func ->
        let (_, x, _, args, _) = func in
        let lhs = IdSet.add x lhs in
        let g = fun rhs (y, t) -> IdSet.add y rhs in
        let rhs = List.fold_left g rhs args in
        (lhs, rhs)
    in
    List.fold_left f (IdSet.empty, IdSet.empty) funcs

(* obtain the set of all variables occurring in a formula *)
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

(* fqmap: F \mapsto \bigcup { P | (F :: yss, P) is a node of ACG } *)
let generate_fqmap = fun top_vars acg ->
    let f = fun lhs fml qs acc ->
        match fml with
        | ACG.App (x, yss) when IdSet.mem x lhs ->
            let ps = LHS.find_default States.empty x acc in
            let ps = States.union ps qs in
            LHS.add x ps acc
        | _ -> acc
    in
    let (lhs, _) = top_vars in
    let (nodes, _, _) = acg in
    FmlMap2.fold (f lhs) nodes LHS.empty

(* xqmap: X \mapsto \bigcup { P | (X :: yss, P) is a node of ACG } *)
let generate_xqmap = fun top_vars acg ->
    let f = fun rhs fml qs acc ->
        match fml with
        | ACG.App (x, yss) when IdSet.mem x rhs ->
            let ps = RHS.find_default States.empty x acc in
            let ps = States.union ps qs in
            RHS.add x ps acc
        | _ -> acc
    in
    let (_, rhs) = top_vars in
    let (nodes, _, _) = acg in
    FmlMap2.fold (f rhs) nodes RHS.empty

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
            let zs = LHS.find_default [] x acc in
            let zs = (yss, qs) :: zs in
            LHS.add x zs acc
        | _ -> acc
    in
    let (lhs, _) = top_vars in
    let (nodes, _, _) = acg in
    FmlMap2.fold (f lhs) nodes LHS.empty

(* fvmap: F \mapsto { X | X occurs in the body of F } *)
let generate_fvmap = fun top_vars funcs ->
    let f = fun rhs acc func ->
        let (_, x, _, _, body) = func in
        let xs = get_xs IdSet.empty body in
        let xs = IdSet.inter rhs xs in
        LHS.add x xs acc
    in
    let (_, rhs) = top_vars in
    List.fold_left (f rhs) LHS.empty funcs

(* ffmap: F \mapsto { G | G occurs in the body of F } *)
let generate_ffmap = fun top_vars funcs ->
    let f = fun lhs acc func ->
        let (_, x, _, _, body) = func in
        let xs = get_xs IdSet.empty body in
        let xs = IdSet.inter lhs xs in
        LHS.add x xs acc
    in
    let (lhs, _) = top_vars in
    List.fold_left (f lhs) LHS.empty funcs

(* simplify ys -> xss to ys -> xs *)
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

(* exclude unused variables from simplified rev_flows *)
let restrict_rev_flows = fun fvmap acg ->
    let f = fun x fvs acc -> IdSet.union fvs acc in
    let g = fun fvs ys zs acc ->
        let zs = IdSet.inter zs fvs in
        if IdSet.is_empty zs then acc
        else FmlsMap.add ys zs acc
    in
    let (nodes, flows, rev_flows) = acg in
    let fvs = LHS.fold f fvmap IdSet.empty in
    let rev_flows = simplify_rev_flows rev_flows in
    let rev_flows = FmlsMap.fold (g fvs) rev_flows FmlsMap.empty in
    (nodes, flows, rev_flows)

(* avmap: \phi \mapsto { X | X occurs in \phi } *)
let generate_avmap = fun top_vars acg ->
    let f = fun rhs ys zs acc ->
        let xs = List.fold_left get_xs IdSet.empty ys in
        let xs = IdSet.inter xs rhs in
        FmlsMap.add ys xs acc
    in
    let (_, rhs) = top_vars in
    let (_, _, rev_flows) = acg in
    FmlsMap.fold (f rhs) rev_flows FmlsMap.empty

(* afmap: \phi \mapsto { F | F occurs in \phi } *)
let generate_afmap = fun top_vars acg ->
    let f = fun lhs ys zs acc ->
        let xs = List.fold_left get_xs IdSet.empty ys in
        let xs = IdSet.inter xs lhs in
        FmlsMap.add ys xs acc
    in
    let (lhs, _) = top_vars in
    let (_, _, rev_flows) = acg in
    FmlsMap.fold (f lhs) rev_flows FmlsMap.empty

(* fml is a subformula of the body of p *)
let rec add_parent = fun p acc fml ->
    match Enc.decode fml with
    | Enc.Or (ys)
    | Enc.And (ys) ->
        List.fold_left (add_parent p) acc ys
    | Enc.Box (a, x)
    | Enc.Diamond (a, x) -> (add_parent p) acc x
    | Enc.App (x, ys) ->
        let acc = FmlsMap.add ys p acc in
        List.fold_left (add_parent p) acc ys

(* parents: \phi \mapsto F : F is the parent of \phi *)
let generate_parents = fun acg funcs ->
    let f = fun acc func ->
        let (fp, x, sort, args, body) = func in
        add_parent x acc body
    in
    let g = fun ps ys zs acc ->
        let x = FmlsMap.find ys ps in
        FmlsMap.add ys x acc
    in
    let ps = List.fold_left f FmlsMap.empty funcs in
    let (_, _, rev_flows) = acg in
    FmlsMap.fold (g ps) rev_flows FmlsMap.empty

(* abmap: \phi \mapsto [ yss | (P :: yss, qs) is a node of ACG } *)
let generate_abmap = fun top_vars acg fbmap parents ->
    let f = fun rhs fbmap parents ys zs acc ->
        let xs = List.fold_left get_xs IdSet.empty ys in
        let inter = IdSet.inter xs rhs in
        if IdSet.is_empty inter then
            FmlsMap.add ys [] acc
        else
            let p = FmlsMap.find ys parents in
            let bindings = LHS.find_default [] p fbmap in
            let contexts = X.List.map fst bindings in
            FmlsMap.add ys contexts acc
    in
    let (_, rhs) = top_vars in
    let (_, _, rev_flows) = acg in
    FmlsMap.fold (f rhs fbmap parents) rev_flows FmlsMap.empty

(* childrens: F \mapsto { X/G | X/G occurs in the body of F } *)
let generate_childrens = fun funcs ->
    let f = fun acc func ->
        let (fp, x, sort, args, body) = func in
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

(* llmap: F \mapsto { G | F occurs in the body of G } *)
let generate_llmap = fun top_vars funcs ->
    let f = fun lhs acc func ->
        let g = fun x y acc ->
            let xs = LHS.find_default IdSet.empty y acc in
            let xs = IdSet.add x xs in
            LHS.add y xs acc
        in
        let (_, x, _, _, body) = func in
        let xs = get_xs IdSet.empty body in
        let xs = IdSet.inter lhs xs in
        IdSet.fold (g x) xs acc
    in
    let (lhs, _) = top_vars in
    List.fold_left (f lhs) LHS.empty funcs

(* lamap: F \mapsto { \phi | F occurs in \phi } *)
let generate_lamap = fun top_vars acg ->
    let f = fun lhs ys zs acc ->
        let g = fun ys x acc ->
            let yss = LHS.find_default FmlsSet.empty x acc in
            let yss = FmlsSet.add ys yss in
            LHS.add x yss acc
        in
        let xs = List.fold_left get_xs IdSet.empty ys in
        let xs = IdSet.inter lhs xs in
        IdSet.fold (g ys) xs acc
    in
    let (lhs, _) = top_vars in
    let (_, _, rev_flows) = acg in
    FmlsMap.fold (f lhs) rev_flows LHS.empty

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

(* ramap: X \mapsto { \phi | X occurs in \phi } *)
let generate_ramap = fun top_vars acg ->
    let f = fun rhs ys zs acc ->
        let g = fun ys x acc ->
            let yss = RHS.find_default FmlsSet.empty x acc in
            let yss = FmlsSet.add ys yss in
            LHS.add x yss acc
        in
        let xs = List.fold_left get_xs IdSet.empty ys in
        let xs = IdSet.inter rhs xs in
        IdSet.fold (g ys) xs acc
    in
    let (_, rhs) = top_vars in
    let (_, _, rev_flows) = acg in
    FmlsMap.fold (f rhs) rev_flows RHS.empty

let generate_flow_info = fun funcs lts ->
    let acg = ACG.construct funcs lts in
    let top_vars = generate_top_vars funcs in
    let fqmap = generate_fqmap top_vars acg in
    let aqmap = generate_aqmap top_vars acg in
    let fbmap = generate_fbmap top_vars acg in
    let fvmap = generate_fvmap top_vars funcs in
    let acg = restrict_rev_flows fvmap acg in
    let parents = generate_parents acg funcs in
    let childrens = generate_childrens funcs in
    let siblings = generate_siblings acg in
    let abmap = generate_abmap top_vars acg fbmap parents in
    let llmap = generate_llmap top_vars funcs in
    let lamap = generate_lamap top_vars acg in
    let rlmap = generate_rlmap funcs in
    let ramap = generate_ramap top_vars acg in
    let (_, flows, rev_flows) = acg in
    { flows : flows; rev_flows : rev_flows;
      fqmap : fqmap; aqmap : aqmap; fbmap : fbmap; abmap : abmap;
      parents : parents; childrens : childrens; siblings : siblings;
      llmap : llmap; lamap : lamap; rlmap : rlmap; ramap : ramap; }

let get_flows = fun flow_info -> flow_info.flows
let get_rev_flows = fun flow_info -> flow_info.rev_flows
let get_fqmap = fun flow_info -> flow_info.fqmap
let get_aqmap = fun flow_info -> flow_info.aqmap
let get_fbmap = fun flow_info -> flow_info.fbmap
let get_abmap = fun flow_info -> flow_info.abmap
let get_parents = fun flow_info -> flow_info.parents
let get_childrens = fun flow_info -> flow_info.childrens
let get_siblings = fun flow_info -> flow_info.siblings
let get_llmap = fun flow_info -> flow_info.llmap
let get_lamap = fun flow_info -> flow_info.lamap
let get_rlmap = fun flow_info -> flow_info.rlmap
let get_ramap = fun flow_info -> flow_info.ramap

(* return binding list for x *)
let get_bindings = fun x flow_info ->
    let fbmap = get_fbmap flow_info in
    LHS.find_default [] x fbmap

let get_contexts = fun ys flow_info ->
    let abmap = get_abmap flow_info in
    FmlsMap.find ys abmap

let get_parent = fun ys flow_info ->
    let parents = get_parents flow_info in
    FmlsMap.find ys parents

(* return the set of variables occurring in the body of x *)
let get_children = fun x flow_info ->
    let childrens = get_childrens flow_info in
    LHS.find x childrens

(* return the set of variables occurring in ys *)
let get_siblings = fun ys flow_info ->
    let siblings = get_siblings flow_info in
    FmlsMap.find ys siblings

(* destinations of propagation from a lhs variable x *)
let get_dep_lhs = fun x flow_info ->
    let llmap = get_llmap flow_info in
    let lamap = get_lamap flow_info in
    let ys = LHS.find_default IdSet.empty x llmap in
    let zs = LHS.find_default FmlsSet.empty x lamap in
    (ys, zs)

(* destinations of propagation from a rhs variable x *)
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
