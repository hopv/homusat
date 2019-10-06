(* Saturation loop *)

module LHS = Id.IdMap
module RHS = Id.IdMap
module IdSet = Id.IdSet
module IdMap = Id.IdMap
module States = LTS.States
module FmlSet = ACG.FmlSet
module FmlMap = ACG.FmlMap
module FmlsSet = ACG.FmlsSet
module FmlsMap = ACG.FmlsMap
module Tau = Types.Tau
module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta
module Epsilon = Types.Epsilon
module Queue = Dependency.Queue

let print_epsilon = fun sx epsilon ->
    let f = fun sx tau theta ->
        let g = fun sx st gamma ->
            let sg = Types.string_of_gamma gamma in
            print_endline (sg ^ " |- " ^ sx ^ " : " ^ st)
        in
        let st = Types.string_of_tau tau in
        Theta.iter (g sx st) theta
    in
    Epsilon.iter (f sx) epsilon

let print_tj = fun tj ->
    let f = fun x epsilon ->
        let sx = Id.to_string x in
        print_epsilon sx epsilon
    in
    LHS.iter f tj

let print_lhste = fun lhste ->
    let f = fun x sigma ->
        let g = fun sx tau ->
            let st = Types.string_of_tau tau in
            print_endline (sx ^ " : " ^ st)
        in
        let sx = Id.to_string x in
        Sigma.iter (g sx) sigma
    in
    Gamma.iter f lhste

let string_of_formulas = fun xs ->
    let ls = X.List.map Enc.string_of_formula xs in
    "[" ^ (String.concat "; " ls) ^ "]"

let string_of_sigmas = fun sigmas ->
    let ls = X.List.map Types.string_of_sigma sigmas in
    "[" ^ (String.concat "; " ls) ^ "]"

let print_argte = fun argte ->
    let f = fun xs sigmass ->
        let g = fun sxs sigmas ->
            let sts = string_of_sigmas sigmas in
            print_endline (sxs ^ " : " ^ sts)
        in
        let sxs = string_of_formulas xs in
        List.iter (g sxs) sigmass
    in
    FmlsMap.iter f argte

(* Split xs into xs1 and xs2 so that |xs1| = |ys| *)
let split_xs = fun xs ys ->
    let rec f = fun xs ys acc ->
        match (xs, ys) with
        | (_, []) -> (List.rev acc, xs)
        | ([], _) -> assert false
        | (x :: xs, y :: ys) -> f xs ys (x :: acc)
    in
    f xs ys []

(* { x : sigma | x is a free variable } *)
let generate_gamma = fun xs fvs sigmas ->
    let f = fun fvs gamma x sigma ->
        if Sigma.is_empty sigma then gamma
        else if IdSet.mem x fvs then Gamma.add x sigma gamma
        else gamma
    in
    List.fold_left2 (f fvs) Gamma.empty xs sigmas

(* { { x : sigma | x is a free variable } } *)
let generate_theta = fun xs fvs sigmass ->
    let f = fun xs fvs theta sigmas ->
        let gamma = generate_gamma xs fvs sigmas in
        Theta.add gamma theta
    in
    List.fold_left (f xs fvs) Theta.empty sigmass

let prod_rhstes = fun argte xs ys fvs rhstes ->
    let (xs, next_xs) = split_xs xs ys in
    if FmlsMap.mem ys argte then
        let sigmass = FmlsMap.find ys argte in
        let theta = generate_theta xs fvs sigmass in
        let rhstes = Types.prod_thetas theta rhstes in
        (rhstes, next_xs)
    else (rhstes, next_xs)

(* Generate type environments for rhs variables *)
let generate_rhstes = fun argte xs fvs yss ->
    let rec f = fun argte xs fvs yss acc ->
        match yss with
        | [] -> acc
        | ys :: yss ->
            let (acc, next_xs) = prod_rhstes argte xs ys fvs acc in
            f argte next_xs fvs yss acc
    in
    let seed = Theta.singleton Gamma.empty in
    f argte xs fvs yss seed

(* Generate an intersection type \sigma_{1} -> ... -> \sigma_{k} -> q *)
(* from a type judgment x_{1} : \sigma_{1}, ..., x_{n} : \sigma_{k} |- q *)
let generate_tau = fun xs q gamma ->
    let g = fun (sigmas, gamma) x ->
        let sigma = Gamma.find_default Sigma.empty x gamma in
        let sigmas = sigma :: sigmas in
        let gamma = Gamma.remove x gamma in
        (sigmas, gamma)
    in
    let (rsigmas, gamma) = List.fold_left g ([], gamma) xs in
    let tau = Tau.encode (List.rev rsigmas, q) in
    (tau, gamma)

(* Generate epsilon from newly derived type judgments *)
let generate_epsilon = fun xs q theta ->
    let f = fun xs q gamma acc ->
        let (tau, gamma) = generate_tau xs q gamma in
        let theta = Epsilon.find_default Theta.empty tau acc in
        Epsilon.add tau (Theta.add gamma theta) acc
    in
    Theta.fold (f xs q) theta Epsilon.empty

let generate_epsilon_q =
    fun delta winning_nodes lhste rhste x ys body q acc ->
    let tau = Tau.encode ([], q) in
    let theta =
        TypeJudge.type_envs delta winning_nodes lhste rhste x body tau
    in
    (* let theta = Opt.normalize_theta theta in *)
    let epsilon = generate_epsilon ys q theta in
    Types.merge_epsilons acc epsilon

let generate_epsilon_rhste =
    fun qs delta winning_nodes lhste x ys body rhste acc ->
    TypeJudge.reset_memo (); (* Set a new memo for the new type env. *)
    (* let te = Types.merge_gammas lhste rhste in *)
    let f = generate_epsilon_q delta winning_nodes lhste rhste x ys body in
    States.fold f qs acc

let generate_epsilon_binding =
    fun delta winning_nodes lhste argte x ys body fvs acc binding ->
    let (zss, qs) = binding in
    let rhstes = generate_rhstes argte ys fvs zss in
    let f = generate_epsilon_rhste qs delta winning_nodes lhste x ys body in
    Theta.fold f rhstes acc

let generate_epsilon_lhs =
    fun fmap delta flow_info winning_nodes lhste argte x fvs ->
    let (ys, body) = LHS.find x fmap in
    let bindings = Flow.get_bindings x flow_info in
    let f =
        generate_epsilon_binding delta winning_nodes
                                 lhste argte x ys body fvs
    in
    List.fold_left f Epsilon.empty bindings

let update_tj = fun x epsilon tj ->
    LHS.add x epsilon tj (* Simply update with the new epsilon *)
    (*
    let tmp = LHS.find_default Epsilon.empty x tj in
    let epsilon = Types.merge_epsilons tmp epsilon in
    LHS.add x epsilon tj
    *)

let update_lhste = fun x epsilon lhste ->
    let f = fun tau theta sigma -> Sigma.add tau sigma in
    let sigma = Epsilon.fold f epsilon Sigma.empty in
    let old_sigma = Gamma.find_default Sigma.empty x lhste in
    let diff = Sigma.diff sigma old_sigma in
    if Sigma.is_empty diff then
        (lhste, false) (* Not updated *)
    else
        (* Simply update with the new sigma *)
        let lhste = Gamma.add x sigma lhste in
        (lhste, true) (* Updated *)
        (*
        let sigma = Sigma.union old_sigma diff in
        let lhste = Gamma.add x sigma lhste in
        (lhste, true) (* Updated *)
        *)

let generate_sigmas_rhste = fun delta aqmap lhste rhste ys ->
    let f = fun delta aqmap lhste rhste acc y ->
        let qs = FmlMap.find_default States.empty y aqmap in
        let sigma = TypeCheck.types qs delta lhste rhste y in
        sigma :: acc
    in
    TypeCheck.reset_memo (); (* Set a new memo for the new type env. *)
    (* let te = Types.merge_gammas lhste rhste in *)
    let rsigmas = List.fold_left (f delta aqmap lhste rhste) [] ys in
    List.rev rsigmas

let generate_sigmass_rhstes = fun delta aqmap lhste rhstes ys ->
    let f = fun delta aqmap lhste ys rhste acc ->
        let sigmas = generate_sigmas_rhste delta aqmap lhste rhste ys in
        sigmas :: acc
    in
    Theta.fold (f delta aqmap lhste ys) rhstes []

(* simplify sigmass to sigmas *)
let merge_sigmass = fun sigmass ->
    let f = fun acc sigmas ->
        let g = fun acc sigma1 sigma2 ->
            let sigma = Sigma.union sigma1 sigma2 in
            sigma :: acc
        in
        match acc with
        | [] -> sigmas
        | _ ->
            let racc = List.fold_left2 g [] acc sigmas in
            List.rev racc
    in
    List.fold_left f [] sigmass

let generate_sigmass_context =
    fun delta aqmap lhste argte xs ys fvs acc context ->
    let rhstes = generate_rhstes argte xs fvs context in
    let sigmass = generate_sigmass_rhstes delta aqmap lhste rhstes ys in
    List.rev_append sigmass acc

(* Safe and simple comparison (possibly inefficient in the long run) *)
let subsumed = fun sigmas1 sigmas2 ->
    List.for_all2 Sigma.subset sigmas1 sigmas2

(* Compare two sigma lists *)
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

module SigmasSet = X.Set.Make (struct
    type t = Sigma.t list
    let compare : t -> t -> int = compare_sigmass
end)

(* Memoize sigmas subsumed by another sigmas *)
let memo_sub = ref FmlsMap.empty

let remove_subsumed = fun ys sigmass ->
    let new_sigmass = SigmasSet.of_list sigmass in
    let old_sigmass = FmlsMap.find_default SigmasSet.empty ys !memo_sub in
    let sigmass = SigmasSet.diff new_sigmass old_sigmass in
    SigmasSet.elements sigmass

let update_subsumed = fun ys old_sigmass new_sigmass ->
    let old_sigmass = SigmasSet.of_list old_sigmass in
    let new_sigmass = SigmasSet.of_list new_sigmass in
    let diff = SigmasSet.diff old_sigmass new_sigmass in
    let old_diff = FmlsMap.find_default SigmasSet.empty ys !memo_sub in
    let new_diff = SigmasSet.union diff old_diff in
    memo_sub := FmlsMap.add ys new_diff !memo_sub

(* Naive implementation *)
(* Can be improved using some sophisticated algorithm like AMS-Lex *)
let merge_sigmass = fun sigmass1 sigmass2 ->
    let f = fun sigmass acc sigmas ->
        if List.exists (subsumed sigmas) sigmass then acc
        else sigmas :: acc
    in
    let sigmass1 = List.fold_left (f sigmass2) [] sigmass1 in
    let merged = List.fold_left (f sigmass1) sigmass1 sigmass2 in
    SigmasSet.elements (SigmasSet.of_list merged)

let normalize_sigmass = fun argte ys sigmass ->
    let sigmass = remove_subsumed ys sigmass in
    let sigmass = SigmasSet.of_list sigmass in
    let old_sigmass = FmlsMap.find_default [] ys argte in
    let old_sigmass = SigmasSet.of_list old_sigmass in
    let old_sigmass = SigmasSet.inter sigmass old_sigmass in
    let new_sigmass = SigmasSet.diff sigmass old_sigmass in
    let optimized =
        if SigmasSet.is_empty new_sigmass then
            FmlsMap.find_default [] ys argte
            (* SigmasSet.elements old_sigmass *)
        else
            let new_sigmass = SigmasSet.elements new_sigmass in
            let new_sigmass = Opt.normalize_sigmass new_sigmass in
            if SigmasSet.is_empty old_sigmass then new_sigmass
            else
                (* Here we know that old_sigmass and new_sigmass both *)
                (* consist of maximal sets. Moreover, they are mutually *)
                (* exclusive. How should we merge them? *)
                let old_sigmass = SigmasSet.elements old_sigmass in
                merge_sigmass old_sigmass new_sigmass
    in
    let sigmass = SigmasSet.elements sigmass in
    update_subsumed ys sigmass optimized;
    optimized

let generate_sigmass_rhs = fun fmap delta flow_info lhste argte x ys fvs ->
    let aqmap = Flow.get_aqmap flow_info in
    let contexts = Flow.get_contexts ys flow_info in
    if contexts = [] then
        let rhstes = Theta.singleton Gamma.empty in
        generate_sigmass_rhstes delta aqmap lhste rhstes ys
    else
        let (xs, _) = LHS.find x fmap in
        let f =
            generate_sigmass_context delta aqmap lhste argte xs ys fvs
        in
        let sigmass = List.fold_left f [] contexts in
        normalize_sigmass argte ys sigmass
        (* Opt.normalize_sigmass sigmass *)

(* Check if updated assuming that both lists are normalized *)
let updated_sigmass = fun sigmass1 sigmass2 ->
    if List.length sigmass1 = List.length sigmass2 then
        not (List.for_all2 (List.for_all2 Sigma.equal) sigmass1 sigmass2)
    else true

let update_argte = fun ys sigmass argte ->
    let old_sigmass = FmlsMap.find_default [] ys argte in
    if old_sigmass = [] then
        let argte = FmlsMap.add ys sigmass argte in
        (argte, true) (* Updated *)
    else if updated_sigmass sigmass old_sigmass then
        (FmlsMap.add ys sigmass argte, true) (* Updated *)
    else (argte, false) (* No updated *)

(* Add winning nodes to tj *)
let add_winning_nodes = fun winning_nodes tj ->
    let f = fun x sigma tj ->
        let g = fun x tau tj ->
            let theta = Theta.singleton Gamma.empty in
            let epsilon = LHS.find_default Epsilon.empty x tj in
            let epsilon = Epsilon.add tau theta epsilon in
            LHS.add x epsilon tj
        in
        Sigma.fold (g x) sigma tj
    in
    LHS.fold f winning_nodes tj

exception Over_loop
let counter = ref 1

let check_loop_count = fun lhste argte ->
    if !Flags.max_loops < !counter then begin
        let sn = string_of_int !Flags.max_loops in
        let msg = "Warning: maximum loop count (" ^ sn ^ ") is exceeded" in
        Log.prerrln 0 msg;
        raise Over_loop
    end else ()

let restrict_lhste = fun fvs lhste ->
    let f = fun lhste x acc ->
        if Gamma.mem x lhste then
            let sigma = Gamma.find x lhste in
            Gamma.add x sigma acc
        else acc
    in
    IdSet.fold (f lhste) fvs Gamma.empty

let add_axioms = fun axioms dep_kernels x lhste ->
    let f = fun axioms kernel acc ->
        let axiom = Gamma.find kernel axioms in
        let sigma = Gamma.find_default Sigma.empty kernel acc in
        let sigma = Sigma.union axiom sigma in
        Gamma.add kernel sigma acc
    in
    let kernels = LHS.find_default IdSet.empty x dep_kernels in
    IdSet.fold (f axioms) kernels lhste

(* Memoize type environments already checked by TypeJudge.type_envs *)
let prev_x = ref LHS.empty

(* TypeJudge.hoge must be refreshed when lhste is updated *)
let update_prev_x = fun x lhste ->
    let prev_lhste = LHS.find_default Gamma.empty x !prev_x in
    if Gamma.equal Sigma.equal lhste prev_lhste then ()
    else begin
        TypeJudge.reset_hoge x;
        prev_x := LHS.add x lhste !prev_x
    end

let propagate_lhs =
    fun fmap delta flow_info winning_nodes axioms dep_kernels tj lhste argte queue x ->
    Log.exec 3 (fun () ->
        print_endline ("propagating " ^ (Id.to_string x)));
    let fvs = Flow.get_children x flow_info in
    let lhste' = restrict_lhste fvs lhste in
    let lhste' = add_axioms axioms dep_kernels x lhste' in
    update_prev_x x lhste';
    let epsilon =
        generate_epsilon_lhs fmap delta flow_info
                             winning_nodes lhste' argte x fvs
    in
    let (epsilon, winning_nodes, tj) =
        Imm.optimize x epsilon winning_nodes tj
    in
    let tj = update_tj x epsilon tj in
    let (lhste, updated) = update_lhste x epsilon lhste in
    if updated then
        let queue = Queue.push_deps_func x queue in
        Log.println 3 "updated";
        (winning_nodes, axioms, tj, lhste, argte, queue)
    else (winning_nodes, axioms, tj, lhste, argte, queue)

(* Memoize type environments already checked by TypeCheck.types *)
let prev_ys = ref FmlsMap.empty

(* TypeCheck.hoge must be refreshed when lhste is updated *)
let update_prev_ys = fun ys lhste ->
    let prev_lhste = FmlsMap.find_default Gamma.empty ys !prev_ys in
    if Gamma.equal Sigma.equal lhste prev_lhste then ()
    else begin
        List.iter TypeCheck.reset_hoge ys;
        prev_ys := FmlsMap.add ys lhste !prev_ys
    end

let propagate_rhs =
    fun fmap delta flow_info winning_nodes axioms dep_kernels tj lhste argte queue ys ->
    Log.exec 3 (fun () ->
        print_endline ("propagating " ^ (string_of_formulas ys)));
    let x = Flow.get_parent ys flow_info in
    let fvs = Flow.get_siblings ys flow_info in
    let lhste' = restrict_lhste fvs lhste in
    let lhste' = add_axioms axioms dep_kernels x lhste' in
    update_prev_ys ys lhste';
    let sigmass =
        generate_sigmass_rhs fmap delta flow_info lhste' argte x ys fvs
    in
    let (argte, updated) = update_argte ys sigmass argte in
    if updated then
        let queue = Queue.push_deps_formulas ys queue in
        Log.println 3 "updated";
        (winning_nodes, axioms, tj, lhste, argte, queue)
    else (winning_nodes, axioms, tj, lhste, argte, queue)

let propagate =
    fun fmap delta flow_info
        winning_nodes axioms dep_kernels tj lhste argte queue elt ->
    Log.exec 6 (fun () -> print_lhste lhste);
    Log.exec 6 (fun () -> print_argte argte);
    Log.exec 3 (fun () ->
        print_endline ("loop #" ^ (string_of_int !counter)));
    counter := !counter + 1;
    check_loop_count lhste argte;
    match Queue.decode elt with
    | Dependency.Function (x) ->
        propagate_lhs fmap delta flow_info
                      winning_nodes axioms dep_kernels tj lhste argte queue x
    | Dependency.Formulas (ys) ->
        propagate_rhs fmap delta flow_info
                      winning_nodes axioms dep_kernels tj lhste argte queue ys

let rec loop =
    fun fmap delta flow_info
        winning_nodes axioms dep_kernels tj lhste argte queue ->
    if Queue.is_empty queue then
        let tj = add_winning_nodes winning_nodes tj in
        Log.exec 4 (fun () -> print_lhste lhste);
        Log.exec 4 (fun () -> print_argte argte);
        Log.exec 4 (fun () -> print_tj tj);
        tj
    else
        let elt = Queue.min_elt queue in
        let queue = Queue.remove elt queue in
        let (winning_nodes, axioms, tj, lhste, argte, queue) =
            propagate fmap delta flow_info
                winning_nodes axioms dep_kernels tj lhste argte queue elt
        in
        loop fmap delta flow_info
             winning_nodes axioms dep_kernels tj lhste argte queue

let generate_axioms = fun funcs flow_info kernels ->
    let f = fun fqmap kernels acc func ->
        let g = fun sort q sigma ->
            let tau = Types.strongest_type sort q in
            Sigma.add tau sigma
        in
        let (fp, x, sort, args, body) = func in
        if IdSet.mem x kernels then
            let qs = LHS.find_default States.empty x fqmap in
            let sigma = States.fold (g sort) qs Sigma.empty in
            Gamma.add x sigma acc
        else acc
    in
    let fqmap = Flow.get_fqmap flow_info in
    List.fold_left (f fqmap kernels) Gamma.empty funcs

let generate_fmap = fun funcs ->
    let f = fun acc func ->
        let (_, x, _, args, fml) = func in
        let args = X.List.map fst args in
        LHS.add x (args, fml) acc
    in
    List.fold_left f LHS.empty funcs

let saturate = fun funcs lts kernels dep_kernels flow_info ->
    Types.register_states lts;
    let fmap = generate_fmap funcs in
    let (_, _, delta, _) = lts in
    let tj = LHS.empty in
    let winning_nodes = Gamma.empty in
    let axioms = generate_axioms funcs flow_info kernels in
    let lhste = Gamma.empty in
    let argte = FmlsMap.empty in
    let queue = Queue.init funcs flow_info in
    loop fmap delta flow_info
         winning_nodes axioms dep_kernels tj lhste argte queue
