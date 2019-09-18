(* Convert (extended) HES into HFS *)

module LHS = Id.IdMap
(* Type environment *)
module Env = Id.IdMap
(* Free variables *)
module FVs = Id.IdSet
(* Bound variables *)
module BVs = Id.IdSet

let convert_fp = fun fp ->
    match fp with
    | HES.Mu -> HFS.Mu
    | HES.Nu -> HFS.Nu

let rec convert_type = fun t ->
    match t with
    | HES.Prop -> HFS.Prop
    | HES.TyVar (_) -> assert false
    | HES.Arrow (x, y) -> HFS.Arrow (convert_type x, convert_type y)

(* Retrieve all arguments of consecutive lambda abstractions *)
let rec retrieve_formal_args = fun body acc ->
    match body with
    | HES.Abs ((x, _), t, body, _) ->
        retrieve_formal_args body ((x, convert_type t) :: acc)
    | _ -> (List.rev acc, body)

(* Get return type of a function type *)
let get_rt = fun t ->
    match t with
    | HFS.Arrow (l, r) -> r
    | HFS.Prop -> assert false

let add_binding = fun env (x, t) -> Env.add x t env

(* Convert an HFL formula into a sequence of normalized HFS functions *)
let rec convert_fml = fun fp env fml acc ->
    (* Or (a, b) -> [a'; ...; b'; ... ] *)
    let rec convert_or = fun fp env fml acc ->
        match fml with
        | HES.Or (l, r) ->
            let (r, acc) = convert_or fp env r acc in
            let (l, acc) = convert_or fp env l acc in
            let ors = X.List.append l r in
            (ors, acc)
        | _ ->
            let (fml, acc, _) = convert_fml fp env fml acc in
            match fml with
            | HFS.Or (x) -> assert (x = []); ([], acc) (* false *)
            | _ -> ([fml], acc)
    in
    (* And (a, b) -> [a'; ...; b'; ... ] *)
    let rec convert_and = fun fp env fml acc ->
        match fml with
        | HES.And (l, r) ->
            let (r, acc) = convert_and fp env r acc in
            let (l, acc) = convert_and fp env l acc in
            let ands = X.List.append l r in
            (ands, acc)
        | _ ->
            let (fml, acc, _) = convert_fml fp env fml acc in
            match fml with
            | HFS.And (xs) -> assert (xs = []); ([], acc) (* true *)
            | _ -> ([fml], acc)
    in
    (* ((...((F a) b) ...) z) -> F' [...; a'; b'; ...; z'] *)
    let rec convert_app = fun fp env fml acc args ->
        match fml with
        | HES.App (l, r) ->
            let (r, acc, _) = convert_fml fp env r acc in
            let (fml, acc, lt) = convert_app fp env l acc (r :: args) in
            (fml, acc, get_rt lt)
        | _ ->
            let (fml, acc, t) = convert_fml fp env fml acc in
            match fml with
            | HFS.App (x, []) -> (* A variable or a functional formula *)
                (HFS.App (x, args), acc, t)
            | _ -> assert false
    in
    (* Convert a functional formula into a function *)
    let convert_func = fun fp x env args body acc ->
        let (body, acc, t) = convert_fml fp env body acc in
        let f = fun acc (_, t) -> HFS.Arrow (t, acc) in
        let rt = List.fold_left f t (List.rev args) in
        let ret = HFS.App (x, []) in
        let acc = (fp, x, rt, args, body) :: acc in
        (ret, acc, rt)
    in
    match fml with
    | HES.True (_) -> (HFS.And ([]), acc, HFS.Prop)
    | HES.False (_) -> (HFS.Or ([]), acc, HFS.Prop)
    | HES.Var (x, _) -> (HFS.App (x, []), acc, Env.find x env)
    | HES.Or (l, r) ->
        let (r, acc) = convert_or fp env r acc in
        let (l, acc) = convert_or fp env l acc in
        let ors = X.List.append l r in
        (HFS.Or (ors), acc, HFS.Prop)
    | HES.And (l, r) ->
        let (r, acc) = convert_and fp env r acc in
        let (l, acc) = convert_and fp env l acc in
        let ands = X.List.append l r in
        (HFS.And (ands), acc, HFS.Prop)
    | HES.Box (a, x, _) ->
        let (x, acc, t) = convert_fml fp env x acc in
        (HFS.Box (a, x), acc, HFS.Prop)
    | HES.Diamond (a, x, _) ->
        let (x, acc, t) = convert_fml fp env x acc in
        (HFS.Diamond (a, x), acc, HFS.Prop)
    | HES.App (_, _) -> convert_app fp env fml acc []
    | HES.Abs ((x, _), t, body, _) ->
        let y = Id.gen_var "F" in
        let t = convert_type t in
        let (args, body) = retrieve_formal_args body [(x, t)] in
        let env = List.fold_left add_binding env args in
        convert_func fp y env args body acc
    | HES.Mu ((x, _), t, body, _) ->
        let (args, body) = retrieve_formal_args body [] in
        let env = Env.add x (convert_type t) env in
        let env = List.fold_left add_binding env args in
        convert_func HFS.Mu x env args body acc
    | HES.Nu ((x, _), t, body, _) ->
        let (args, body) = retrieve_formal_args body [] in
        let env = Env.add x (convert_type t) env in
        let env = List.fold_left add_binding env args in
        convert_func HFS.Nu x env args body acc

let convert_eq = fun env acc eq ->
    let (fp, (x, _), t, fml) = eq in
    let fp = convert_fp fp in
    let (args, fml) = retrieve_formal_args fml [] in
    let env = List.fold_left add_binding env args in
    let (fml, acc, rt) = convert_fml fp env fml acc in
    let func = (fp, x, convert_type t, args, fml) in
    func :: acc

(* Add arguments for applications of functions with free variables *)
(* This can result in additional free variables occurring in the formula *)
let rec add_free_args_with_fvmap_fml = fun fvmap fml ->
    match fml with
    | HFS.Or (xs) ->
        HFS.Or (X.List.map (add_free_args_with_fvmap_fml fvmap) xs)
    | HFS.And (xs) ->
        HFS.And (X.List.map (add_free_args_with_fvmap_fml fvmap) xs)
    | HFS.Box (a, x) ->
        let x = add_free_args_with_fvmap_fml fvmap x in
        HFS.Box (a, x)
    | HFS.Diamond (a, x) ->
        let x = add_free_args_with_fvmap_fml fvmap x in
        HFS.Diamond (a, x)
    | HFS.App (x, ys) ->
       let ys = X.List.map (add_free_args_with_fvmap_fml fvmap) ys in
       if LHS.mem x fvmap then
           let fargs = LHS.find x fvmap in
           let f = fun acc (y, _) -> (HFS.App (y, [])) :: acc in
           let ys = List.fold_left f ys fargs in
           HFS.App (x, ys) (* Should be renamed later *)
       else HFS.App (x, ys)

(* Add formal arguments for functions with free variables *)
let add_free_args_with_fvmap = fun fvmap funcs ->
    let f = fun fvmap func ->
        let (fp, x, t, args, fml) = func in
        let fml = add_free_args_with_fvmap_fml fvmap fml in
        if LHS.mem x fvmap then
            let fargs = LHS.find x fvmap in
            let g = fun acc (_, u) -> HFS.Arrow (u, acc) in
            let t = List.fold_left g t fargs in (* Type must be changed *)
            let args = List.rev_append fargs args in
            (fp, x, t, args, fml)
        else (fp, x, t, args, fml)
    in
    X.List.map (f fvmap) funcs

(* Get all free variables in fml *)
let rec get_fvs = fun bvs fml ->
    let add_fvs = fun bvs acc y -> FVs.union acc (get_fvs bvs y) in
    match fml with
    | HFS.Or (xs)
    | HFS.And (xs) ->
        List.fold_left (add_fvs bvs) FVs.empty xs
    | HFS.Box (a, x)
    | HFS.Diamond (a, x) ->
        get_fvs bvs x
    | HFS.App (x, ys) ->
       let fvs = if BVs.mem x bvs then FVs.empty else FVs.singleton x in
       List.fold_left (add_fvs bvs) fvs ys

(* Get the set of all lhs variables and type bindings for all variables *)
let get_lhs_and_env = fun funcs ->
    let f = fun (lhs, env) func ->
        let (_, x, t, args, _) = func in
        let lhs = BVs.add x lhs in
        let env = List.fold_left add_binding (Env.add x t env) args in
        (lhs, env)
    in
    let seed = (BVs.empty, Env.empty) in
    List.fold_left f seed funcs

(* Construct fvmap for the current state of funcs *)
let construct_fvmap = fun lhs env funcs ->
    let f = fun lhs env fvmap func ->
        let (_, x, t, args, fml) = func in
        let g = fun acc (y, u) -> BVs.add y acc in
        let bvs = List.fold_left g lhs args in
        let fvs = get_fvs bvs fml in
        if FVs.is_empty fvs then fvmap
        else
            let h = fun env y acc -> (y, Env.find y env) :: acc in
            let fvs = FVs.fold (h env) fvs [] in
            LHS.add x fvs fvmap
    in
    List.fold_left (f lhs env) LHS.empty funcs

(* Add free arguments recursively until it reaches the fixed-point *)
let add_free_args = fun funcs ->
    let rec loop = fun lhs env funcs ->
        let fvmap = construct_fvmap lhs env funcs in
        if LHS.is_empty fvmap then funcs
        else
            let funcs = add_free_args_with_fvmap fvmap funcs in
            loop lhs env funcs
    in
    let (lhs, env) = get_lhs_and_env funcs in
    (* All variables are contained in env and thus update is unnecessary *)
    loop lhs env funcs

(* Get sorts of arguments as a list *)
let get_arg_sorts = fun t ->
    let rec get_arg_sorts_rec = fun t acc ->
        match t with
        | HFS.Prop -> List.rev acc
        | HFS.Arrow (x, y) -> get_arg_sorts_rec y (x :: acc)
    in
    get_arg_sorts_rec t []

let add_ornamental_args_func = fun func ->
    let rec f = fun arg_sorts args (rargs, revr) ->
        match (arg_sorts, args) with
        | ([], []) -> (List.rev rargs, List.rev revr)
        | ([], _) -> assert false
        | (arg_sort :: arg_sorts, []) ->
            let x = Id.gen_var "x" in
            let rargs = (x, arg_sort) :: rargs in
            let revr = (HFS.App (x, [])) :: revr in
            f arg_sorts [] (rargs, revr)
        | (arg_sort :: arg_sorts, arg :: args) ->
            let rargs = arg :: rargs in
            f arg_sorts args (rargs, revr)
    in
    let (fp, x, t, args, fml) = func in
    let arg_sorts = get_arg_sorts t in
    let diff = List.length arg_sorts - List.length args in
    if 0 < diff then
        match fml with
        | HFS.App (l, r) ->
            let (args, r) = f arg_sorts args ([], List.rev r) in
            (fp, x, t, args, HFS.App (l, r))
        | _ -> assert false
    else (fp, x, t, args, fml)

let add_ornamental_args = fun funcs ->
    X.List.map add_ornamental_args_func funcs

let initial_env = fun eqs ->
    let f = fun env eq ->
        let (_, (x, _), t, _) = eq in
        Env.add x (convert_type t) env
    in
    List.fold_left f Env.empty eqs

let normalize = fun eqs ->
    let reqs = List.rev eqs in
    let env = initial_env reqs in
    let funcs = List.fold_left (convert_eq env) [] reqs in
    let funcs = add_free_args funcs in
    let funcs = add_ornamental_args funcs in
    AlphaHFS.rename funcs
