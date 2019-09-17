(* Type inference/reconstruction *)

(* Type environment *)
module Env = Id.IdMap

module UnionFind = struct

    (* We can use arrays instead of sets and maps *)
    module S = X.Set.Make (struct
        type t = HES.simple_type
        let compare : t -> t -> int = compare
    end)
    module M = X.Map.Make (struct
        type t = HES.simple_type
        let compare : t -> t -> int = compare
    end)

    (* No rank function *)
    type t = HES.simple_type M.t

    exception Typing_error
    exception Unification_error of HES.simple_type

    let rec find = fun x uft ->
        let px = M.find_default x x uft in
        if px = x then (px, uft)
        else
            let (px, uft) = find px uft in
            (px, M.add x px uft)

    let rec union = fun x y uft ->
        let (x, uft) = find x uft in
        let (y, uft) = find y uft in
        match (x, y) with
        | (HES.Prop, HES.Prop) -> uft
        | (HES.Arrow (x1, x2), HES.Arrow (y1, y2)) ->
            let uft = M.add x y uft in (* Corbin & Bidoit (1983) *)
            union x2 y2 (union x1 y1 uft)
        | (HES.TyVar (i), HES.TyVar (j)) when i = j -> uft
        | (HES.TyVar (i), _) -> M.add x y uft (* No occurs check *)
        | (_, HES.TyVar (i)) -> M.add y x uft (* No occurs check *)
        | _ -> raise Typing_error

    let exit_with_typing_error = fun x y pos ->
        let spos = Position.to_string pos in
        let sx = HES.string_of_simple_type x in
        let sy = HES.string_of_simple_type y in
        let msg = spos ^ ":\n" ^
                  "Typing error: this expression has type " ^ sx ^ ", " ^
                  "but an expression was expected of type " ^ sy in
        Log.println 0 msg;
        exit 1

    let exit_with_unification_error = fun t u v w pos ->
        let spos = Position.to_string pos in
        let st = HES.string_of_simple_type t in
        let su = HES.string_of_simple_type u in
        let sv = HES.string_of_simple_type v in
        let sw = HES.string_of_simple_type w in
        let msg = spos ^ ":\n" ^
                  "Unification error: this expression has type " ^ st ^
                  ", but an expression was expected of type " ^ su ^ "." ^
                  " the type variable " ^ sv ^ " occurs inside " ^ sw in
        Log.println 0 msg;
        exit 1

    (* Auxiliary function for pretty error printing *)
    let rec partially_reconstruct_oc = fun visited x uft ->
        if S.mem x visited then (x, uft)
        else
            let visited = S.add x visited in
            let (x, uft) = find x uft in
            match x with
            | HES.Arrow (x, y) ->
                let (x, uft) = partially_reconstruct_oc visited x uft in
                let (y, uft) = partially_reconstruct_oc visited y uft in
                (HES.Arrow (x, y), uft)
            | _ -> (x, uft)

    let partially_reconstruct = fun x uft ->
        partially_reconstruct_oc S.empty x uft

    let unify = fun x y pos uft ->
        try union x y uft
        with Typing_error ->
            let (x, uft) = partially_reconstruct x uft in
            let (y, uft) = partially_reconstruct y uft in
            exit_with_typing_error x y pos

    let warn_unresolved_variable = fun x pos t ->
        let sx = Id.to_string x in
        let st = HES.string_of_simple_type t in
        let so = HES.string_of_simple_type HES.Prop in
        let spos = Position.to_string pos in
        let msg = spos ^ ":\n" ^
                  "Warning: inferred type for the variable '" ^ sx ^ "'" ^
                  " contains an unresolved type variable " ^ st ^ "," ^
                  " which is arbitrarily assumed to be type " ^ so in
        Log.prerrln 0 msg

    (* Reconstruction with occurs check *)
    let rec reconstruct_oc = fun x pos visited t uft ->
        if S.mem t visited then
            raise (Unification_error (t))
        else
            let visited = S.add t visited in
            let (t, uft) = find t uft in
            match t with
            | HES.Prop -> (HES.Prop, uft)
            | HES.TyVar (_) ->
                warn_unresolved_variable x pos t;
                let uft = unify t HES.Prop pos uft in
                (HES.Prop, uft)
            | HES.Arrow (t1, t2) ->
                let (t1, uft) = reconstruct_oc x pos visited t1 uft in
                let (t2, uft) = reconstruct_oc x pos visited t2 uft in
                let ret = HES.Arrow (t1, t2) in
                let uft = union t ret uft in
                (ret, uft)

    (* The id x and pos are used for warning *)
    let reconstruct = fun x pos t uft ->
        try reconstruct_oc x pos S.empty t uft
        with Unification_error (v) ->
            let stop = S.singleton v in
            let (u, uft) = partially_reconstruct t uft in
            let (w, uft) = partially_reconstruct v uft in
            let (t, uft) = partially_reconstruct_oc stop t uft in
            exit_with_unification_error t u v w pos

    let create_from_constraints = fun cs ->
        let f = fun uft (t, u, pos) ->
            unify t u pos uft
        in
        List.fold_left f M.empty cs

end

let initial_env = fun eqs ->
    let f = fun acc eq ->
        let (_, (x, _), t, _) = eq in
        Env.add x t acc
    in
    List.fold_left f Env.empty eqs

let generate_constraints = fun eqs ->
    let rec generate_from_formula = fun env cs fml ->
        match fml with
        | HES.True (pos)
        | HES.False (pos) ->
            (HES.Prop, cs, pos)
        | HES.Var (x, pos) ->
            if Env.mem x env then (Env.find x env, cs, pos)
            else begin
                let sx = Id.to_string x in
                let spos = Position.to_string pos in
                let msg = spos ^ ":\n" ^
                          "Error: unbound variable '" ^ sx ^ "'" in
                Log.println 0 msg;
                exit 1
            end
        | HES.Or (l, r) | HES.And (l, r) ->
            let (lt, cs, lp) = generate_from_formula env cs l in
            let (rt, cs, rp) = generate_from_formula env cs r in
            let cs = (lt, HES.Prop, lp) :: cs in
            let cs = (rt, HES.Prop, rp) :: cs in
            (HES.Prop, cs, Position.compose lp rp)
        | HES.Box (_, x, pos) | HES.Diamond (_, x, pos) ->
            let (t, cs, q) = generate_from_formula env cs x in
            let cs = (t, HES.Prop, q) :: cs in
            (HES.Prop, cs, pos)
        | HES.App (l, r) ->
            let (lt, cs, lp) = generate_from_formula env cs l in
            let (rt, cs, rp) = generate_from_formula env cs r in
            let t = HES.gen_type () in
            let cs = (lt, HES.Arrow (rt, t), lp) :: cs in
            (t, cs, Position.compose lp rp)
        | HES.Abs ((x, p), t, body, q) ->
            let env = Env.add x t env in
            let (u, cs, _) = generate_from_formula env cs body in
            (HES.Arrow (t, u), cs, q)
        | HES.Mu ((x, p), t, body, q)
        | HES.Nu ((x, p), t, body, q) ->
            let env = Env.add x t env in
            let (u, cs, _) = generate_from_formula env cs body in
            let cs = (t, u, p) :: cs in
            (t, cs, q)
    in
    let generate_from_eq = fun env cs eq ->
        let (fp, (x, pos), t, fml) = eq in
        let (u, cs, pos) = generate_from_formula env cs fml in
        (t, u, pos) :: cs
    in
    let env = initial_env eqs in
    List.fold_left (generate_from_eq env) [] eqs

let rec annot_formula = fun uft fml ->
    match fml with
    | HES.True (_)
    | HES.False (_)
    | HES.Var (_, _) -> (fml, uft)
    | HES.Or (l, r) ->
        let (l, uft) = annot_formula uft l in
        let (r, uft) = annot_formula uft r in
        (HES.Or (l, r), uft)
    | HES.And (l, r) ->
        let (l, uft) = annot_formula uft l in
        let (r, uft) = annot_formula uft r in
        (HES.And (l, r), uft)
    | HES.Box (a, x, p) ->
        let (x, uft) = annot_formula uft x in
        (HES.Box (a, x, p), uft)
    | HES.Diamond (a, x, p) ->
        let (x, uft) = annot_formula uft x in
        (HES.Diamond (a, x, p), uft)
    | HES.Abs ((x, p), t, y, q) ->
        let (t, uft) = UnionFind.reconstruct x p t uft in
        let (y, uft) = annot_formula uft y in
        (HES.Abs ((x, p), t, y, q), uft)
    | HES.App (l, r) ->
        let (l, uft) = annot_formula uft l in
        let (r, uft) = annot_formula uft r in
        (HES.App (l, r), uft)
    | HES.Mu ((x, p), t, y, q) ->
        let (t, uft) = UnionFind.reconstruct x p t uft in
        let (y, uft) = annot_formula uft y in
        (HES.Mu ((x, p), t, y, q), uft)
    | HES.Nu ((x, p), t, y, q) ->
        let (t, uft) = UnionFind.reconstruct x p t uft in
        let (y, uft) = annot_formula uft y in
        (HES.Nu ((x, p), t, y, q), uft)

let annot_eqs = fun uft eqs ->
    let f = fun (uft, reqs) eq ->
        let (fp, (x, p), t, body) = eq in
        let (t, uft) = UnionFind.reconstruct x p t uft in
        let (body, uft) = annot_formula uft body in
        let eq = (fp, (x, p), t, body) in
        let reqs = eq :: reqs in
        (uft, reqs)
    in
    let (_, reqs) = List.fold_left f (uft, []) eqs in
    List.rev reqs

let final_check = fun eqs ->
    let seq = List.hd eqs in
    let (_, (x, pos), t, _) = seq in
    if t = HES.Prop then eqs
    else begin
        let spos = Position.to_string pos in
        let st = HES.string_of_simple_type t in
        let so = HES.string_of_simple_type HES.Prop in
        let msg = spos ^ ":\n" ^
                  "Typing error: this expression has type " ^ st ^ ", " ^
                  "but an initial equation must have type " ^ so in
        Log.println 0 msg;
        exit 1
    end

let annot = fun eqs ->
    let cs = generate_constraints eqs in
    let uft = UnionFind.create_from_constraints cs in
    let eqs = annot_eqs uft eqs in
    final_check eqs
