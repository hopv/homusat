(* alpha conversion for HES *)

(* substitution map *)
module Sub = Id.IdMap

let exit_with_unbound_var_error = fun x pos ->
    let sx = Id.to_string x in
    let spos = Position.to_string pos in
    let msg = spos ^ ":\n" ^
              "Error: unbound variable '" ^ sx ^ "'" in
    Log.println 0 msg;
    exit 1

let rec convert_formula = fun sub fml ->
    match fml with
    | HES.True (_)
    | HES.False (_) -> fml
    | HES.Var (x, pos) ->
        if Sub.mem x sub then
            HES.Var (Sub.find x sub, pos)
        else exit_with_unbound_var_error x pos
    | HES.Or (l, r) ->
        let l = convert_formula sub l in
        let r = convert_formula sub r in
        HES.Or (l, r)
    | HES.And (l, r) ->
        let l = convert_formula sub l in
        let r = convert_formula sub r in
        HES.And (l, r)
    | HES.Box (a, x, pos) ->
        let x = convert_formula sub x in
        HES.Box (a, x, pos)
    | HES.Diamond (a, x, pos) ->
        let x = convert_formula sub x in
        HES.Diamond (a, x, pos)
    | HES.App (l, r) ->
        let l = convert_formula sub l in
        let r = convert_formula sub r in
        HES.App (l, r)
    | HES.Abs ((x, p), t, body, q) ->
        let x' = Id.gen x in
        let sub = Sub.add x x' sub in
        let body = convert_formula sub body in
        HES.Abs ((x', p), t, body, q)
    | HES.Mu ((x, p), t, body, q) ->
        let x' = Id.gen x in
        let sub = Sub.add x x' sub in
        let body = convert_formula sub body in
        HES.Mu ((x', p), t, body, q)
    | HES.Nu ((x, p), t, body, q) ->
        let x' = Id.gen x in
        let sub = Sub.add x x' sub in
        let body = convert_formula sub body in
        HES.Nu ((x', p), t, body, q)

let convert_eq = fun sub eq ->
    let (fp, (x, pos), t, fml) = eq in
    let fml = convert_formula sub fml in
    (fp, (Sub.find x sub, pos), t, fml)

let exit_with_multiple_defs_error = fun x pos ->
    let sx = Id.to_string x in
    let spos = Position.to_string pos in
    let msg = spos ^ ":\n" ^
              "Error: left-hand side variable '" ^ sx ^
              "' is defined multiple times" in
    Log.println 0 msg;
    exit 1

let initial_sub = fun eqs ->
    let f = fun sub eq ->
        let (_, (x, pos), _, _) = eq in
        if Sub.mem x sub then
            exit_with_multiple_defs_error x pos
        else
            let x' = Id.gen x in
            Sub.add x x' sub
    in
    List.fold_left f Sub.empty eqs

let rename = fun eqs ->
    let sub = initial_sub eqs in
    List.rev (List.rev_map (convert_eq sub) eqs)
