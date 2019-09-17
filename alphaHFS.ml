(* Alpha conversion for HFS *)

(* Substitution map *)
module Sub = Id.IdMap

let rec convert_formula = fun sub fml ->
    match fml with
    | HFS.Or (xs) -> HFS.Or (X.List.map (convert_formula sub) xs)
    | HFS.And (xs) -> HFS.And (X.List.map (convert_formula sub) xs)
    | HFS.Box (a, x) ->
        let x = convert_formula sub x in
        HFS.Box (a, x)
    | HFS.Diamond (a, x) ->
        let x = convert_formula sub x in
        HFS.Diamond (a, x)
    | HFS.App (x, ys) ->
        let x = Sub.find x sub in
        let ys = X.List.map (convert_formula sub) ys in
        HFS.App (x, ys)

let convert_func = fun sub func ->
    let f = fun (sub, rargs) (y, t) ->
        let y' = Id.gen y in
        let sub = Sub.add y y' sub in
        let rargs = (y', t) :: rargs in
        (sub, rargs)
    in
    let (fp, x, t, args, fml) = func in
    let (sub, rargs) = List.fold_left f (sub, []) args in
    let fml = convert_formula sub fml in
    let x = Sub.find x sub in
    let args = List.rev rargs in
    (fp, x, t, args, fml)

let initial_sub = fun funcs ->
    let f = fun acc func ->
        let (_, x, _, _, _) = func in
        let x' = Id.gen x in
        Sub.add x x' acc
    in
    List.fold_left f Sub.empty funcs

let rename = fun funcs ->
    let sub = initial_sub funcs in
    X.List.map (convert_func sub) funcs
