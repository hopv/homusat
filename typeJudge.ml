(* type judgments for lhs variables *)

module Env = Id.IdMap
module Delta = LTS.Delta
module States = LTS.States
module FmlMap = ACG.FmlMap
module Tau = Types.Tau
module Sigma = Types.Sigma
module Gamma = Types.Gamma
module Theta = Types.Theta
module Epsilon = Types.Epsilon

exception Empty

let memo = ref Epsilon.empty
let reset_memo = fun () -> memo := Epsilon.empty

(* return the set of type environments under which fml has type tau *)
let rec type_envs = fun delta winning_nodes te fml tau ->
    Profile.check_time_out "model checking" !Flags.time_out;
    let tbl = Epsilon.find_default FmlMap.empty tau !memo in
    if FmlMap.mem fml tbl then FmlMap.find fml tbl
    else
        let ret = type_envs_without_memo delta winning_nodes te fml tau in
        let tbl = FmlMap.add fml ret tbl in
        memo := Epsilon.add tau tbl !memo;
        ret
and type_envs_without_memo = fun delta winning_nodes te fml tau ->
    match fml with
    | HFS.Or (xs) ->
        let f = fun delta winning_nodes te tau acc x ->
            let theta = type_envs delta winning_nodes te x tau in
            Theta.union theta acc
        in
        List.fold_left (f delta winning_nodes te tau) Theta.empty xs
    | HFS.And (xs) ->
        let f = fun delta winning_nodes te tau acc x ->
            if Theta.is_empty acc then acc
            else
                let theta = type_envs delta winning_nodes te x tau in
                Opt.prod_thetas theta acc
        in
        let f = f delta winning_nodes te tau in
        List.fold_left f (Theta.singleton Gamma.empty) xs
    | HFS.Box (a, x) ->
        let q = Types.codom tau in
        let f = fun delta winning_nodes te x p acc ->
            let tau = Tau.encode ([], p) in
            let theta = type_envs delta winning_nodes te x tau in
            if Theta.is_empty theta then raise Empty
            else Opt.prod_thetas theta acc
        in
        let ps = Delta.find_default States.empty (q, a) delta in
        begin try
            let seed = Theta.singleton Gamma.empty in
            States.fold (f delta winning_nodes te x) ps seed
        with Empty -> Theta.empty end
    | HFS.Diamond (a, x) ->
        let q = Types.codom tau in
        let f = fun delta winning_nodes te x p acc ->
            let tau = Tau.encode ([], p) in
            let theta = type_envs delta winning_nodes te x tau in
            Theta.union theta acc
            (* Opt.merge_thetas theta acc *)
        in
        let ps = Delta.find_default States.empty (q, a) delta in
        States.fold (f delta winning_nodes te x) ps Theta.empty
    | HFS.App (x, ys) ->
        let f = fun tau n tc -> tau = (Types.drop tc n) in
        let tcs = Env.find_default Sigma.empty x te in
        let tcs = Sigma.filter (f tau (List.length ys)) tcs in
        Sigma.fold (judge_app delta winning_nodes te x ys) tcs Theta.empty
and judge_app = fun delta winning_nodes te x ys tau acc ->
    let judge_tau = fun delta winning_nodes te y tau acc ->
        let theta = type_envs delta winning_nodes te y tau in
        if Theta.is_empty theta then raise Empty
        else Opt.prod_thetas theta acc
    in
    let judge_arg = fun delta winning_nodes te acc (y, sigma) ->
        let seed = Theta.singleton Gamma.empty in
        let f = judge_tau delta winning_nodes te y in
        let theta = Sigma.fold f sigma seed in
        Opt.prod_thetas theta acc
    in
    let gen_seed = fun winning_nodes x tau ->
        let sigma = Env.find_default Sigma.empty x winning_nodes in
        if Sigma.mem tau sigma then Theta.singleton Gamma.empty
        else Theta.singleton (Gamma.singleton x (Sigma.singleton tau))
    in
    try let ys = Types.annot ys tau in
        let seed = gen_seed winning_nodes x tau in
        let f = judge_arg delta winning_nodes te in
        let theta = List.fold_left f seed ys in
        Theta.union theta acc
        (* Opt.merge_thetas theta acc *)
    with Empty -> acc

module EnvMap = X.Map.Make (struct
    type t = Sigma.t Env.t
    let compare : t -> t -> int = Env.compare Sigma.compare
end)

let hoge = ref Env.empty
let reset_hoge = fun x -> hoge := Env.remove x !hoge

let type_envs = fun delta winning_nodes lhste rhste x fml tau ->
(*
    let te = Types.merge_gammas lhste rhste in
    type_envs delta winning_nodes te fml tau
*)
    let fuga = Env.find_default EnvMap.empty x !hoge in
    let piyo = EnvMap.find_default Epsilon.empty rhste fuga in
    if Epsilon.mem tau piyo then
        Epsilon.find tau piyo
    else
        let te = Types.merge_gammas lhste rhste in
        let ret = type_envs delta winning_nodes te fml tau in
        let piyo = Epsilon.add tau ret piyo in
        let fuga = EnvMap.add rhste piyo fuga in
        hoge := Env.add x fuga !hoge;
        ret
