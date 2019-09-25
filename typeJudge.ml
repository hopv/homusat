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

let memo = ref FmlMap.empty
let reset_memo = fun () -> memo := FmlMap.empty

(* return the set of type environments under which fml has type tau *)
let rec type_envs = fun delta winning_nodes te fml tau ->
    Profile.check_time_out "model checking" !Flags.time_out;
    let tbl = FmlMap.find_default Epsilon.empty fml !memo in
    if Epsilon.mem tau tbl then Epsilon.find tau tbl
    else
        let ret = type_envs_without_memo delta winning_nodes te fml tau in
        let tbl = Epsilon.add tau ret tbl in
        memo := FmlMap.add fml tbl !memo;
        ret
and type_envs_without_memo = fun delta winning_nodes te fml tau ->
    match Enc.decode fml with
    | Enc.Or (xs) ->
        let f = fun delta winning_nodes te tau x ->
            type_envs delta winning_nodes te x tau
        in
        let thetas = List.rev_map (f delta winning_nodes te tau) xs in
        (* List.fold_left Theta.union Theta.empty thetas *)
        List.fold_left Opt.merge_thetas Theta.empty thetas
    | Enc.And (xs) ->
        let f = fun delta winning_nodes te tau x ->
            let theta = type_envs delta winning_nodes te x tau in
            if Theta.is_empty theta then raise Empty else theta
        in
        begin try
            let thetas = List.rev_map (f delta winning_nodes te tau) xs in
            let seed = Theta.singleton Gamma.empty in
            List.fold_left Opt.prod_thetas seed thetas
        with Empty -> Theta.empty end
    | Enc.Box (a, x) ->
        let f = fun delta winning_nodes te x q ->
            let tau = Tau.encode ([], q) in
            let theta = type_envs delta winning_nodes te x tau in
            if Theta.is_empty theta then raise Empty else theta
        in
        let q = Types.codom tau in
        let ps = Delta.find_default States.empty (q, a) delta in
        let ps = States.elements ps in
        begin try
            let thetas = List.rev_map (f delta winning_nodes te x) ps in
            let seed = Theta.singleton Gamma.empty in
            List.fold_left Opt.prod_thetas seed thetas
        with Empty -> Theta.empty end
    | Enc.Diamond (a, x) ->
        let f = fun delta winning_nodes te x q ->
            let tau = Tau.encode ([], q) in
            type_envs delta winning_nodes te x tau
        in
        let q = Types.codom tau in
        let ps = Delta.find_default States.empty (q, a) delta in
        let ps = States.elements ps in
        let thetas = List.rev_map (f delta winning_nodes te x) ps in
        (* List.fold_left Theta.union Theta.empty thetas *)
        List.fold_left Opt.merge_thetas Theta.empty thetas
    | Enc.App (x, ys) ->
        let f = fun tau n tc -> tau = Types.drop_tau tc n in
        let tcs = Env.find_default Sigma.empty x te in
        let tcs = Sigma.filter (f tau (List.length ys)) tcs in
        Sigma.fold (judge_app delta winning_nodes te x ys) tcs Theta.empty
and judge_app = fun delta winning_nodes te x ys tau acc ->
    let judge_tau = fun delta winning_nodes te y tau ->
        let theta = type_envs delta winning_nodes te y tau in
        if Theta.is_empty theta then raise Empty else theta
    in
    let judge_arg = fun delta winning_nodes te y sigma ->
        let f = judge_tau delta winning_nodes te y in
        let taus = Sigma.elements sigma in
        let thetas = List.rev_map f taus in
        let seed = Theta.singleton Gamma.empty in
        List.fold_left Opt.prod_thetas seed thetas
    in
    let gen_seed = fun winning_nodes x tau ->
        let sigma = Env.find_default Sigma.empty x winning_nodes in
        if Sigma.mem tau sigma then Theta.singleton Gamma.empty
        else Theta.singleton (Gamma.singleton x (Sigma.singleton tau))
    in
    try let sigmas = Types.drop_sigmas tau (List.length ys) in
        let f = judge_arg delta winning_nodes te in
        let thetas = List.rev_map2 f ys sigmas in
        let seed = gen_seed winning_nodes x tau in
        let theta = List.fold_left Opt.prod_thetas seed thetas in
        (* Theta.union acc theta *)
        Opt.merge_thetas acc theta
    with Empty -> acc

module EnvMap = X.Map.Make (struct
    type t = Sigma.t Env.t
    let compare : t -> t -> int = Env.compare Sigma.compare
end)

let hoge = ref Env.empty
let reset_hoge = fun x -> hoge := Env.remove x !hoge

let cnt = ref 0

let type_envs = fun delta winning_nodes lhste rhste x fml tau ->
(*
    let te = Types.merge_gammas lhste rhste in
    type_envs delta winning_nodes te fml tau
*)
    let fuga = Env.find_default EnvMap.empty x !hoge in
    let piyo = EnvMap.find_default Epsilon.empty rhste fuga in
    if Epsilon.mem tau piyo then
        (* let _ = cnt := !cnt + 1; print_endline (string_of_int !cnt) in *)
        Epsilon.find tau piyo
    else
        let te = Types.merge_gammas lhste rhste in
        let ret = type_envs delta winning_nodes te fml tau in
        let piyo = Epsilon.add tau ret piyo in
        let fuga = EnvMap.add rhste piyo fuga in
        hoge := Env.add x fuga !hoge;
        ret
