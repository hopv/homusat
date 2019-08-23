(* Labeled Transition System *)

(* states and labels *)
type state = int
type label = Id.t

(* transitions *)
type transition = state * label * state

module States = Set.Make (struct
    type t = state
    let compare : t -> t -> int = compare
end)
module Actions = Set.Make (struct
    type t = label
    let compare : t -> t -> int = compare
end)
module Delta = X.Map.Make (struct
    type t = state * label
    let compare : t -> t -> int =
        fun (s1, a1) (s2, a2) ->
        let cs = compare s1 s2 in
        if cs = 0 then compare a1 a2
        else cs
end)

(* for states *)
module OfStr = X.Map.Make (String)
module ToStr = X.Map.Make (struct
    type t = int
    let compare : t -> t -> int = compare
end)

let counter = ref 0
let of_str = ref OfStr.empty
let to_str = ref ToStr.empty

(* unique identifier for the given string *)
let state_of_string = fun str ->
    if OfStr.mem str !of_str then
        OfStr.find str !of_str
    else begin
        let id = !counter in
        of_str := OfStr.add str id !of_str;
        to_str := ToStr.add id str !to_str;
        counter := !counter + 1;
        id
    end
let label_of_string = Id.of_string

let string_of_state = fun id ->
    if !Flags.debug_mode then
        (ToStr.find id !to_str) ^ "." ^ (string_of_int id)
    else
        ToStr.find id !to_str
let string_of_label = Id.to_string

(* LTS: (Q, A, \delta, q_{0}) *)
type t = States.t * Actions.t * (States.t Delta.t) * state

(* empty LTS *)
let empty = fun q0 ->
    let q0 = match q0 with Some (q0) -> q0 | _ -> state_of_string "q" in
    let states = States.singleton q0 in
    let actions = Actions.empty in
    let delta = Delta.empty in
    (states, actions, delta, q0)

let add_transition = fun s a t delta ->
    let ts = Delta.find_default States.empty (s, a) delta in
    Delta.add (s, a) (States.add t ts) delta

let of_transitions = fun q0 ls ->
    let f = fun (states, actions, delta) (s, a, t) ->
        let states = States.add t (States.add s states) in
        let actions = Actions.add a actions in
        let delta = add_transition s a t delta in
        (states, actions, delta)
    in
    match ls with
    | [] -> empty q0
    | (q, _, _) :: _ ->
        let seed = (States.empty, Actions.empty, Delta.empty) in
        let (states, actions, delta) = List.fold_left f seed ls in
        let q0 = match q0 with Some (q0) -> q0 | None -> q in
        (states, actions, delta, q0)

let to_string = fun (_, _, delta, q0) ->
    let f = fun (s, a) ts acc ->
        let g = fun ss sa t acc ->
            let st = string_of_state t in
            let str = ss ^ " " ^ sa ^ " -> " ^ st in
            str :: acc
        in
        let ss = string_of_state s in
        let sa = string_of_label a in
        States.fold (g ss sa) ts acc
    in
    let init = "initial state: " ^ (string_of_state q0) in
    let ls = Delta.fold f delta [] in
    let trans = String.concat ".\n" (List.rev ls) in
    let trans = "transitions:\n" ^ trans ^ "." in
    init ^ "\n" ^ trans
