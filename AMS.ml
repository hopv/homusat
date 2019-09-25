(* All Maximal/Minimal Sets *)
(* http://www.bayardo.org/ps/sdm2011.pdf by Bayardo and Panda *)
(* https://arxiv.org/abs/1508.01753 by Marinov, Nash, and Gregg *)

(* The input is assumed to be given as an int list list, *)
(* where each int list is sorted and represents a set of integers *)

let print_iss = fun iss ->
    let f = fun is ->
        let ls = X.List.map string_of_int is in
        let str = String.concat "; " ls in
        "[" ^ str ^ "]"
    in
    let ls = X.List.map f iss in
    let str = String.concat "; " ls in
    print_endline ("[" ^ str ^ "]")

(* The lexicographic ordering on lists of integers *)
(* Probably the same as the standard compare function *)
let rec compare_int_lists = fun is1 is2 ->
    match (is1, is2) with
    | ([], []) -> 0
    | ([], _) -> -1
    | (_, []) ->  1
    | (i1 :: is1, i2 :: is2) ->
        if i1 < i2 then -1
        else if i2 < i1 then 1
        else compare_int_lists is1 is2

(* Check if is1 is a prefix of is2 *)
let rec is_prefix = fun is1 is2 ->
    match (is1, is2) with
    | ([], _) -> true
    | (_, []) -> false
    | (i1 :: is1, i2 :: is2) ->
        if i1 = i2 then is_prefix is1 is2
        else false

(* The input iss is assumed to be lexicographically ordered *)
let remove_all_prefixes = fun iss ->
    let rec f = fun iss acc ->
        match iss with
        | [] -> acc
        | [is] -> is :: acc
        | prev :: (succ :: iss) ->
            if is_prefix prev succ then
                f (succ :: iss) acc
            else f (succ :: iss) (prev :: acc)
    in
    List.rev (f iss [])

(* min.(i) := minimum size of iss.(i), ..., iss.(n - 1) *)
(* If min.(i) = |iss.(i)| then subsumption judgment can be skipped *)
let generate_mins = fun iss ->
    let rec f = fun iss i acc mins ->
        if i < 0 then mins
        else
            let n = Array.length iss.(i) in
            let acc = min acc n in
            mins.(i) <- acc;
            f iss (i - 1) acc mins
    in
    let n = Array.length iss in
    let mins = Array.make n 0 in
    f iss (n - 1) max_int mins

(* Convert int list list to int array array (for binary search) *)
let convert_to_arrays = fun iss ->
    Array.of_list (X.List.map Array.of_list iss)

(* Return the first i such that l < i <= r and cond i *)
(* # r is returned if no such i exists *)
let rec lower_bound = fun l r cond ->
    if r - 1 <= l then r
    else
        let c = (l + r) / 2 in
        if cond c then lower_bound l c cond
        else lower_bound c r cond

(* Return the last i such that l <= i < r and cond i *)
(* # l is returned if no such i exists *)
let rec upper_bound = fun l r cond ->
    if r - 1 <= l then l
    else
        let c = (l + r) / 2 in
        if cond c then upper_bound c r cond
        else upper_bound l c cond

(* Return the least i such that l <= i < r and v <= s.(i) *)
(* # r - 1 is returned if no such i exists *)
let next_item = fun s l r v ->
    let cond = fun s v i -> v <= s.(i) in
    lower_bound (l - 1) (r - 1) (cond s v)

(* Return the least i such that l < i <= r and v <= d.(i).(k) *)
(* # r is returned if no such i exists *)
let next_begin_range = fun d l r v k ->
    let cond = fun d v k i -> v <= d.(i).(k) in
    lower_bound l r (cond d v k)

(* Return the largest i such that l <= i <= r and d.(i).(k) <= v *)
let next_end_range = fun d l r v k ->
    let cond = fun d v k i -> d.(i).(k) <= v in
    upper_bound l (r + 1) (cond d v k)

(* Mark d.(b) as subsumed if b <= e and |d.(b)| = k *)
let rec mark = fun d b e k subsumed ->
    if b <= e && Array.length d.(b) = k then begin
        subsumed.(b) <- true;
        mark d (b + 1) e k subsumed
    end else (b, subsumed)

(* Mark all sets in d.(b..e).(k..) subsumed by s.(j..) *)
let rec mark_subsumed = fun d s n b e j k subsumed ->
    Profile.check_time_out "model checking" !Flags.time_out;
    if e < b then subsumed
    else
        let v = d.(b).(k) in
        let j = next_item s j n v in
        let w = s.(j) in
        if w < v then subsumed
        else if v < w then
            let b = next_begin_range d b e w k in
            if d.(b).(k) < w then subsumed
            else mark_subsumed d s n b e j k subsumed
        else (* v = w *)
            let e' = next_end_range d b e w k in
            let k' = k + 1 in
            let (b, subsumed) =
                if k' < n then mark d b e' k' subsumed
                else (b, subsumed)
            in
            let j' = j + 1 in
            let subsumed =
                if j' < n && b <= e' then
                    mark_subsumed d s n b e' j' k' subsumed
                else subsumed
            in
            mark_subsumed d s n (e' + 1) e j k subsumed

(* Iteratively mark all subsumed sets *)
let generate_subsumed = fun iss ->
    let rec loop = fun iss mins e i subsumed ->
        if e <= i then subsumed
        else if subsumed.(i) then
            loop iss mins e (i + 1) subsumed
        else
            let s = iss.(i) in
            let n = Array.length s in
            if n = mins.(i) then
                loop iss mins e (i + 1) subsumed
            else
                let subsumed =
                    mark_subsumed iss s n (i + 1) e 0 0 subsumed
                in
                loop iss mins e (i + 1) subsumed
    in
    let n = Array.length iss in
    let subsumed = Array.make n false in
    let mins = generate_mins iss in
    loop iss mins (n - 1) 0 subsumed

(* Gather all sets that are not marked as subsumed *)
let gather_maximal_sets = fun iss subsumed ->
    let rec loop = fun iss subsumed i acc ->
        if i < 0 then acc
        else if subsumed.(i) then
            loop iss subsumed (i - 1) acc
        else
            let is = Array.to_list iss.(i) in
            loop iss subsumed (i - 1) (is :: acc)
    in
    let n = Array.length iss in
    loop iss subsumed (n - 1) []

let all_maximal_sets = fun iss ->
    let iss = List.sort compare_int_lists iss in
    let iss = remove_all_prefixes iss in
    let iss = convert_to_arrays iss in
    let subsumed = generate_subsumed iss in
    gather_maximal_sets iss subsumed

(* The input iss is assumed to be lexicographically ordered *)
let remove_all_successors_of_prefixes = fun iss ->
    let rec f = fun iss acc ->
        match iss with
        | [] -> acc
        | [is] -> is :: acc
        | prev :: (succ :: iss) ->
            if is_prefix prev succ then
                f (prev :: iss) acc
            else f (succ :: iss) (prev :: acc)
    in
    List.rev (f iss [])

(* Check if s.(j..) subsumes some of d.(b..e).(k..) *)
let rec subsumes = fun d s n b e j k ->
    Profile.check_time_out "model checking" !Flags.time_out;
    if e < b then false
    else
        let v = d.(b).(k) in
        let j = next_item s j n v in
        let w = s.(j) in
        if w < v then false
        else if v < w then
            let b = next_begin_range d b e w k in
            if d.(b).(k) < w then false
            else subsumes d s n b e j k
        else (* v = w *)
            let e' = next_end_range d b e w k in
            let k' = k + 1 in
            if k' < n && Array.length d.(b) = k' then true
            else
                let j' = j + 1 in
                if j' < n then
                    if subsumes d s n b e' j' k' then true
                    else subsumes d s n (e' + 1) e j k
                else subsumes d s n (e' + 1) e j k

(* Iteratively mark all subsumed sets *)
let generate_is_minimal = fun iss ->
    let rec loop = fun iss mins e i is_minimal ->
        if e <= i then is_minimal
        else if is_minimal.(i) then
            let s = iss.(i) in
            let n = Array.length s in
            if n = mins.(i) then
                loop iss mins e (i + 1) is_minimal
            else if 0 < n then begin
                is_minimal.(i) <- not (subsumes iss s n (i + 1) e 0 0);
                loop iss mins e (i + 1) is_minimal
            end else loop iss mins e (i + 1) is_minimal
        else loop iss mins e (i + 1) is_minimal
    in
    let n = Array.length iss in
    let is_minimal = Array.make n true in
    let mins = generate_mins iss in
    loop iss mins (n - 1) 0 is_minimal

(* Gather all sets that are marked as minimal *)
let gather_minimal_sets = fun iss is_minimal ->
    let rec loop = fun iss is_minimal i acc ->
        if i < 0 then acc
        else if is_minimal.(i) then
            let is = Array.to_list iss.(i) in
            loop iss is_minimal (i - 1) (is :: acc)
        else loop iss is_minimal (i - 1) acc
    in
    let n = Array.length iss in
    loop iss is_minimal (n - 1) []

let all_minimal_sets = fun iss ->
    let iss = List.sort compare_int_lists iss in
    let iss = remove_all_successors_of_prefixes iss in
    let iss = convert_to_arrays iss in
    let is_minimal = generate_is_minimal iss in
    gather_minimal_sets iss is_minimal
