(* profiling *)

exception Time_out

module Timer = Map.Make (String)
let timer = ref Timer.empty

let start_proc = fun key ->
    let s = Unix.gettimeofday () in
    timer := Timer.add key s !timer

let gettimeofproc = fun key ->
    Timer.find key !timer

let check_time_out = fun key time_out ->
    let t = Unix.gettimeofday () in
    let s = gettimeofproc key in
    let elapsed = t -. s in
    if time_out <= elapsed then begin
        let msg = "Warning: " ^ (string_of_float elapsed) ^ " seconds " ^
                  "have passed since the process '" ^ key ^ "' started" in
        Log.prerrln 0 msg;
        raise Time_out
    end else ()

let end_proc = fun key ->
    let t = Unix.gettimeofday () in
    let s = gettimeofproc key in
    let elapsed = t -. s in
    timer := Timer.add key elapsed !timer

let print_proc = fun level key ->
    Log.exec level (fun () ->
        let elapsed = gettimeofproc key in
        print_endline (key ^ ": " ^ (string_of_float elapsed) ^ " sec"))
