(* profiling *)

exception Time_out

val start_proc : string -> unit
val gettimeofproc : string -> float
val check_time_out : string -> float -> unit
val end_proc : string -> unit
val print_proc : int -> string -> unit
