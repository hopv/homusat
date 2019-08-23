(* log output *)

let println = fun level str ->
    if level <= !Flags.verbosity then print_endline str else ()

let prerrln = fun level str ->
    if level <= !Flags.verbosity then prerr_endline str else ()

let exec = fun level f ->
    if level <= !Flags.verbosity then f () else ()
