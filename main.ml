let parse = fun srcpath in_channel ->
    let lexbuf = Lexing.from_channel in_channel in
    Lexer.init_lexbuf lexbuf srcpath;
    let top = Parser.top Lexer.token lexbuf in
    close_in in_channel;
    top

let solve = fun srcpath ->
    try
        Profile.start_proc "elapsed";
        Profile.start_proc "parsing";
        let in_channel = if srcpath = "" then begin
            Log.println 0 "input file: stdin";
            stdin
        end else begin
            Log.println 0 ("input file: \"" ^ srcpath ^ "\"");
            open_in srcpath
        end in
        let (hes, lts) = parse srcpath in_channel in
        Profile.end_proc "parsing";
        Profile.print_proc 1 "parsing";
        Log.exec 2 (fun () ->
            print_endline ("%HES\n" ^ (HES.to_string hes)));
        Log.exec 2 (fun () ->
            print_endline ("%LTS\n" ^ (LTS.to_string lts)));
        Profile.start_proc "type reconstruction";
        let hes = AlphaHES.rename hes in
        let hes = Typing.annot hes in
        Profile.end_proc "type reconstruction";
        Profile.print_proc 1 "type reconstruction";
        Log.exec 2 (fun () ->
            print_endline ("%TYPED\n" ^ (HES.to_string hes)));
        Profile.start_proc "normalization";
        let hfs = Norm.normalize hes in
        Profile.end_proc "normalization";
        Profile.print_proc 1 "normalization";
        Log.exec 2 (fun () ->
            print_endline ("%NORMALIZED\n" ^ (HFS.to_string hfs)));
        Log.exec 0 (fun () ->
            Profile.start_proc "analysis";
            Analysis.analyze hfs lts;
            Profile.end_proc "analysis";
            Profile.print_proc 1 "analysis");
        Profile.start_proc "model checking";
        Profile.start_proc "reduction";
        let hfs = Reduction.reduce hfs in
        Profile.end_proc "reduction";
        Profile.print_proc 1 "reduction";
        Log.exec 2 (fun () ->
            print_endline ("%REDUCED\n" ^ (HFS.to_string hfs)));
        Profile.start_proc "preprocess";
        let (kernels, dep_kernels) = Preproc.generate_kernels hfs in
        (* let (hfs, kernels) = Preproc.approx hfs in *)
        Profile.end_proc "preprocess";
        Profile.print_proc 1 "preprocess";
        Log.exec 2 (fun () ->
            print_endline ("%PREPROCESSED\n" ^ (HFS.to_string hfs)));
        Profile.start_proc "flow calculation";
        let enc = Enc.encode hfs in
        let flow_info = Flow.generate_flow_info enc lts in
        Profile.end_proc "flow calculation";
        Profile.print_proc 1 "flow calculation";
        Log.exec 2 (fun () ->
            print_endline "%FLOWS"; Flow.print flow_info);
        Profile.start_proc "saturation loop";
        let tj =
            Saturation.saturate enc lts kernels dep_kernels flow_info
        in
        Profile.end_proc "saturation loop";
        Profile.print_proc 1 "saturation loop";
        Profile.start_proc "parity game solving";
        let satisfied = Solver.solve hfs lts tj in
        Profile.end_proc "parity game solving";
        Profile.print_proc 1 "parity game solving";
        Profile.end_proc "model checking";
        Profile.print_proc 0 "model checking";
        let res = if satisfied then "satisfied" else "unsatisfied" in
        Log.println 0 ("result: " ^ res);
        Profile.end_proc "elapsed";
        Profile.print_proc 1 "elapsed"
    with
    | Profile.Time_out -> Log.println 0 "result: time-out"
    | Saturation.Over_loop -> Log.println 0 "result: over-loop"

let srcpath = ref ""
let args = [
    ("-d", Arg.Set Flags.debug_mode,
     "Enable debug mode");
    ("-n", Arg.Set Flags.noopt_mode,
     "Disable optimizations");
    ("-m", Arg.Set Flags.muker_mode,
     "Axiomatize mu kernels");
    ("-v", Arg.Int (fun n -> Flags.verbosity := n),
     "[n] Set verbosity level");
    ("-f", Arg.String (fun s -> srcpath := s),
     "[s] Set source file path");
    ("-t", Arg.Float (fun t -> Flags.time_out := t),
     "[f] Set time-out (seconds)");
    ("-l", Arg.Int (fun n -> Flags.max_loops := n),
     "[n] Set maximum loop count for saturation");
]
let usage_msg = "HomuSat: A type-based HFL model cheker"
let ignore = fun s ->
    let msg = "Warning: unrecognizable argument '" ^ s ^ "' is ignored" in
    Log.prerrln 0 msg

(* main entrance *)
let _ =
    Arg.parse args ignore usage_msg;
    solve !srcpath
