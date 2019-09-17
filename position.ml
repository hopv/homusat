(* Positional information (used for pretty error printing) *)

type t = Lexing.position * Lexing.position

let get_file_name = fun pos -> pos.Lexing.pos_fname

let get_line_num = fun pos -> pos.Lexing.pos_lnum

let get_line_pos = fun pos ->
    let cnum = pos.Lexing.pos_cnum in
    let bol = pos.Lexing.pos_bol in
    cnum - bol

let get_parser_pos = fun () ->
    (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())

let get_lexer_pos = fun lexbuf ->
    (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)

let compose = fun (ls, lt) (rs, rt) -> (ls, rt)

let to_string : t -> string =
    fun (start_pos, end_pos) ->
    let sf = get_file_name start_pos in
    let sl = get_line_num start_pos in
    let sp = get_line_pos start_pos + 1 in
    let el = get_line_num end_pos in
    let ep = get_line_pos end_pos in
    let ssl = string_of_int sl in
    let ssp = string_of_int sp in
    let sep = string_of_int ep in
    let sf = if sf = "" then "Input" else "File \"" ^ sf ^ "\"," in
    if sl = el then
        if ep <= sp then sf ^ " line " ^ ssl ^ ", character " ^ sep
        else sf ^ " line " ^ ssl ^ ", characters " ^ ssp ^ "-" ^ sep
    else
        let sel = string_of_int el in
        sf ^ " from line " ^ ssl ^ ", character " ^ ssp ^
        " to line " ^ sel ^ ", character " ^ sep
