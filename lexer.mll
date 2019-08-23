{
    open Parser

    (* set file name *)
    let init_lexbuf = fun lexbuf filename ->
        let tmp = lexbuf.Lexing.lex_curr_p in
        lexbuf.Lexing.lex_curr_p <- { tmp with Lexing.pos_fname = filename }

    let exit_with_lexing_error = fun lexbuf msg ->
        let pos = Position.get_lexer_pos lexbuf in
        let spos = Position.to_string pos in
        let msg = spos ^ ":\n" ^ msg in
        Log.println 0 msg;
        exit 1
}

let newline = '\n'
let space = [' ' '\t' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']
let bar = '|'
let amper = '&'
let sharp = '#'
let slash = '/'
let prime = '\''
let atmark = '@'
let dollar = '$'
let underscore = '_'
let letter = (lower|upper)
let pred = (letter|bar|amper|atmark|dollar)
let succ = (pred|digit|prime|underscore|sharp|slash)

rule token = parse
    | space+           { token lexbuf }
    | newline          { Lexing.new_line lexbuf; token lexbuf }
    | "/*"             { comment_out lexbuf; token lexbuf }
    | "//"             { comment_out_single_line lexbuf; token lexbuf }
    | "\\true"         { TRUE }
    | "\\false"        { FALSE }
    | "\\lor"          { LOR }
    | "\\land"         { LAND }
    | "\\lambda"       { LAMBDA }
    | "->"             { ARROW }
    | ':'              { COLON }
    | ';'              { SEMICOLON }
    | '.'              { DOT }
    | "=_\\mu"         { EQUAL_MU }
    | "=_\\nu"         { EQUAL_NU }
    | '='              { EQUAL }
    | "\\mu"           { MU }
    | "\\nu"           { NU }
    | '<'              { LESS }
    | '>'              { GREATER }
    | '['              { LBRACK }
    | ']'              { RBRACK }
    | '('              { LPAREN }
    | ')'              { RPAREN }
    | ','              { COMMA }
    | "%HES"           { HES }
    | "%LTS"           { LTS }
    | "initial state:" { INITIAL_STATE }
    | "transitions:"   { TRANSITIONS }
    | eof              { EOF }
    | pred succ* as id { VAR id }
    | _ { let msg = "Lexing error: unknown token '" ^
                    (Lexing.lexeme lexbuf) ^ "'" in
          exit_with_lexing_error lexbuf msg }
and comment_out = parse
    | "*/"    { () }
    | "/*"    { comment_out lexbuf; comment_out lexbuf }
    | newline { Lexing.new_line lexbuf; comment_out lexbuf }
    | eof     { Log.prerrln 0 "Warning: unterminated comment" }
    | _       { comment_out lexbuf }
and comment_out_single_line = parse
    | newline { Lexing.new_line lexbuf }
    | _ { comment_out_single_line lexbuf }
