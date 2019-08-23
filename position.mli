(* positional information *)

type t

val get_parser_pos : unit -> t
val get_lexer_pos : Lexing.lexbuf -> t
val compose : t -> t -> t
val to_string : t -> string
