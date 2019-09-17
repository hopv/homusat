%{
    let exit_with_parse_error = fun msg ->
        let pos = Position.get_parser_pos () in
        let spos = Position.to_string pos in
        let msg = spos ^ ":\n" ^ msg in
        Log.println 0 msg;
        exit 1
%}

%token <string> VAR
%token TRUE
%token FALSE
%token LOR
%token LAND
%token LAMBDA
%token ARROW
%token COLON
%token SEMICOLON
%token DOT
%token EQUAL_MU
%token EQUAL_NU
%token EQUAL
%token MU
%token NU
%token LESS
%token GREATER
%token LBRACK
%token RBRACK
%token LPAREN
%token RPAREN
%token COMMA
%token HES
%token LTS
%token INITIAL_STATE
%token TRANSITIONS
%token EOF

/* (* Priorities and associativities *) */
%right prec_lambda
%right ARROW
%left LOR
%left LAND
%nonassoc LAMBDA MU NU
%nonassoc VAR TRUE FALSE
%nonassoc LESS LPAREN LBRACK
%nonassoc prec_app
%right prec_modality

%start top
%type <HES.t * LTS.t> top
%%

top:
    | hes lts EOF
        { ($1, $2) }
    | lts hes EOF
        { ($2, $1) }
    | error
        { exit_with_parse_error "Parse error: failed to parse token" }
;

hes:
    | HES equations
        { $2 }
;

lts:
    | LTS transitions
        { LTS.of_transitions None $2 }
    | LTS
        { LTS.of_transitions None [] }
    | LTS DOT
        { LTS.of_transitions None [] }
    | LTS INITIAL_STATE VAR TRANSITIONS transitions
        { let q0 = LTS.state_of_string $3 in
          LTS.of_transitions (Some (q0)) $5 }
    | LTS INITIAL_STATE VAR TRANSITIONS
        { let q0 = LTS.state_of_string $3 in
          LTS.of_transitions (Some (q0)) [] }
    | LTS INITIAL_STATE VAR TRANSITIONS DOT
        { let q0 = LTS.state_of_string $3 in
          LTS.of_transitions (Some (q0)) [] }

/* (* A variable augmented with positional information *) */
variable:
    | VAR
        { (Id.of_string $1, Position.get_parser_pos ()) }
;

equations:
    | equation SEMICOLON equations
        { $1 :: $3 }
    | equation SEMICOLON
        { [$1] }
    | equation
        { [$1] }
;

equation:
    | variable COLON simple_type EQUAL_MU formula
        { (HES.Mu, $1, $3, $5) }
    | variable COLON simple_type EQUAL_NU formula
        { (HES.Nu, $1, $3, $5) }
    | variable COLON simple_type EQUAL formula
        { (HES.Nu, $1, $3, $5) }
    | variable EQUAL_MU formula
        { (HES.Mu, $1, HES.gen_type (), $3) }
    | variable EQUAL_NU formula
        { (HES.Nu, $1, HES.gen_type (), $3) }
    | variable EQUAL formula
        { (HES.Nu, $1, HES.gen_type (), $3) }
;

term:
    | variable
        { let (x, pos) = $1 in HES.Var (x, pos) }
    | TRUE
        { HES.True (Position.get_parser_pos ()) }
    | FALSE
        { HES.False (Position.get_parser_pos ()) }
    | LPAREN formula RPAREN
        { $2 }
;

formula:
    | term
        { $1 }
    | formula LOR formula
        { HES.Or ($1, $3) }
    | formula LAND formula
        { HES.And ($1, $3) }
    | LBRACK VAR RBRACK formula
        %prec prec_modality
        { let pos = Position.get_parser_pos () in
          HES.Box (LTS.label_of_string $2, $4, pos) }
    | LESS VAR GREATER formula
        %prec prec_modality
        { let pos = Position.get_parser_pos () in
          HES.Diamond (LTS.label_of_string $2, $4, pos) }
    | formula formula
        %prec prec_app
        { HES.App ($1, $2) }
    | LAMBDA variable COLON simple_type DOT formula
        %prec prec_lambda
        { let pos = Position.get_parser_pos () in
          HES.Abs ($2, $4, $6, pos) }
    | MU variable COLON simple_type DOT formula
        %prec prec_lambda
        { let pos = Position.get_parser_pos () in
          HES.Mu ($2, $4, $6, pos) }
    | NU variable COLON simple_type DOT formula
        %prec prec_lambda
        { let pos = Position.get_parser_pos () in
          HES.Nu ($2, $4, $6, pos) }
    | LAMBDA variable DOT formula
        %prec prec_lambda
        { let pos = Position.get_parser_pos () in
          HES.Abs ($2, HES.gen_type (), $4, pos) }
    | MU variable DOT formula
        %prec prec_lambda
        { let pos = Position.get_parser_pos () in
          HES.Mu ($2, HES.gen_type (), $4, pos) }
    | NU variable DOT formula
        %prec prec_lambda
        { let pos = Position.get_parser_pos () in
          HES.Nu ($2, HES.gen_type (), $4, pos) }
;

base_type:
    | VAR
        { match $1 with
          | "o" -> HES.Prop
          | _ ->
              let so = HES.string_of_simple_type HES.Prop in
              let msg = "Parse error: base type must be written as " ^
                        "'" ^ so ^ "'" in
              exit_with_parse_error msg }
    | LPAREN simple_type RPAREN
        { $2 }
;

simple_type:
    | base_type
        { $1 }
    | simple_type ARROW simple_type
        { HES.Arrow ($1, $3) }
;

transitions:
    | transition DOT transitions
        { $1 :: $3 }
    | transition DOT
        { [$1] }
    | transition
        { [$1] }
;

transition:
    | VAR VAR ARROW VAR
        { let x = LTS.state_of_string $1 in
          let a = LTS.label_of_string $2 in
          let y = LTS.state_of_string $4 in
          (x, a, y) }
;
