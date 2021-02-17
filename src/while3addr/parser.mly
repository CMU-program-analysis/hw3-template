%{
open Core
open Lang

%}

%token <string>         IDENTIFIER
%token <int>            POSITIVE
%token                  ZERO
%token <int>            INT

%token PLUS
%token MINUS
%token TIMES
%token DIV
%token COLON
%token EQ_TOK
%token LT_TOK
%token GOTO
%token SET
%token IF
%token PRINT
%token HALT

%token EOF

%start listing
%type <Lang.listing> listing

%nonassoc PLUS MINUS TIMES DIV EQ_TOK LT_TOK

%%

opr:
  | EQ_TOK                                   { EQ }
  | LT_TOK                                   { LT }

op:
  | PLUS                                     { Add }
  | MINUS                                    { Sub }
  | TIMES                                    { Mul }
  | DIV                                      { Div }

const:
  | POSITIVE                                 { $1 }
  | ZERO                                     { 0 }
  | INT                                      { $1 }

location:
  | POSITIVE { $1 }

stmt:
  | IDENTIFIER SET const                      { ConstAssign ($1, $3) }
  | IDENTIFIER SET IDENTIFIER                 { VarAssign ($1, $3) }
  | IDENTIFIER SET IDENTIFIER op IDENTIFIER   { OpAssign ($1, $3, $5, $4) }
  | GOTO location                             { Goto $2 }
  | IF IDENTIFIER opr ZERO GOTO location      { IfGoto ($2, $3, $6) }
  | PRINT IDENTIFIER                          { Print $2 }
  | HALT                                      { Halt }

insn:
  | location COLON stmt                       { $1, $3 }
;

listing:
  | insn              { let location, stmt = $1 in
                        Int.Map.add_exn Int.Map.empty ~key:location ~data:stmt }
  | insn listing      { let listing = $2 in
                        let location, stmt = $1 in
                        Int.Map.add_exn listing ~key:location ~data:stmt }
;
