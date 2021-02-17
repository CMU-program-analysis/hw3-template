%{
open Lang

%}

%token <string>         IDENTIFIER
%token <int>            INT

%token PLUS
%token MINUS
%token TIMES
%token DIV
%token MOD
%token TRUE
%token FALSE
%token EQ_TOK
%token LT_TOK
%token LEQ_TOK
%token GT_TOK
%token GEQ_TOK
%token NOT
%token AND
%token OR
%token SKIP
%token SET
%token SEMICOLON
%token IF
%token THEN
%token ELSE
%token WHILE
%token DO
%token LET
%token IN
%token PRINT
%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE

%token EOF

%start program
%type <Lang.stmt> program

%left AND
%left OR
%left PLUS MINUS
%left TIMES DIV
%left LEQ_TOK LT_TOK EQ_TOK GT_TOK GEQ_TOK
%nonassoc NOT

%%

aexp : INT                                   { Num($1) }
| IDENTIFIER                                 { Var($1) }
| aexp PLUS aexp                             { Add ($1,$3) }
| aexp MINUS aexp                            { Sub ($1,$3) }
| aexp TIMES aexp                            { Mul ($1,$3) }
| aexp DIV aexp                              { Div ($1,$3) }
| LPAREN aexp RPAREN                         { $2 }
;

bexp : TRUE                                  { True }
| FALSE                                      { False }
| aexp LT_TOK aexp                           { LT($1,$3) }
| aexp LEQ_TOK aexp                          { LEQ ($1,$3) }
| aexp EQ_TOK aexp                           { EQ ($1,$3) }
| aexp GT_TOK aexp                           { GT($1,$3) }
| aexp GEQ_TOK aexp                          { GEQ ($1,$3) }
| NOT bexp                                   { Not($2) }
| bexp AND bexp                              { And($1,$3)  }
| bexp OR bexp                               { Or($1,$3) }
| LPAREN bexp RPAREN                         { $2 }
;

program : sequence                           { $1 }

sequence : stmt SEMICOLON sequence           { Seq($1,$3) }
| stmt                                       { $1 }

stmt : SKIP                                  { Skip }
| IDENTIFIER SET aexp                        { Assign($1,$3) }
| IF bexp THEN sequence ELSE stmt            { If($2,$4,$6) }
| WHILE bexp DO stmt                         { While($2,$4) }
| LET IDENTIFIER EQ_TOK aexp IN stmt         { Let($2,$4,$6) }
| LBRACE sequence RBRACE                     { $2 }
| PRINT aexp                                 { Print($2) }
;
