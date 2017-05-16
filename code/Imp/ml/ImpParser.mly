%{

open ZUtil
open ImpSyntax

%}

%token TRUE
%token FALSE
%token <Big.big_int> INTLIT
%token <string> STRLIT

%token LEN
%token NOT
%token ADD
%token SUB
%token MUL
%token DIV
%token MOD
%token EQ
%token LT
%token LE
%token CONJ
%token DISJ

%token NOP
%token ASSIGN
%token ALLOC
%token SEMI
%token IF
%token ELSE
%token WHILE
%token DEF
%token RET

%token COMMA
%token LPAREN
%token RPAREN
%token LCURL
%token RCURL
%token LSQUARE
%token RSQUARE
%token EOF

%token <string> ID
%token <string> ANNO

%start file
%type <ImpSyntax.prog> file

/* TODO make sure these match python */
%right ANNO
%left DISJ
%left CONJ
%right EQ
%nonassoc LT LE
%left ADD SUB
%left MUL DIV MOD
%left NOT
%%

file :
  | funcs RET expr SEMI EOF
      { Prog ($1, Snop, $3) }
  | funcs stmt RET expr SEMI EOF
      { Prog ($1, $2, $4) }

funcs :
  | { [] }
  | func funcs
      { $1 :: $2 }

func :
  | DEF aID params LCURL RET expr SEMI RCURL
      { Func ($2, $3, Snop, $6) }
  | DEF aID params LCURL stmt RET expr SEMI RCURL
      { Func ($2, $3, $5, $7) }

params :
  | LPAREN RPAREN
      { [] }
  | LPAREN idlist RPAREN
      { $2 }

idlist :
  | aID
      { $1 :: [] }
  | aID COMMA idlist
      { $1 :: $3 }

args :
  | LPAREN RPAREN
      { [] }
  | LPAREN exprlist RPAREN
      { $2 }

exprlist :
  | expr
      { $1 :: [] }
  | expr COMMA exprlist
      { $1 :: $3 }

aID :
  | ID
    { Var (explode $1)}
  | ANNO ID
    { AnnoVar (explode $1, explode $2)}

anno:
    | ID ASSIGN ANNO
    { AnnoEq (explode $1, explode $3) }

anno_list:
    | anno
        { AnnoSt ($1) }
    | anno COMMA anno_list
        { AnnoSeq ($1, $3) }

anno_store:
  | LSQUARE anno_list RSQUARE
    { $2 }

stmt :
  | lstmt
      { $1 }
  | lstmt stmt
      { Sseq ($1, $2) }
  | anno_store stmt
      { AStmt ($1, $2)}

lstmt :
  | NOP SEMI
      { Snop }
(* Assignment *)
  | aID ASSIGN expr SEMI
      { Sset ($1, $3) }
  | aID ASSIGN ALLOC LPAREN expr COMMA expr RPAREN SEMI
      { Salloc ($1, $5, $7) }
  | aID LSQUARE expr RSQUARE ASSIGN expr SEMI
      { Swrite ($1, $3, $6) }
(* Function calls *)
  | aID ASSIGN aID args SEMI
      { Scall ($1, $3, $4) }
  | IF expr LCURL stmt RCURL
      { Sifelse ($2, $4, Snop) }
  | IF expr LCURL stmt RCURL ELSE LCURL stmt RCURL
      { Sifelse ($2, $4, $8) }
  | WHILE expr LCURL stmt RCURL
      { Swhile ($2, $4) }


bexpr :
  | TRUE
      { Eval (Vbool true) }
  | FALSE
      { Eval (Vbool false) }
  | INTLIT
      { Eval (Vint $1) }
  | STRLIT
      { Eval (Vstr (explode $1)) }
  | ID
      { Evar (explode $1) }
  | LEN LPAREN expr RPAREN
      { Elen $3 }
  | bexpr LSQUARE expr RSQUARE
      { Eidx ($1, $3) }
  | LPAREN expr RPAREN
      { $2 }

expr :
  | bexpr
      { $1 }
  (* Expressions can have an 'annotated type'*)
  | ANNO expr
      { Eanno (explode $1, $2) }
  | NOT expr
      { Eop1 (Onot, $2) }
  | SUB expr
      { Eop1 (Oneg, $2) }
  | binop
      { $1 }

binop :
  | expr ADD expr
      { Eop2 (Oadd, $1, $3) }
  | expr SUB expr
      { Eop2 (Osub, $1, $3) }
  | expr MUL expr
      { Eop2 (Omul, $1, $3) }
  | expr DIV expr
      { Eop2 (Odiv, $1, $3) }
  | expr MOD expr
      { Eop2 (Omod, $1, $3) }
  | expr EQ expr
      { Eop2 (Oeq, $1, $3) }
  | expr LT expr
      { Eop2 (Olt, $1, $3) }
  | expr LE expr
      { Eop2 (Ole, $1, $3) }
  | expr CONJ expr
      { Eop2 (Oconj, $1, $3) }
  | expr DISJ expr
      { Eop2 (Odisj, $1, $3) }

%%

