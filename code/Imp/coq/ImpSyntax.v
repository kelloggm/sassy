Require Import String.
Require Import ZArith.

Inductive val : Type :=
| Vbool : bool -> val
| Vint  : Z -> val
| Vstr  : string -> val
| Vaddr : Z -> val.

Inductive op1 : Type :=
| Oneg
| Onot.

Inductive op2 : Type :=
| Oadd
| Osub
| Omul
| Odiv
| Omod
| Oeq
| Olt
| Ole
| Oconj
| Odisj.

Inductive var : Type :=
| Var : string -> var
| AnnoVar : string -> string -> var.

Inductive anno_mem : Type :=
| AnnoEq : string -> string -> anno_mem.

Inductive anno_store : Type :=
| AnnoSt : anno_mem -> anno_store
| AnnoSeq : anno_mem -> anno_store -> anno_store.

Inductive expr : Type :=
| Eval : val -> expr
| Evar : string -> expr
| Eop1 : op1 -> expr -> expr
| Eop2 : op2 -> expr -> expr -> expr
| Elen : expr -> expr
| Eidx : expr -> expr -> expr
| Eanno : string -> expr -> expr.

Definition store : Type :=
  list (string * val).

Definition heap : Type :=
  list val.

Inductive stmt : Type :=
| Snop : stmt
| Sset : var -> expr -> stmt
| Salloc : var -> expr -> expr -> stmt
| Swrite : var -> expr -> expr -> stmt
| Scall : var -> var -> list expr -> stmt
| Sifelse : expr -> stmt -> stmt -> stmt
| Swhile : expr -> stmt -> stmt
| Sseq : stmt -> stmt -> stmt
| AStmt : anno_store -> stmt -> stmt.

Inductive func : Type :=
| Func : var -> list var -> stmt -> expr -> func.

Inductive prog : Type :=
| Prog : list func -> stmt -> expr -> prog.
