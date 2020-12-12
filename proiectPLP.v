Require Import String.
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.

Inductive eroareNat :=
| error_nat : eroareNat
| num : nat -> eroareNat.
Inductive eroareBool :=
| error_bool : eroareBool
| boolean : bool -> eroareBool.
Inductive eroareString :=
| error_str : eroareString
| str : string -> eroareString.

Inductive Values :=
| undecl : Values
| assign : Values
| naturals: nat -> Values
| booleans: bool -> Values
| strings : string -> Values.

Inductive AExp :=
| avar : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| aproc: AExp -> AExp -> AExp.
Inductive BExp :=
| bvar : string-> BExp
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp
| bequal : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.
Inductive SExp :=
| svar : string-> SExp
| sconc : string -> string -> SExp
| scmp : string -> string -> SExp
| scpy : string -> string -> SExp.
Inductive Stmt :=
| nat_decl : string -> Stmt
| nat_assig : string -> AExp -> Stmt
| nat_decl_assign : string -> AExp -> Stmt
| bool_decl : string -> Stmt
| bool_assig : string -> BExp -> Stmt
| bool_decl_assign : string -> BExp -> Stmt
| string_decl : string -> Stmt
| string_assig : string -> SExp -> Stmt
| string_decl_assign : string -> SExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifelse : BExp -> Stmt -> Stmt ->Stmt.



