Require Import String.
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.
Local Open Scope list_scope.
Require Import List.
Import ListNotations.

Inductive eroareNat :=
| error_nat : eroareNat
| num : nat -> eroareNat.
Inductive eroareBool :=
| error_bool : eroareBool
| boolean : bool -> eroareBool.

Inductive AExp :=
| avar : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| adiv : AExp -> AExp -> AExp
| aproc: AExp -> AExp -> AExp.
Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp
| bequal : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

Definition Parametrii := list string.
Inductive Stmt :=
| nat_decl : string -> Stmt
| nat_assign : string -> AExp -> Stmt
| nat_decl_assign : string -> AExp -> Stmt
| bool_decl : string -> Stmt
| bool_assign : string -> BExp -> Stmt
| bool_decl_assign : string -> BExp -> Stmt
| apelare_functie : string -> Parametrii -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifelse : BExp -> Stmt -> Stmt ->Stmt
| lambda : string -> Parametrii -> Parametrii -> Stmt -> Stmt.

Inductive Values :=
| undecl : Values
| assign : Values
| default : Values
| naturals: nat -> Values
| booleans: bool -> Values
| code : Stmt -> Values.
Inductive Programs :=
| decl_functie : string -> Parametrii -> Stmt -> Programs
| decl_var_globale: string -> Programs
| decl_var_locale: string -> Programs
| decl_functie_main : Stmt -> Programs
| sequance_program : Programs -> Programs -> Programs
| decl_templates : string -> Programs.
Inductive Memory :=
  | mem_default : Memory
  | offset : nat -> Memory.
Definition Env := string -> Memory.
Definition MemLayer := Memory -> Values.
Definition Stack := list Env.
Inductive Config :=
  | config : nat -> Env -> MemLayer -> Stack -> Config.
Inductive Coada :=
| nil : Coada
| elem : nat -> Coada -> Coada.
Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.

Notation "A +' B" := (aplus A B) (at level 48).
Notation "A ++' " := (aplus A 1) (at level 48).
Notation "A -' B" := (aminus A B) (at level 48).
Notation "A --' " := (aminus A 1) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A /' B" := (adiv A B) (at level 58).
Notation "A %' B" := (aproc A B) (at level 58).
Notation "A <=' B" := (blessthan A B) (at level 53).
Notation "A =>' B" := (bgreaterthan A B) (at level 53).
Notation "A ==' B" := (bequal A B) (at level 53).
Notation " !' A" := (bnot A) (at level 53).
Notation "A &' B" := (band A B) (at level 53).
Notation "A |' B" := (bor A B) (at level 53).
Notation " 'int' A " := (nat_decl A) (at level 50).
Notation " X ':n=' A  " := (nat_assign X A) (at level 50).
Notation " 'int*' X '::n=' A  " := (nat_decl_assign X A) (at level 50).
Notation " 'bol' A " := (bool_decl A) (at level 50).
Notation " X ':b=' A  " := (bool_assign X A) (at level 50).
Notation " 'bol*' X '::n=' A  " := (bool_decl_assign X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).
Notation " 'If' '(' b ')' 'Then' S1 'Else' S2  " := (ifelse b S1 S2 ) (at level 70).
Notation " 'While' '(' b ')' '{' S '}'" := (while b S)(at level 71).
Notation " 'For' '(' S1 ';' b ';' S2 ')' '{' S3 '}' " := ( S1 ;; while b (S3 ;; S2) ) (at level 71).
Notation " 'Do' '{' S1 '}' 'while*' '(' b ')' " := ( S1 ;; while b (S1) ) (at level 71).
Notation " 'functie' S1 '(' a ')' '{' S2 '}' " :=( decl_functie S1 a S2)(at level 45).
Notation " 'begin_main ' S2 'end_main' " :=( decl_functie_main S2).
Notation " 'intglobal' A " := (decl_var_globale A) (at level 50).
Notation " S1 ';*' S2 " := (sequance_program S1 S2)(at level 50).
Notation " 'Template' '<' S '>'" := (decl_templates S )(at level 49).
Notation " a '=*' p1 p2 '{' s '}' ":= (lambda a p1 p2 s )(at level 49). 

Check For ( "i" :n= 1 ; "i" <=' 11 ; "i" :n= "i" +'1 ) {
      "ok" :n= "ok" +' 1
}.
Check While ( "i" =>' 9 ) { "ok" :n= "dada" } .
Check "k"++'.
Check 1+'1.

Check decl_functie "da" [ "ok";"da" ] ("ok":n= "ok"++') .
Check decl_functie_main ( "ok":n= "ok"++' ).
Check int "a".
Check "a":n=3.
Check int* "a"::n=4.
Check decl_templates "tip" ;*
      decl_functie "da" [ "ok";"da" ] ("ok":n= "ok"++') ;*
      intglobal "ok" ;* 
      decl_functie_main ( (int* "ok"::n="ok"+'1) ;;
                          lambda "lbd" []["ok"] ("ok":n=1) ;;
                          apelare_functie "da" [ "a";"b" ]
                        ).


