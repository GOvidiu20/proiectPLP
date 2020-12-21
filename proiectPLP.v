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
Definition Var := string.
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
| berror
| btrue : BExp
| bfalse : BExp
| bvar: Var -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp
| bequal : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

Definition Parametrii := list Var.
Inductive Stmt :=
| nat_decl : Var -> Stmt
| nat_assign : Var -> AExp -> Stmt
| nat_decl_assign : Var -> AExp -> Stmt
| bool_decl : Var -> Stmt
| bool_assign : Var -> BExp -> Stmt
| bool_decl_assign : Var -> BExp -> Stmt
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
| naturals: eroareNat -> Values
| booleans: eroareBool -> Values.
Inductive Programs :=
| decl_functie : string -> Parametrii -> Stmt ->Values-> Programs
| decl_var_globale: Var -> Programs
| decl_var_locale: Var -> Programs
| decl_functie_main : Stmt -> Programs
| sequance_program : Programs -> Programs -> Programs
| decl_templates : string -> Programs.
Inductive Memory :=
  | mem_default : Memory
  | offset : nat -> Memory.
Definition EnvMem := string -> Memory.
Definition MemLayer := Memory -> Values.
Definition Stack := list EnvMem.
Inductive Config :=
  | config : nat -> EnvMem -> MemLayer -> Stack -> Config.
Inductive coada: Type :=
| nil : coada
| elem : eroareNat -> coada -> coada.

Coercion avar :  string >-> AExp.
Coercion anum : nat >-> AExp.

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
Notation "  a ->' c " := (elem a c) (at level 50).

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
      decl_functie "da" [ "ok";"da" ] ("ok":n= "ok"++') (naturals (num 1)) ;*
      intglobal "ok" ;*
      decl_functie_main ( (int* "ok"::n="ok"+'1) ;;
                          lambda "lbd" []["ok"] ("ok":n=1) ;;
                          Do { 
                              "ok":n="ok"+'1
                          }while* ( "ok" =>' 0);;
                          apelare_functie "da" [ "a";"b" ]
                        ).
Check nil.
Check ( (num 1) ->' ( (num 2) ->' nil)).








(*
Definition Env := Var -> Values.
Definition plus_eroareNat (n1 n2 : eroareNat) : eroareNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.

Definition min_eroareNat (n1 n2 : eroareNat) : eroareNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else num (n1 - n2)
    end.

Definition mul_eroareNat (n1 n2 : eroareNat) : eroareNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_eroareNat (n1 n2 : eroareNat) : eroareNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition proc_eroareNat (n1 n2 : eroareNat) : eroareNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.
Fixpoint aeval_fun (a : AExp) (env : Env) : eroareNat :=
  match a with
  | avar v => match (env v) with
                | naturals n => n
                | _ => error_nat
                end
  | anum v => num v
  | aplus a1 a2 => (plus_eroareNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amul a1 a2 => (mul_eroareNat (aeval_fun a1 env) (aeval_fun a2 env))
  | aminus a1 a2 => (min_eroareNat (aeval_fun a1 env) (aeval_fun a2 env))
  | adiv a1 a2 => (div_eroareNat  (aeval_fun a1 env) (aeval_fun a2 env))
  | aproc a1 a2 => (proc_eroareNat (aeval_fun a1 env) (aeval_fun a2 env))
  end.
Reserved Notation "A =[ S ]=> N" (at level 70).
Inductive aeval : AExp -> Env -> eroareNat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> num n
| var : forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                              | naturals x => x
                                              | _ => error_nat
                                              end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plus_eroareNat i1 i2) ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mul_eroareNat i1 i2) ->
    a1 *' a2 =[sigma]=> n
| substract : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (min_eroareNat i1 i2) ->
    a1 -' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (div_eroareNat  i1 i2) ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (proc_eroareNat i1 i2) ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).
Definition env : Env := fun x => undecl.
Example substract_error : 1 -' 5 =[ env ]=> error_nat.
Proof.
  eapply substract.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

Definition lt_eroareBool (n1 n2 : eroareNat) : eroareBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
    end.
Definition gt_eroareBool (n1 n2 : eroareNat) : eroareBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v2 v1)
    end.
Definition eq_eroareBool (n1 n2 : eroareNat) : eroareBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.eqb v2 v1)
    end.
Definition not_eroareBool (n :eroareBool) : eroareBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Definition and_eroareBool (n1 n2 : eroareBool) : eroareBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition or_eroareBool (n1 n2 : eroareBool) : eroareBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.

Fixpoint beval_fun (a : BExp) (envnat : Env) : eroareBool :=
  match a with
  | btrue => boolean true
  | bfalse => boolean false
  | berror => error_bool
  | bvar v => match (env v) with
                | booleans n => n
                | _ => error_bool
                end
  | blessthan a1 a2 => (lt_eroareBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bgreaterthan a1 a2 => (gt_eroareBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bequal a1 a2 => (gt_eroareBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bnot b1 => (not_eroareBool (beval_fun b1 envnat))
  | band b1 b2 => (and_eroareBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  | bor b1 b2 => (or_eroareBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  
end.

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Env -> eroareBool -> Prop :=
| b_error: forall sigma, berror  ={ sigma }=> error_bool
| b_true : forall sigma, btrue ={ sigma }=> boolean true
| b_false : forall sigma, bfalse ={ sigma }=> boolean false
| b_var : forall v sigma, bvar v ={ sigma }=>  match (sigma v) with
                                                | booleans x => x
                                                | _ => error_bool
                                                end
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (lt_eroareBool i1 i2) ->
    a1 <=' a2 ={ sigma }=> b
| b_greaterthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (gt_eroareBool i1 i2) ->
    a1 =>' a2 ={ sigma }=> b
| b_equal : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (eq_eroareBool i1 i2) ->
    a1 ==' a2 ={ sigma }=> b
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (not_eroareBool i1) ->
    !'a1 ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (and_eroareBool i1 i2) ->
    (a1 &' a2) ={ sigma }=> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (or_eroareBool i1 i2) ->
    (a1 |' a2) ={ sigma }=> b 
where "B ={ S }=> B'" := (beval B S B').
Example boolean_operation : bnot (100 <=' "n") ={ env }=> error_bool.
Proof.
  eapply b_not.
  eapply b_lessthan.
  - eapply const.
  - eapply var.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_decl: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (res_nat i)) ->
   (x :n= a) -{ sigma }-> sigma'
| e_nat_assign: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (res_nat i)) ->
    (x :n= a) -{ sigma }-> sigma'
| e_bool_decl: forall a i x sigma sigma',
   a ={ sigma }=> i ->
   sigma' = (update sigma x (res_bool i)) ->
   (x :b= a) -{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (res_bool i)) ->
    (x :b= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma,
    ifthen b s -{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').
*)
