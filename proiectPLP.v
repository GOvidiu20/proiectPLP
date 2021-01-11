Require Import String.
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.
Delimit Scope string_scope with string.
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
| lambda : string -> Parametrii -> Stmt -> Stmt
| lambda_atribuire : Var -> string -> Stmt
| comentarii : Stmt -> Stmt
| switch : AExp -> AExp -> Stmt -> AExp ->Stmt -> Stmt -> Stmt
| break : Stmt -> Stmt.

Inductive Values :=
| err_undecl : Values
| err_assign : Values
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
Inductive coada ( tip : Set) : Set :=
| nill : coada tip
| elem : tip -> coada tip -> coada tip.

Coercion avar :  string >-> AExp.
Coercion anum : nat >-> AExp.
Coercion num : nat >-> eroareNat.
Coercion boolean: bool >-> eroareBool.

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
Notation "  a '=*' p1 p2 '{' s '}' ":= (lambda a p1 p2 s )(at level 49).
Notation " /* s *\ " := (comentarii s ) (at level 48).
Notation " 'Switch' '(' v ')' '{' 'case' a1 ':' s1 'case' a2 ':' s2 s3 } " := (switch v a1 s1 a2 s2 s3) (at level 50).
Check For ( "i" :n= 1 ; "i" <=' 11 ; "i" :n= "i" +'1 ) {
      /* "ok" :n= "ok" +' 1 *\
}.
Check switch ("v") 3 ("a":n=4) 
                   4 ("a":n=3)
                     ("a":n=3) .
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
                          lambda "lbd" [] ("ok":n=1) ;;
                          Do { 
                              "ok":n="ok"+'1
                          }while* ( "ok" =>' 0);;
                          apelare_functie "da" [ "a";"b" ]
                        ).
Check nill.
Check (elem nat 5) (nill nat).


Definition Env := Var -> Values.
Definition env1 : Env := fun x => err_undecl.
Definition check_eq_over_types (t1 : Values)(t2 : Values) : bool :=
  match t1 with
| err_assign => match t2 with 
                   | err_assign => true
                   | _ => false
                   end
| err_undecl => match t2 with 
                   | err_undecl => true
                   | _ => false
                   end
| default => match t2 with 
                   | default => true
                   | _ => false
                   end
| naturals n=> match t2 with 
                   | naturals n=> true
                   | _ => false
                   end
| booleans n=> match t2 with 
                   | booleans n=> true
                   | _ => false
                   end
  end.
Definition update (env : Env) ( x: string ) ( v : Values ) : Env :=
fun y =>
 if(string_beq x y)
  then 
      if ( andb (check_eq_over_types (env y) err_assign ) true )
                       then v
         else if (andb ( check_eq_over_types (env y) v) true ) then v else
            if (andb (check_eq_over_types (env y) default) true ) then v else err_assign
  else (env y).

Definition plus_eroareNat (n1 n2 : eroareNat) : eroareNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 =>  (v1 + v2)
    end.

Definition min_eroareNat (n1 n2 : eroareNat) : eroareNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else  (n1 - n2)
    end.

Definition mul_eroareNat (n1 n2 : eroareNat) : eroareNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 =>  (v1 * v2)
    end.

Definition div_eroareNat (n1 n2 : eroareNat) : eroareNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 =>  (Nat.div v1 v2)
    end.

Definition proc_eroareNat (n1 n2 : eroareNat) : eroareNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => (v1 - v2 * (Nat.div v1 v2))
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
Definition env : Env := fun x => err_undecl.

Compute aeval (1+'5) env error_nat.
Example substract_error : 1 -' 5 =[ env ]=> error_nat.
Proof.
  eapply substract.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.
Example add1 : 1 +' 5 =[ env ]=> 6.
Proof.
    eapply add.
      -eapply const.
      -eapply const.
      - simpl. reflexivity.
Qed.

Require Import Nat.
Definition lt_eroareBool (n1 n2 : eroareNat) : eroareBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => ( leb v1 v2 )
    end.
Compute lt_eroareBool 3 4.
Definition gt_eroareBool (n1 n2 : eroareNat) : eroareBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => (Nat.ltb v2 v1)
    end.

Definition eq_eroareBool (n1 n2 : eroareNat) : eroareBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 =>  (Nat.eqb v2 v1)
    end.
Definition not_eroareBool (n :eroareBool) : eroareBool :=
  match n with
    | error_bool => error_bool
    | boolean v =>  (negb v)
    end.

Definition and_eroareBool (n1 n2 : eroareBool) : eroareBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 =>(andb v1 v2)
    end.

Definition or_eroareBool (n1 n2 : eroareBool) : eroareBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 =>  (orb v1 v2)
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
| b_true : forall sigma, btrue ={ sigma }=>  true
| b_false : forall sigma, bfalse ={ sigma }=>  false
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


Scheme Equality for Memory.
Definition update_env (env: EnvMem) (x: string) (n: Memory) : EnvMem :=
  fun y =>
      if (andb (string_beq x y ) (Memory_beq (env y) mem_default))
      then
        n
      else
        (env y).
Definition envMem : EnvMem := fun x => mem_default.
Definition update_mem (mem : MemLayer) (env : EnvMem) (x : string) (type : Memory) (v : Values) : MemLayer :=
  fun y =>
    if(andb (Memory_beq y type)(Memory_beq (env x) type))
    then
      if(andb (check_eq_over_types err_undecl (mem y)) (negb (check_eq_over_types default v)))
        then err_undecl
      else
        if(andb (check_eq_over_types err_undecl (mem y)) (check_eq_over_types default v))
          then default
        else
          if(orb (check_eq_over_types default (mem y)) (check_eq_over_types v (mem y)))
              then v
          else err_assign
    else (mem y).
Definition mem : MemLayer := fun x => err_undecl.

Check mem.
Compute update_env envMem "x" mem_default.
Compute update_env envMem "y" (offset 5).
Compute envMem "x".
Compute envMem "y".
Compute ( update_env envMem  "x" (offset 5)) "x".
Check envMem.
Compute (update_mem mem envMem "sal" mem_default default).
Compute (update_mem mem ( update_env envMem  "x" (offset 5)) "x" mem_default (naturals (num 5))).

Definition coada_push ( n : Set ) ( c : coada n) ( el : n) : coada n:=
  match c with
  | _ => (elem n el c )
  end.
Definition coada_pop1 ( n : Set ) ( c : coada n) : coada n:=
  match c with
  | elem _ x ( elem _ y ( elem _ z (nill _ ))) => elem n x ( elem n y (nill n))
  | elem _ x ( elem _ y (nill _ )) => elem n x (nill n) 
  | elem _ x ( nill _ ) => nill n  
  | elem _ x c' => c'
  | nill _ => nill n
end.
Fixpoint coada_length (n : Set) ( c : coada n) : nat :=
  match c with
  | nill _ => 0
  | elem _ x c' => 1 + ( coada_length n c')
  end.
Definition coada_first ( n : Set) (err : n) (c : coada n) : n :=
  match c with 
  | elem _ x c' => x
  | nill _ => err
end.
Definition coada_last ( n : Set) (err : n) (c : coada n) : n :=
  match c with
  | elem _ x ( elem _ y ( elem _ z (nill _ ))) => z
  | elem _ x ( elem _ y (nill _ )) => y 
  | elem _ x ( nill _ ) => x
  | elem _ x c' => x
  | nill _ => err
end.

Definition update_list_globale ( l : list Var ) ( x : Var )
    : list Var := l++ [x].
Definition update_list_locale ( l : list Var ) ( x : Var )
    : list Var := l++ [x].
Definition update_list_functii ( l : list Var ) ( x : Var )  
    : list Var := l++ [x].
Definition update_template ( l : list Var ) ( x : Var )  
    : list Var := l++ [x].
Fixpoint search_functie ( l:list Var ) (x : Var) : bool :=
  match l with
  | [] => false
  | y :: l => if ( andb (string_beq y x ) true ) then true
                else
                  search_functie l x
end.
Compute search_functie ["a" ; "b" ; "c" ] "c". 
Compute update_list_globale ["a";"b"] "c". 
Definition parametrii1 := Parametrii.
Definition parametrii2 := Parametrii.

 Inductive Instruction :=
| push_stmt : Stmt -> Instruction
| pop_stmt: Stmt -> Instruction.
Definition Stackf := list Stmt.
Definition take_stmt (i : Instruction) (s : Stmt): Stmt :=
  match i with
  | pop_stmt c => c
  | _ => s
end.
Definition compile1 (e : Stmt) (stack : list Instruction ): list Instruction :=
  match e with
  | nat_decl a => stack ++ [push_stmt (nat_decl a)]
  | nat_assign a x => stack ++[push_stmt (nat_assign a x)]
  | nat_decl_assign a x=> stack ++[push_stmt (nat_decl_assign a x)]
  | bool_decl a => stack ++[push_stmt (bool_decl a)]
  | bool_assign a x=> stack ++[push_stmt (bool_assign a x)]
  | bool_decl_assign a x=> stack ++[push_stmt (bool_decl_assign a x)]
  | apelare_functie x c => stack ++[push_stmt (apelare_functie x c)]
  | sequence a b => stack ++[push_stmt (sequence a b)]
  | while b c=> stack ++[push_stmt (while b c)]
  | ifthen b c =>stack ++ [push_stmt (ifthen b c)]
  | ifelse b a c => stack ++[push_stmt (ifelse b a c)]
  | lambda x a d => stack ++[push_stmt (lambda x a d)]
  | lambda_atribuire x b=> stack ++[push_stmt (lambda_atribuire x b)]
  | comentarii c =>stack ++ [push_stmt (comentarii c)]
  | switch a b c d e f => stack ++ [push_stmt (switch a b c d e f)]
  | break s => stack ++ [push_stmt ( break s)]
end.
Definition compile2 ( l : list Instruction) (i : Instruction) : Instruction := 
  match l with
  | x :: l => x
  | [] => i
end.

Definition update_lambda (env : Env) ( x: string ) :=
fun y =>
 if(string_beq x y)
  then (env x)
  else (naturals 0)
.
Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_nat_assign: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (naturals i)) ->
   (nat_assign x a) -{ sigma }-> sigma'
| e_nat_decl: forall x sigma sigma',
    sigma' = (update sigma x err_assign) ->
    (nat_decl x) -{ sigma }-> sigma'
| e_nat_decl_assign: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (naturals i)) ->
   (nat_decl_assign x a) -{ sigma }-> sigma'

| e_bool_decl: forall x sigma sigma',
   sigma' = (update sigma x err_undecl) ->
   (bool_decl x) -{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (booleans i)) ->
    (bool_assign x a) -{ sigma }-> sigma'
| e_bool_decl_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (booleans i)) ->
    (bool_decl_assign x a) -{ sigma }-> sigma'

| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma sigma',
    b ={ sigma }=> true ->
    s -{ sigma }-> sigma' ->
    ifthen b s -{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=>true ->
    s1 -{ sigma }-> sigma' ->
    ifelse b s1 s2 -{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> boolean false ->
    s2 -{ sigma }-> sigma' ->
    ifelse b s1 s2 -{ sigma }-> sigma' 
| e_switch1 : forall a i a1 a2 s1 s2 s3 sigma sigma' ,
    a =[ sigma ]=> i ->
    s1 -{ sigma }-> sigma' ->
    switch a a1 s1 a2 s2 s3 -{ sigma }-> sigma'
| e_switch2 : forall a i a1 a2 s1 s2 s3 sigma sigma' ,
    a =[ sigma ]=> i ->
    s2 -{ sigma }-> sigma' ->
    switch a a1 s1 a2 s2 s3 -{ sigma }-> sigma'
| e_switchDefault : forall a i a1 a2 s1 s2 s3 sigma sigma' ,
    a =[ sigma ]=> i ->
    s3 -{ sigma }-> sigma' ->
    switch a a1 s1 a2 s2 s3 -{ sigma }-> sigma'
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=>  true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_lambda : forall x s parametrii1 sigma1 sigma2,
    s -{ sigma1 }-> sigma2 ->
    (lambda x parametrii1 s) -{ sigma1 }-> sigma2
| e_lambda_apel : forall x a sigma1 sigma2 ,
    sigma2=(update sigma1 x (sigma1 "var")) ->
    ( lambda_atribuire x a ) -{ sigma1 }-> sigma2
| e_apelare : forall x parametrii1 sigma1 sigma2,
    (* b = search_functie lista x ->
    b =true ->
    instruc = compile2 lista_instruc instruc1 ->
    stmt = take_stmt instruc s->
    stmt -{ sigma1 }-> sigma2 -> *)
    (apelare_functie x parametrii1) -{ sigma1 }-> sigma2
| e_coments : forall s sigma1 sigma2 ,
    /* s *\ -{ sigma1 }-> sigma2
| e_break : forall s sigma1 sigma2 ,
    (break s ) -{ sigma1 }-> sigma2
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

Reserved Notation "S -*{ Sigma }*-> Sigma'" (at level 60).
Inductive evalprograms : Programs -> Env -> Env -> Prop :=
| e_decl_global: forall x list_glb' list_glb sigma sigma',
    sigma' = (update sigma x (naturals (num 0))) ->
    list_glb' = (update_list_globale list_glb x) ->
    (decl_var_globale x) -*{ sigma }*-> sigma'
| e_decl_functie: forall x s Parametrii  y  sigma sigma',
    s -{ sigma }-> sigma' ->
    (* stack' = ( compile1 s stack) -> 
    list_functii' = ( update_list_functii list_functii x)-> *)
    (decl_functie x Parametrii s y) -*{ sigma }*-> sigma'
| e_decl_functie_main : forall s sigma sigma',
    s -{ sigma }-> sigma' ->
    (decl_functie_main s ) -*{ sigma }*-> sigma'
| e_seq_prg : forall s1 s2 sigma sigma1 sigma2,
    s1 -*{ sigma }*-> sigma1 ->
    s2 -*{ sigma1 }*-> sigma2 ->
    (s1 ;* s2) -*{ sigma }*-> sigma2
| e_template : forall x sigma' sigma lista lista' ,
    lista' = (update_template lista x) ->
    decl_templates x -*{ sigma }*-> sigma'
where "s -*{ sigma }*-> sigma'" := (evalprograms s sigma sigma').


Compute (coada_push nat ( nill nat ) 4).
Compute (coada_push nat (coada_push nat ( nill nat ) 4) 5).
Compute coada_pop1 nat (coada_push nat (coada_push nat ( (coada_push nat ( nill nat )3) ) 4) 5).
Compute coada_length nat (coada_push nat (coada_push nat ( nill nat ) 4) 5).
Compute coada_first eroareNat error_nat (coada_push eroareNat (coada_push eroareNat ( nill eroareNat ) (num 4)) (num 5)).
Compute coada_last eroareNat error_nat (coada_push eroareNat (coada_push eroareNat ( nill eroareNat ) (num 4)) (num 5)).


Definition ex_stmt := 
  int "i";; 
  int "j";;
  int "s";; 
  ("i":n=0);;
  ("j":n=1);;
  ifthen ( "i" <=' "j") 
    (("s":n=18);;
    break
    (("s" :n= 11);;
     ("s" :n= 12) ) );;
  Do 
  { "s" :n= 10
  }while* ( "j"<='"i");;
  switch ("j") 1   ("s":n=18) 
               "i" ("s":n=17)
                   ("s":n=13);;
  bol "c";;
  ("c" :b= btrue);;
  /* "s":n=19 *\.

Example eval_ex :
  exists state, ex_stmt -{ env }-> state .
Proof.
  eexists.
  +unfold ex_stmt.
    eapply e_seq.
      -eapply e_seq.  
        -- eapply e_seq.
          --- eapply e_seq.  
             ++ eapply e_seq.
              +++ eapply e_seq.
               +++++ eapply e_seq.
                ++++++ eapply e_seq.
                  +++++++ eapply e_seq.
                    ++++++++ eapply e_seq.
                  ++++ eapply e_nat_decl. eauto.
                  ++++ eapply e_nat_decl. eauto.
                    ++++++++ eapply e_nat_decl.
                ++++ split.
            +++++++ eapply e_nat_assign. 
              ++++ eapply const.
              ++++ split.
         ++++++ eapply e_nat_assign.
           ++++ eapply const.
           ++++ split.
       +++++ eapply e_if_then.
           ++++eapply b_lessthan.
             +++++++ eapply var. 
             +++++++ eapply var.
             +++++++ simpl. reflexivity.
          ++++ eapply e_seq.
            +++++++ eapply e_nat_assign. eapply const. eauto.
            +++++++ eapply e_break.
    +++ eapply e_seq.
     ++++ eapply e_nat_assign.
        +++++ eapply const.
        +++++ split.
    ++++ eapply e_whilefalse.
      ++++++ eapply b_lessthan.
        +++++ eapply var.
        +++++ eapply var.
        +++++ simpl. reflexivity.
  ++ eapply e_switch1.
    +++ eapply var.
    +++ eapply e_nat_assign.
      ++++ eapply const.
      ++++ split.
  --- eapply e_bool_decl. split.
  -- eapply e_bool_assign.
    ++ eapply b_true.
    ++ split.
  - eapply e_coments.
Abort.

Definition max1 :=
  intglobal "n";*
  decl_functie "da" [ "ok";"da" ] ( ("ok":n=3) ) (naturals (num 1)) ;*
  intglobal "ok" ;*
  decl_functie_main ( (int "a") ;;
                       ("a" :n=3 );;
                       lambda "lbd" [] ( int "var";;
                                         "var":n=3);;
                       int "m";;
                       lambda_atribuire "m" "lbd";;
                       ifthen ("m"=='3) ("m":n=3);;
                       apelare_functie "da" [ "a";"b" ]
                       ).

Definition state0 := fun (x:Var) => err_undecl.
Example eval_max1 : 
 exists state, max1 -*{ state0 }*-> state .
Proof.
  eexists.
  - unfold max1. 
    eapply e_seq_prg.
    ++ eapply e_seq_prg.
        +++ eapply e_decl_global;eauto.
        +++ eapply e_decl_functie; eauto.
             +++++ eapply e_nat_assign.
              ++++++ eapply const.
              ++++++ split.
    ++ eapply e_seq_prg.
      +++ simpl. eapply e_decl_global; eauto.
      +++ eapply e_decl_functie_main. 
          eapply e_seq.
          ++++ eapply e_seq.
            +++++ eapply e_seq.
              ++++++ eapply e_seq.
                -- eapply e_seq.
                --- eapply e_seq.
              +++++++ eapply e_nat_decl.
                ++++++++ simpl. split. 
              +++++++ eapply e_nat_assign.
                    ---- eapply const.
                    ---- split.
             --- eapply e_lambda. eapply e_seq. 
                  ----- eapply e_nat_decl. split. 
                  ----- eapply e_nat_assign. 
                      ---- eapply const.
                      ---- split.
            -- eapply e_nat_decl. split.
              ++++++ eapply e_lambda_apel. split.
             +++++ eapply e_if_then.
               ++++++ eapply b_equal.
                +++++++ eapply var.
                +++++++ eapply const.
                +++++++ simpl. reflexivity.
                  ++++++ eapply e_nat_assign.
                    +++++++ eapply const.
                    +++++++ split.
            ++++ eapply e_apelare.
Abort.

Compute (coada_push nat ( nill nat ) 4).
Compute (coada_push nat (coada_push nat ( nill nat ) 4) 5).
Compute coada_pop1 nat (coada_push nat (coada_push nat ( (coada_push nat ( nill nat )3) ) 4) 5).
Compute coada_length nat (coada_push nat (coada_push nat ( nill nat ) 4) 5).
Compute coada_first eroareNat error_nat (coada_push eroareNat (coada_push eroareNat ( nill eroareNat ) (num 4)) (num 5)).
Compute coada_last eroareNat error_nat (coada_push eroareNat (coada_push eroareNat ( nill eroareNat ) (num 4)) (num 5)).


Inductive string  :=
  | EmptyString : string
  | String : string -> string.

Definition s_concat ( x1 x2 : String.string ) := append x1 x2.
Definition s_copy ( x1 x2 : String.string ) :=
  match x1 with
  | _ => append String.EmptyString x2
end.
Definition s_equal ( x1 x2 : String.string ) :=
  match x1 with
  | _ => if ( string_beq x1 x2 ) then true else false
end.

Definition s_length (x1 : String.string) := String.length x1.
Compute (s_concat "d" "nu").
Compute (s_copy "d" "nu").  
Compute (s_equal "da" "nu").
Compute s_length "aaaaaaa". 



Inductive BExp1 :=
| bTrue : BExp1
| bFalse : BExp1
| bVar : Var-> BExp1
| bNot : BExp1 -> BExp1
| bAnd : BExp1 -> BExp1 -> BExp1
| bOr : BExp1 -> BExp1 -> BExp1.

Notation " a &&' b" := (bAnd a b ) (at level 50).
Notation " a ||' b" := (bOr a b ) (at level 50).
Notation " !!' b" := (bNot b ) (at level 50).
Definition EnvB := Var ->bool.
Definition env0 := fun x => if string_dec x "x" then false else true.


Fixpoint interpret (e : BExp1) (env : EnvB) : bool :=
  match e with
  | bTrue => true
  | bFalse => false
  | bVar x => (env x)
  | bNot x => negb (interpret x env)
  | bAnd e1 e2 => andb (interpret e1 env) (interpret e2 env) 
  | bOr e1 e2 => orb (interpret e1 env) (interpret e2 env)
  end.

Compute (interpret bFalse env0).
Compute (interpret (!!' (bVar "x")) env0).
Compute (interpret (bTrue &&' (bVar "y")) env0).
Compute (interpret (bTrue ||' (bVar "x")) env0).


Inductive BInstruction :=
| push_const : bool -> BInstruction
| push_var : Var -> BInstruction
| notu' : BInstruction
| andu' : BInstruction
| oru' : BInstruction.

Definition BStack := list bool.
Definition run_instruction (i : BInstruction)
         (env : EnvB) (stack : BStack) : BStack :=
  match i with
  | push_const c => (c :: stack)
  | push_var x => ((env x) :: stack)
  | notu' => match stack with
           | n1 :: stack' => ( negb n1) :: stack'
           | _ => stack
           end  
  | andu' => match stack with
           | n1 :: n2 :: stack' => ( andb n1 n2) :: stack'
           | _ => stack
           end 
  | oru' => match stack with
           | n1 :: n2 :: stack' => ( orb n1 n2) :: stack'
           | _ => stack
           end
  end.


Compute (run_instruction (push_const true) env0 []).
Compute (run_instruction (push_var "x") env0 []).
Compute (run_instruction notu' env0 [true]).
Compute (run_instruction andu' env0 [true;false;false]).
Compute (run_instruction oru' env0 [true;false;true]).

Fixpoint run_instructions (is' : list BInstruction)
         (env : EnvB) (stack : BStack) : BStack :=
  match is' with
  | [] => stack
  | i :: is'' => run_instructions is'' env (run_instruction i env stack)
  end.

Definition pgm2 := [
                    push_const true ;
                    push_var "x" ;
                    andu';
                    push_var "x";
                    oru';
                    notu'
                  ].
Compute run_instructions pgm2 env0 [].

Fixpoint compile (e : BExp1) : list BInstruction :=
  match e with
  | bTrue => [push_const true]
  | bFalse => [push_const false]
  | bVar x => [push_var x]
  | bNot x => (compile x ) ++ [notu']
  | bAnd e1 e2 => (compile e1) ++ (compile e2) ++ [andu']
  | bOr e1 e2 => (compile e1) ++ (compile e2) ++ [oru']
  end.


Compute compile (!!' (bVar "x")).
Compute compile (bTrue &&' (bVar "x")).
Compute compile (!!'(bFalse ||' (bVar "x") &&' bTrue)).

Compute interpret (!!'(bFalse ||' (bVar "x") &&' bTrue)) env0.
Compute run_instructions
        (compile (!!'(bFalse ||' (bVar "x") &&' bTrue)))
        env0
        [].

Lemma soundness_helper :
  forall e env stack is',
    run_instructions (compile e ++ is') env stack =
    run_instructions is' env ((interpret e env) :: stack).
Proof.
  induction e; intros; simpl; trivial.
  - rewrite <- app_assoc.
    rewrite IHe. simpl. reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    rewrite andb_comm.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    rewrite orb_comm.
    reflexivity.
Qed.

Theorem soundness :
  forall e env,
    run_instructions (compile e) env [] =
    [interpret e env].
Proof.
  intros.
  rewrite <- app_nil_r with (l := (compile e)).
  rewrite soundness_helper.
  simpl. trivial.
Qed.









