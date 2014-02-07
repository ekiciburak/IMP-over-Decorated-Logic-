(**************************************************************************)
(*  This is part of STATES, it is distributed under the terms of the      *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2013: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory Terms Decorations Axioms Derived_Terms Derived_Pairs
Derived_Products Derived_Rules Proofs.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.

Module Make(Import M: Memory.T).
  Module Export ConversionExp := Proofs.Make(M).

 Inductive ArithExp : Type :=
    | const    : Z -> ArithExp
    | loc      : Loc -> ArithExp
    | add      : ArithExp -> ArithExp -> ArithExp
    | multiply : ArithExp -> ArithExp -> ArithExp.

 Fixpoint defArithExp (a: ArithExp) : term Z unit :=
  match a with
    | const n        => (@constant Z n)
    | loc x          => (lookup x)
    | add t1 t2      => plus o (pair (defArithExp t1) (defArithExp t2))
    | multiply t3 t4 => mult o (pair (defArithExp t3) (defArithExp t4))
  end.

 Inductive BoolExp : Type :=
    | constT  : term boolT unit -> BoolExp
    | constF  : term boolT unit -> BoolExp
    | gtT     : ArithExp -> ArithExp -> BoolExp
    | geT     : ArithExp -> ArithExp -> BoolExp
    | ltT     : ArithExp -> ArithExp -> BoolExp
    | leT     : ArithExp -> ArithExp -> BoolExp
    | eqT     : ArithExp -> ArithExp -> BoolExp
    | andT    : BoolExp -> BoolExp -> BoolExp
    | orT     : BoolExp -> BoolExp -> BoolExp.

 Fixpoint defBoolExp (b: BoolExp) : term boolT unit :=
  match b with
    | constT ttrue  => ttrue
    | constF ffalse => ffalse
    | gtT a1 a2     => (gt o (pair (defArithExp a1) (defArithExp a2)))
    | geT a1 a2     => (ge o (pair (defArithExp a1) (defArithExp a2)))
    | ltT a1 a2     => (lt o (pair (defArithExp a1) (defArithExp a2)))
    | leT a1 a2     => (le o (pair (defArithExp a1) (defArithExp a2)))
    | eqT a1 a2     => (eq o (pair (defArithExp a1) (defArithExp a2)))
    | andT b1 b2    => (andB o (pair (defBoolExp b1) (defBoolExp b2)))
    | orT b3 b4     => (orB o (pair (defBoolExp b3) (defBoolExp b4)))
  end.

 Inductive Command : Type :=
    | skip       : Command
    | sequence   : Command -> Command -> Command
    | assign     : Loc -> ArithExp -> Command 
    | ifthenelse : BoolExp -> Command -> Command -> Command
    | loops      : BoolExp -> Command -> Command
    | throwexc   : EName -> Command
    | trycatch   : EName -> Command -> Command -> Command.

 Fixpoint defCommand (c: Command): (term unit unit) :=
  match c with
    | skip                => (@id unit)
    | sequence c0 c1      => (defCommand c1) o (defCommand c0)
    | assign i e0         => (update i) o (defArithExp e0)
    | ifthenelse b c2 c3  => (copair (defCommand c2) (defCommand c3)) o (defBoolExp b)
    | loops b c4          => (copair (loopdec o defCommand c4) (@id unit)) o (defBoolExp b)
    | throwexc t0         => (throw unit t0)
    | trycatch t1 c5 c6   => (@TRY_CATCH _ _ t1 (defCommand c5) (defCommand c6))
  end.

 Notation "x '::=' a" := (assign x a) (at level 60).
 Notation "c1 ';;' c2" := (sequence c1 c2) (at level 65).
 Notation "'SKIP'" := (skip) (at level 60).
 Notation "'IFB' b 'THEN' t1 'ELSE' t2 'FI'" := (ifthenelse b t1 t2) (at level 60).
 Notation "'WHILE' b 'DO' c" := (loops b c) (at level 60).
 Notation " x '+++' y" := (add x y) (at level 60).
 Notation " x '***' y" := (multiply x y) (at level 60).
 Notation " x '>>' y" := (gtT x y) (at level 63).
 Notation " x '>>=' y" := (geT x y) (at level 63).
 Notation " x '<<' y" := (ltT x y) (at level 63).
 Notation " x '<<=' y" := (leT x y) (at level 63).
 Notation " x '===' y" := (eqT x y) (at level 63).
 Notation " x '&&&' y" := (andT x y) (at level 64).
 Notation " x '|||' y" := (orT x y) (at level 64).
 Notation "'THROW' en" := (throwexc en) (at level 60).
 Notation "'TRY' s0 'CATCH' e '=>' s1" := (trycatch e s0 s1) (at level 60).
 Notation "'{{' c '}}'" := (defCommand c) (at level 67).
 Notation "'``' c '``'" := (defBoolExp c) (at level 67).

 Parameter i j k: Loc.
 Parameter en: EName.
 Check {{ WHILE (constT ttrue) DO (i ::= (loc i +++ const 1)) }}.
 Check {{i ::= (loc j) ;; j ::= (const 5) ;; (k ::= (const 5) ;; SKIP)}}.
 Check (loc j) +++ (const 20) +++ (const 25) +++ (loc k).
 Check {{k ::= (loc i) ;; i ::= (loc j +++ const 20 +++ loc k +++ const 40) ;; k ::= (loc j)}}.
 Check {{i ::= (loc i +++ const 1)}}.
 Check (loc i +++ const 1).
 Check {{i ::= (loc i +++ const 1) ;; THROW en}}.
 Check {{THROW en ;; i ::= (loc i +++ const 1)}}.
 Check {{ i ::= (loc i +++ const 1);; THROW en }}.
 Check {{TRY (IFB (constT ttrue)
               THEN (i ::= (loc i +++ const 1);;
                     THROW en)
              ELSE (SKIP)
              FI)
         CATCH en => (i ::= (const 10))}}.

 Eval simpl in k ::= (loc i) ;; i ::= (loc j +++ const 20 +++ loc k +++ const 40).

 Eval simpl in IFB (constF ffalse) 
                 THEN (k ::= (loc i) ;; i ::= (loc j +++ const 20 +++ loc k +++ const 40))
               ELSE (i ::= (loc j) ;; j ::= (const 5))
               FI.

 Lemma IMP_ex1: forall (x y: Loc) (p q: Z), x <> y ->
      {{x ::= (const p) ;; 
        y ::= (const q)}}
      ==
      {{y ::= (const q);; 
        x ::= (const p)}}.
 Proof.
   intros. unfold defCommand. unfold defArithExp.
   remember (@commutation_update_x_update_y y x).
   specialize(@commutation_update_x_update_y y x q p). intros.
   rewrite assoc. rewrite assoc. apply strong_sym.
   apply H0. auto.
 Qed.

 Lemma IMP_ex2: forall m: Loc,
       {{IFB (constT ttrue) 
           THEN (m ::= const (-30)) 
         ELSE (SKIP)
         FI}}
       ==
       {{IFB (constF ffalse) 
           THEN (SKIP) 
         ELSE (m ::= const (-30))
         FI}}.
 Proof.
 intros. simpl.
 transitivity(update m o constant (-30)) .
 apply strong_coproj_copi1_rwrw. apply strong_sym.
 transitivity(update m o constant (-30)). 
 apply strong_coproj_copi2_rwrw. apply strong_refl.
 Qed.

 Lemma IMP_ex3: forall (x: Loc) (p q: Z),
      {{x ::= (const p)  ;;
        x ::= (const q)}}
      ==
      {{x ::= (const q)}}.
 Proof.
     intros. simpl.
     apply observation. intros. destruct(Loc_dec i0 x). rewrite e.
     transitivity(lookup x o update x o constant q o 
     (forget o constant p)).
     transitivity(id o constant q o update x o constant p).
     rewrite assoc. rewrite assoc. apply weak_subs. apply weak_subs.
     rewrite assoc. apply weak_subs. apply axiom_1.
     apply weak_sym.
     transitivity(id o constant q o forget o constant p).
     rewrite assoc. apply weak_subs. apply weak_subs. apply weak_subs.
     apply axiom_1. 
     rewrite <- assoc. rewrite <- assoc. 
     rewrite <- assoc. rewrite <- assoc.
     apply zero_weak_repl. auto. apply zero_weak_repl. auto. 
     apply weak_final_unique.
     transitivity(id o constant q o forget o constant p).
     rewrite assoc. apply weak_subs. apply weak_subs.
     apply weak_subs. apply axiom_1.
     transitivity(id o constant q o id). rewrite <- assoc.
     apply zero_weak_repl. auto. apply weak_final_unique.
     apply weak_sym.
     transitivity(id o constant q).
     rewrite assoc. apply weak_subs. apply axiom_1.
     rewrite <- assoc. apply zero_weak_repl. auto.
     rewrite id_src. apply weak_refl.
     transitivity(lookup i0 o forget o constant q o update x o constant p).
     rewrite assoc. rewrite assoc. apply weak_subs. apply weak_subs.
     rewrite assoc. apply weak_subs. apply axiom_2. auto.
     transitivity(lookup i0 o id o update x o constant p).
     apply weak_subs. apply weak_subs. apply strong_to_weak. 
     rewrite <- assoc. apply strong_repl. apply zero_weak_to_strong.
     auto. auto. apply weak_final_unique.
     transitivity(lookup i0 o forget o constant p).
     apply weak_subs.
     transitivity(lookup i0 o update x).
     apply weak_subs. rewrite id_src. apply weak_refl.
     apply axiom_2. auto.
     transitivity(lookup i0 o id). apply strong_to_weak.
     rewrite <- assoc. apply strong_repl. apply zero_weak_to_strong.
     auto. auto. apply weak_final_unique. apply weak_sym.
     transitivity(lookup i0 o forget o constant q).
     rewrite assoc. apply weak_subs. apply axiom_2. auto.
     apply strong_to_weak. rewrite <- assoc. apply strong_repl.
     apply zero_weak_to_strong. auto. auto. apply weak_final_unique.  
 Qed.

 Lemma IMP_ex4: forall (x: Loc) (p q: Z),
      {{x ::= (const p)  ;;
        x ::= (loc x +++ const q)}}
      ==
      {{x ::= (const (p+q))}}.
 Proof.
     intros. simpl.
     transitivity(update x o (plus o pair (constant p) (constant q)) o 
     (update x o constant p)). rewrite <- assoc.
     setoid_rewrite <- assoc at 2. apply strong_repl.
     rewrite <- assoc. setoid_rewrite <- assoc at 1.
     apply strong_repl. apply strong_unicity.
     transitivity(lookup x o update x o constant p).
     rewrite assoc. rewrite assoc. apply weak_subs. apply weak_subs.
     apply weak_proj_pi1_rorw. auto. apply weak_sym.
     apply strong_to_weak. 
     transitivity(constant p o update x o constant p).
     rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
     apply strong_proj_pi1_purepure. auto. auto.
     remember commutation_lookup_constant.
     specialize(@commutation_lookup_constant x p). intros.
     apply strong_sym. apply H.
     transitivity(constant q o update x o constant p).
     rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
     apply strong_proj_pi2_rorw. auto. apply strong_sym.
     transitivity(constant q o update x o constant p).
     rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
     apply strong_proj_pi2_purepure. auto. auto. apply strong_refl.
     transitivity((update x o constant (p+q) o (update x o constant p))).
     apply strong_subs. apply strong_repl. apply IMP_IntAdd.
     
     remember IMP_ex3.
     specialize(@IMP_ex3 x p (p+q)). intros. simpl in H. apply H.
 Qed.

 Lemma IMP_ex5: forall (x: Loc) (p q: Z),
      {{x ::= (const p)  ;;
        x ::= (loc x *** const q)}}
      ==
      {{x ::= (const (p*q))}}.
 Proof.
     intros. simpl.
     transitivity(update x o (mult o pair (constant p) (constant q)) o 
     (update x o constant p)). rewrite <- assoc.
     setoid_rewrite <- assoc at 2. apply strong_repl.
     rewrite <- assoc. setoid_rewrite <- assoc at 1.
     apply strong_repl. apply strong_unicity.
     transitivity(lookup x o update x o constant p).
     rewrite assoc. rewrite assoc. apply weak_subs. apply weak_subs.
     apply weak_proj_pi1_rorw. auto. apply weak_sym.
     apply strong_to_weak. 
     transitivity(constant p o update x o constant p).
     rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
     apply strong_proj_pi1_purepure. auto. auto.
     remember commutation_lookup_constant.
     specialize(@commutation_lookup_constant x p). intros.
     apply strong_sym. apply H.
     transitivity(constant q o update x o constant p).
     rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
     apply strong_proj_pi2_rorw. auto. apply strong_sym.
     transitivity(constant q o update x o constant p).
     rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
     apply strong_proj_pi2_purepure. auto. auto. apply strong_refl.
     transitivity((update x o constant (p*q) o (update x o constant p))).
     apply strong_subs. apply strong_repl. apply IMP_IntMult.
     
     remember IMP_ex3.
     specialize(@IMP_ex3 x p (p*q)). intros. simpl in H. apply H.
 Qed.

 Lemma IMP_ex6: forall (x: Loc),
      {{WHILE (constF ffalse) 
          DO (x ::= (const 2)) ;; 
        SKIP}}
      ==
      {{SKIP}}.
 Proof.
     intros. unfold defCommand. unfold defArithExp.
     unfold defBoolExp. rewrite id_tgt.
     apply strong_coproj_copi2_rwrw.
 Qed.

 Lemma pair_ex: forall (m: Loc) (c0 c1: Z),
       gt o (pair (lookup m) (constant c1)) o update m o constant c0
	~~
       gt o (pair (constant c0) (constant c1)).  
 Proof.
     intros. rewrite <- assoc. rewrite <- assoc.
     apply zero_weak_repl. auto. apply unicity.
     transitivity((lookup m) o (update m o constant c0)).
     rewrite assoc. apply weak_subs.
     apply weak_proj_pi1_rorw. auto.
     transitivity(id o constant c0). rewrite assoc.
     apply weak_subs. apply axiom_1. rewrite id_tgt.
     apply weak_sym. apply weak_proj_pi1_rorw. auto.
     transitivity(constant c1 o update m o constant c0).
     rewrite assoc. rewrite assoc. apply weak_subs.
     apply weak_subs. apply strong_to_weak.
     apply strong_proj_pi2_rorw. auto.
     transitivity(constant c1 o forget o constant c0).
     apply weak_subs. apply zero_weak_repl.
     auto. apply weak_final_unique.
     transitivity(constant c1 o id). rewrite <- assoc.
     apply zero_weak_repl. auto. apply weak_final_unique.
     rewrite id_src. apply weak_sym. apply strong_to_weak.
     apply strong_proj_pi2_rorw. auto.     
 Qed.

 Lemma pair_ex_2: forall (m n: Loc) (c0 c1: Z),
       gt o (pair (lookup m) (constant c1)) o update m o constant c0 o update n o constant c1 
	~~
       gt o (pair (constant c0) (constant c1)).  
 Proof.
     intros. rewrite <- assoc. rewrite <- assoc.
     rewrite <- assoc. rewrite <- assoc.
     apply zero_weak_repl. auto. apply unicity.
     transitivity((lookup m) o (update m o constant c0) o (update n o constant c1)).
     rewrite assoc. rewrite assoc. rewrite assoc. apply weak_subs.
     rewrite <- assoc. apply weak_subs. apply weak_proj_pi1_rorw. auto.
     transitivity(id o constant c0 o update n o constant c1).
     rewrite assoc. apply weak_subs. apply weak_subs. 
     rewrite assoc. apply weak_subs. apply axiom_1.
     transitivity(id o constant c0 o forget o constant c1).
     rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
     rewrite <- assoc. apply zero_weak_repl. auto.
     apply zero_weak_repl. auto. apply weak_final_unique.
     transitivity(id o constant c0 o id). rewrite <- assoc.
     apply zero_weak_repl. auto. apply weak_final_unique.
     rewrite id_src. rewrite id_tgt. apply weak_sym. 
     apply weak_proj_pi1_rorw. auto. 
     transitivity(constant c1 o update m o constant c0 o update n o constant c1).
     rewrite <- assoc.  rewrite <- assoc.  rewrite <- assoc. 
     rewrite assoc. apply weak_subs. apply strong_to_weak.
     apply strong_proj_pi2_rorw. auto.
     transitivity((((constant c1 o forget) o constant c0) o update n) o constant c1).
     apply weak_subs. apply weak_subs. apply weak_subs. 
     apply zero_weak_repl. auto. apply weak_final_unique.
     transitivity(constant c1 o forget o (constant c0) o forget o constant c1).
     apply weak_subs. apply zero_weak_repl. auto. apply weak_final_unique.
     transitivity((((constant c1 o forget) o constant c0) o id)).
     rewrite <- assoc. apply zero_weak_repl. auto. apply weak_final_unique.
     transitivity(constant c1 o id o id). apply weak_subs.
     rewrite <- assoc. apply zero_weak_repl. auto. apply weak_final_unique.
     rewrite id_src. rewrite id_src. apply weak_sym. apply strong_to_weak.
     apply strong_proj_pi2_rorw. auto.     
 Qed.     
 

 Lemma strong_pair: forall (m: Loc) (p q: Z),
      (pair (lookup m) (constant q)) o update m o constant p
      ==
      (pair (constant p) (constant q)) o update m o constant p.
 Proof.
      intros. apply strong_unicity.
      transitivity(lookup m o update m o constant p).
      rewrite assoc. apply weak_subs. rewrite assoc.
      apply weak_subs. apply weak_proj_pi1_rorw. auto.
      transitivity(id o constant p).
      apply weak_subs. apply axiom_1. apply weak_sym.
      transitivity(constant p o update m o constant p).
      rewrite assoc. apply weak_subs. rewrite assoc.
      apply weak_subs. apply weak_proj_pi1_rorw. auto.
      rewrite id_tgt. setoid_rewrite <- id_src at 6.
      rewrite <- assoc. apply zero_weak_repl. auto.
      apply weak_final_unique.
      transitivity(constant q o update m o constant p).
      rewrite assoc. apply strong_subs. rewrite assoc.
      apply strong_subs. apply strong_proj_pi2_rorw. auto.
      apply strong_sym.
      transitivity(constant q o update m o constant p).
      rewrite assoc. apply strong_subs. rewrite assoc.
      apply strong_subs. apply strong_proj_pi2_rorw. auto.
      apply strong_refl.      
 Qed.

 (* Lemma strong_permpair: forall (m: Loc) (p q: Z),
      (perm_pair (lookup m) (constant q)) o update m o constant p
      ==
      (perm_pair (constant p) (constant q)) o update m o constant p.
 Proof.
      intros. apply strong_perm_unicity.
      transitivity(lookup m o update m o constant p).
      rewrite assoc. apply strong_subs. rewrite assoc.
      apply strong_subs. apply strong_perm_proj_pi1_rwro. auto.
      transitivity(constant p o update m o constant p).
      specialize(@commutation_lookup_constant m p). intros.
      apply H. apply strong_sym. rewrite assoc. apply strong_subs.
      rewrite assoc. apply strong_subs.
      apply strong_perm_proj_pi1_rwro. auto.
      transitivity(constant q o update m o constant p).
      rewrite assoc. apply weak_subs. rewrite assoc.
      apply weak_subs. apply weak_perm_proj_pi2_rwro. auto.
      apply weak_sym. rewrite assoc. apply weak_subs.
      rewrite assoc. apply weak_subs. 
      apply weak_perm_proj_pi2_rwro. auto.
 Qed. *)

 Lemma perm_strong_pair: forall (m: Loc) (p q: Z),
      (pair (constant q) (lookup m)) o update m o constant p
      ==
      (pair (constant q) (constant p)) o update m o constant p.
 Proof.
      intros. apply strong_unicity.
      transitivity(constant q o update m o constant p).
      rewrite assoc. apply weak_subs. rewrite assoc.
      apply weak_subs. apply weak_proj_pi1_rorw. auto.
      apply weak_sym. rewrite assoc. apply weak_subs.
      rewrite assoc. apply weak_subs. 
      apply weak_proj_pi1_rorw. auto.
      transitivity(lookup m o update m o constant p).
      rewrite assoc. apply strong_subs. rewrite assoc.
      apply strong_subs. apply strong_proj_pi2_rorw. auto.
      transitivity(constant p o update m o constant p).
      specialize(@commutation_lookup_constant m p). intros.
      apply H. apply strong_sym. rewrite assoc. apply strong_subs.
      rewrite assoc. apply strong_subs.
      apply strong_proj_pi2_rorw. auto.
 Qed.

 Lemma IMP_ex7: forall (x: Loc),
      {{x ::= (const 10) ;;
        IFB ((loc x) >> (const 5)) 
          THEN (x ::= (const 2)) 
        ELSE SKIP 
        FI}}
      ==
      {{x ::= (const 2)}}.
 Proof.
    intros.  unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. 
    transitivity((copair (update x o constant 2) id o
    (gt o pair (constant 10) (constant 5))) o (update x o constant 10)).
    rewrite <- assoc. rewrite <- assoc. apply strong_repl. 
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    specialize(@strong_pair x 10 5). intros. rewrite assoc. 
    rewrite assoc. apply H. 
    transitivity((copair (update x o constant 2) id) o ttrue 
    o (update x o constant 10)).
    rewrite <- assoc. rewrite <- assoc.
    apply strong_repl. apply strong_subs. apply IMP_IntGtT. simpl. auto.
    transitivity((update x o constant 2) o (update x o constant 10)).
    apply strong_subs. apply strong_coproj_copi1_rwrw.
    specialize(@IMP_ex3 x 10 2). unfold defCommand.
    unfold defBoolExp. unfold defArithExp. intros. apply H.   
 Qed.

 Lemma IMP_ex8: forall (x: Loc),
      {{x ::= (const 10) ;;
        IFB ((loc x) >>= (const 5))
          THEN (x ::= (const 2)) 
        ELSE SKIP 
        FI}}
      ==
      {{x ::= (const 2)}}.
 Proof.
    intros.  unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. 
    transitivity((copair (update x o constant 2) id o
    (ge o pair (constant 10) (constant 5))) o (update x o constant 10)).
    rewrite <- assoc. rewrite <- assoc. apply strong_repl. 
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    specialize(@strong_pair x 10 5). intros. rewrite assoc. 
    rewrite assoc. apply H. 
    transitivity((copair (update x o constant 2) id) o ttrue 
    o (update x o constant 10)).
    rewrite <- assoc. rewrite <- assoc.
    apply strong_repl. apply strong_subs. apply IMP_IntGeT. simpl. auto.
    transitivity((update x o constant 2) o (update x o constant 10)).
    apply strong_subs. apply strong_coproj_copi1_rwrw.
    specialize(@IMP_ex3 x 10 2). unfold defCommand.
    unfold defBoolExp. unfold defArithExp. intros. apply H.   
 Qed.

 Lemma IMP_ex9: forall (x: Loc) (p: Z),
      {{x ::= (const 10) ;;
        IFB ((loc x) >>= (const 0))
          THEN (SKIP) 
        ELSE (x ::= (loc x *** (const (-1)))) 
        FI}}
      ==
      {{x ::= (const 10) ;;
        IFB ((loc x) <<= (const 0))
          THEN (x ::= (loc x *** (const (-1)))) 
        ELSE (SKIP) 
        FI}}.
 Proof.
    intros. unfold defCommand. unfold defBoolExp. 
    unfold defArithExp.
    transitivity((copair id (update x o (mult o 
    pair (lookup x) (constant (-1)))) o 
    (ge o pair (constant 10) (constant 0))) o 
    (update x o constant 10)).
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    specialize(@strong_pair x 10 0). intros. rewrite assoc. 
    rewrite assoc. apply H.   
    transitivity((copair id (update x o (mult o 
    pair (lookup x) (constant (-1)))) o 
    (ttrue) o (update x o constant 10))).
    apply strong_subs. apply strong_repl.
    apply IMP_IntGeT. simpl. auto.
    transitivity(id o update x o constant 10).
    rewrite assoc. apply strong_subs. apply strong_subs.
    apply strong_coproj_copi1_rwrw. apply strong_sym.
    transitivity((copair (update x o (mult o 
    pair (lookup x) (constant (-1)))) id o 
    (le o pair (constant 10) (constant 0))) o 
    (update x o constant 10)).
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    specialize(@strong_pair x 10 0). intros. 
    rewrite assoc. rewrite assoc. apply H.
    transitivity((copair (update x o (mult o 
    pair (lookup x) (constant (-1)))) id o 
    (ffalse) o (update x o constant 10))).
    apply strong_subs. apply strong_repl.
    apply IMP_IntLeF. simpl. auto.
    rewrite assoc. apply strong_subs. apply strong_subs.
    apply strong_coproj_copi2_rwrw.    
 Qed.

 Lemma IMP_ex10: forall (x: Loc) (p: Z),
      {{x ::= (const (-10)) ;;
        IFB ((loc x) >>= (const 0)) 
          THEN (SKIP) 
        ELSE (x ::= (loc x *** (const (-1)))) 
        FI}}
      ==
      {{x ::= (const (-10)) ;;
        IFB ((loc x) <<= (const 0)) 
          THEN (x ::= ( loc x *** (const (-1)))) 
        ELSE (SKIP) 
        FI}}.
 Proof.
    intros. unfold defCommand. unfold defBoolExp. 
    unfold defArithExp.
    transitivity((copair id (update x o (mult o 
    pair (lookup x) (constant (-1)))) o 
    (ge o pair (constant (-10)) (constant 0))) o 
    (update x o constant (-10))).
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    specialize(@strong_pair x (-10) 0). intros. rewrite assoc. 
    rewrite assoc. apply H.   
    transitivity((copair id (update x o (mult o 
    pair (lookup x) (constant (-1)))) o 
    (ffalse) o (update x o constant (-10)))).
    apply strong_subs. apply strong_repl.
    apply IMP_IntGeF. simpl. auto.
    transitivity((update x o (mult o pair  (lookup x) (constant (-1)))
    o (update x o constant (-10)))).
    apply strong_subs. apply strong_coproj_copi2_rwrw.
    transitivity(update x o mult o 
    pair (constant (-10)) (constant (-1))
    o update x o (constant (-10))). apply strong_sym.
    rewrite <- assoc. rewrite <- assoc.
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. apply strong_repl. apply strong_unicity.
    apply weak_sym.
    transitivity(lookup x o update x o (constant (-10))).
    rewrite assoc. rewrite assoc. apply weak_subs. apply weak_subs.
    apply weak_proj_pi1_rorw. auto.
    transitivity(id o (constant (-10))). apply weak_subs. apply axiom_1.
    apply weak_sym.
    transitivity((constant (-10)) o (update x o constant (-10))).
    rewrite assoc. apply weak_subs. apply weak_proj_pi1_rorw. auto.
    transitivity((constant (-10)) o id). apply zero_weak_repl. auto.
    apply weak_final_unique. rewrite id_tgt. rewrite id_src. apply weak_refl.
    
    transitivity((constant (-1)) o update x o (constant (-10))).
    rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
    apply strong_proj_pi2_rorw. auto. apply strong_sym.
    transitivity((constant (-1)) o update x o (constant (-10))).
    rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
    apply strong_proj_pi2_rorw. auto. apply strong_refl.
    transitivity(update x o (constant 10) o update x o (constant (-10))).
    apply strong_subs. apply strong_subs. rewrite <- assoc.
    apply strong_repl. apply IMP_IntMult.
    transitivity(update x o constant 10).
    specialize(@IMP_ex3 x (-10) 10). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. rewrite <- assoc. apply H. apply strong_sym.

    transitivity((copair (update x o (mult o 
    pair (lookup x) (constant (-1)))) id o 
    (le o pair (constant (-10)) (constant 0))) o 
    (update x o constant (-10))).
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    specialize(@strong_pair x (-10) 0). intros.
    rewrite assoc. rewrite assoc. apply H.
    transitivity((copair (update x o (mult o 
    pair (lookup x) (constant (-1)))) id o 
    (ttrue) o (update x o constant (-10)))).
    apply strong_subs. apply strong_repl. apply IMP_IntLeT.
    simpl. auto.
    transitivity((update x o (mult o pair (lookup x) (constant (-1))) o 
    (update x o constant (-10)))).
    apply strong_subs. apply strong_coproj_copi1_rwrw.
    transitivity(update x o mult o pair (constant (-10)) (constant (-1)) o 
    update x o (constant (-10))). apply strong_sym. rewrite <- assoc.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. apply strong_repl. apply strong_sym.
    specialize(@strong_pair x (-10) (-1)). intros. rewrite assoc.
    rewrite assoc. apply H.
    transitivity(update x o (constant 10) o update x o (constant (-10))).
    apply strong_subs. apply strong_subs. rewrite <- assoc. 
    apply strong_repl. apply IMP_IntMult.  
    specialize(@IMP_ex3 x (-10) 10). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. rewrite <- assoc. apply H. 
 Qed.

 Lemma IMP_ex11: forall (x: Loc) (p: Z),
      {{x ::= (const 0) ;;
        IFB ((loc x) >>= (const 0)) 
          THEN (SKIP) 
        ELSE (x ::= (loc x *** (const (-1)))) 
        FI}}
      ==
      {{x ::= (const 0) ;;
        IFB ((loc x) <<= (const 0))
          THEN (x ::= ( loc x *** (const (-1)))) 
        ELSE (SKIP) 
        FI}}.
 Proof.
    intros. unfold defCommand. unfold defBoolExp. 
    unfold defArithExp.
    transitivity((copair id (update x o 
    (mult o pair (lookup x) (constant (-1)))) o 
    (ge o pair (constant 0) (constant 0))) o (update x o constant 0)).
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    specialize(@strong_pair x 0 0). intros.
    rewrite assoc. rewrite assoc. apply H.
    transitivity((copair id (update x o 
    (mult o pair (lookup x) (constant (-1)))) o 
    (ttrue) o (update x o constant 0))).
    apply strong_subs. apply strong_repl.
    apply IMP_IntGeT. simpl. auto.
    transitivity(id o update x o constant 0).
    rewrite assoc. apply strong_subs. apply strong_subs.
    apply strong_coproj_copi1_rwrw. rewrite <- assoc.
    rewrite id_tgt. apply strong_sym.

    transitivity((copair (update x o 
    (mult o pair (lookup x) (constant (-1)))) id o 
    (le o pair (constant 0) (constant 0))) o (update x o constant 0)).
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    specialize(@strong_pair x 0 0). intros.
    rewrite assoc. rewrite assoc. apply H.
    transitivity((copair (update x o 
    (mult o pair (lookup x) (constant (-1)))) id o 
    (ttrue) o (update x o constant 0))).
    apply strong_subs. apply strong_repl.
    apply IMP_IntLeT. simpl. auto.
    transitivity((update x o (mult o pair (lookup x) (constant (-1))))
    o update x o constant 0).
    rewrite assoc. apply strong_subs. apply strong_subs.
    apply strong_coproj_copi1_rwrw.
    transitivity(update x o mult o pair (constant 0) (constant (-1)) 
    o update x o constant 0 ). apply strong_sym.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. 
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. apply strong_repl. apply strong_sym.
    specialize(@strong_pair x 0 (-1)). intros.
    rewrite assoc. rewrite assoc. apply H.
    transitivity(update x o (constant 0) o update x o (constant 0)).
    apply strong_subs. apply strong_subs. rewrite <- assoc.
    apply strong_repl. apply IMP_IntMult.
    specialize(@IMP_ex3 x 0 0). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. rewrite <- assoc. apply H. 
 Qed.

 Lemma IMP_perm_ex11: forall (x: Loc) (p: Z),
      {{x ::= (const 0) ;;
        IFB ((loc x) >>= (const 0)) 
          THEN (SKIP) 
        ELSE (x ::= ((const (-1)) *** loc x)) 
        FI}}
      ==
      {{x ::= (const 0) ;;
        IFB ((loc x) <<= (const 0))
          THEN (x ::= ((const (-1)) *** loc x)) 
        ELSE (SKIP) 
        FI}}.
 Proof.
    intros. unfold defCommand. unfold defBoolExp. 
    unfold defArithExp.
    transitivity((copair id (update x o 
    (mult o pair (constant (-1)) (lookup x))) o 
    (ge o pair (constant 0) (constant 0))) o (update x o constant 0)).
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    specialize(@strong_pair x 0 0). intros.
    rewrite assoc. rewrite assoc. apply H.
    transitivity((copair id (update x o 
    (mult o pair (constant (-1)) (lookup x))) o 
    (ttrue) o (update x o constant 0))).
    apply strong_subs. apply strong_repl.
    apply IMP_IntGeT. simpl. auto.
    transitivity(id o update x o constant 0).
    rewrite assoc. apply strong_subs. apply strong_subs.
    apply strong_coproj_copi1_rwrw. rewrite <- assoc.
    rewrite id_tgt. apply strong_sym.

    transitivity((copair (update x o 
    (mult o pair (constant (-1)) (lookup x))) id o 
    (le o pair (constant 0) (constant 0))) o (update x o constant 0)).
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    specialize(@strong_pair x 0 0). intros.
    rewrite assoc. rewrite assoc. apply H.
    transitivity((copair (update x o 
    (mult o pair (constant (-1)) (lookup x))) id o 
    (ttrue) o (update x o constant 0))).
    apply strong_subs. apply strong_repl.
    apply IMP_IntLeT. simpl. auto.
    transitivity((update x o (mult o pair (constant (-1)) (lookup x)))
    o update x o constant 0).
    rewrite assoc. apply strong_subs. apply strong_subs.
    apply strong_coproj_copi1_rwrw.
    transitivity(update x o mult o (pair (constant (-1)) (constant 0)) 
    o update x o constant 0). apply strong_sym.
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc. 
    rewrite <- assoc. rewrite <- assoc. apply strong_repl.
    rewrite <- assoc. apply strong_repl. apply strong_sym.
    specialize(@perm_strong_pair x 0 (-1)). intros.
    rewrite assoc. rewrite assoc. apply H.
    transitivity(update x o (constant 0) o update x o (constant 0)).
    apply strong_subs. apply strong_subs. rewrite <- assoc.
    apply strong_repl. apply IMP_IntMult.
    specialize(@IMP_ex3 x 0 0). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. rewrite <- assoc. apply H. 
 Qed.

 Lemma IMP_ex12: forall (x y: Loc), x <> y ->
       {{x ::= (const 5) ;; y ::= (loc x)}}
       ==
       {{y ::= (const 5) ;; x ::= (loc y)}}.
 Proof.
    intros. unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. apply strong_sym.
    transitivity(update x o constant 5 o update y o constant 5).
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    apply strong_repl. remember commutation_lookup_constant.
    specialize(@commutation_lookup_constant y 5).
    intros. rewrite assoc. rewrite assoc. apply H0.
    apply strong_sym. 
    transitivity(update y o constant 5 o update x o constant 5).
    rewrite <- assoc. rewrite <- assoc. rewrite <- assoc.
    apply strong_repl. remember commutation_lookup_constant.
    specialize(@commutation_lookup_constant x 5).
    intros. rewrite assoc. rewrite assoc. apply H0.
    rewrite <- assoc. specialize(@IMP_ex1 y x 5 5).
    unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. apply strong_sym.
    rewrite <- assoc. apply H0. auto.
 Qed.
 
 Lemma IMP_ex13: forall (x y: Loc), x <> y ->
       {{x ::= (const 10) ;;
         y ::= (const 3) ;;
        IFB ((loc x) >>= (loc y) *** (const 3))
          THEN (x ::= (loc y)) 
        ELSE (SKIP) 
        FI}}
        ==
       {{x ::= (const 10) ;;
         y ::= (const 3) ;;
        IFB ((loc x) >>= (const 4) *** (loc y)) 
          THEN (SKIP) 
        ELSE (x ::= (loc y)) 
        FI}}.
 Proof.
    intros. unfold defCommand. unfold defBoolExp. 
    unfold defArithExp.
    transitivity(copair (update x o lookup y) id o 
    ge o pair (lookup x) (mult o pair (constant 3) (constant 3)) o 
    update y o constant 3  o update x o constant 10).
    apply strong_sym. repeat rewrite <- assoc.
    apply strong_repl. repeat rewrite assoc.
    repeat apply strong_subs. repeat rewrite <- assoc.
    apply strong_repl. apply strong_unicity. 
    transitivity(lookup x o update y o constant 3).
    rewrite assoc. rewrite assoc. apply weak_subs. 
    apply weak_subs. apply weak_proj_pi1_rorw. auto. 
    apply weak_sym. repeat rewrite assoc. repeat apply weak_subs.
    apply weak_proj_pi1_rorw. auto.
    transitivity( (mult o pair (constant 3) (constant 3)) o 
    (update y o constant 3)). rewrite assoc. apply strong_subs.
    apply strong_proj_pi2_rorw. auto. apply strong_sym.
    transitivity((mult o pair (lookup y) (constant 3)) o 
    (update y o constant 3)). rewrite assoc. apply strong_subs.
    apply strong_proj_pi2_rorw. auto. repeat rewrite <- assoc. 
    apply strong_repl. specialize(@strong_pair y 3 3). intros.
    repeat rewrite assoc. apply H0.
    transitivity(copair (update x o lookup y) id o ge o
    (pair (lookup x) (constant 9)) o update y o
    constant 3 o update x o constant 10).
    repeat apply strong_subs. apply strong_repl. apply strong_unicity.
    transitivity(lookup x). apply weak_proj_pi1_rorw. auto.
    apply weak_sym. apply weak_proj_pi1_rorw. auto.
    transitivity(mult o pair (constant 3) (constant 3)).
    apply strong_proj_pi2_rorw. auto. apply strong_sym.
    transitivity(constant 9). apply strong_proj_pi2_rorw. auto.
    apply strong_sym. apply IMP_IntMult.
    transitivity(copair (update x o lookup y) id o ge o 
    (pair (lookup x) (constant 9)) o (update x o constant 10) 
    o (update y o constant 3)). repeat rewrite <- assoc.
    repeat apply strong_repl. rewrite assoc. specialize(@IMP_ex1 x y 10 3).
    unfold defCommand. unfold defBoolExp. unfold defArithExp.
    intros. apply H0. assumption.
    transitivity((((copair (update x o lookup y) id o ge) o
    pair (constant 10) (constant 9)) o (update x o constant 10)) o
    (update y o constant 3)). apply strong_subs. repeat rewrite <- assoc.
    repeat apply strong_repl. specialize(@strong_pair x 10 9). intros.
    repeat rewrite assoc. apply H0.
    transitivity((((copair (update x o lookup y) id o ttrue o 
    (update x o constant 10)) o (update y o constant 3)))).
    repeat apply strong_subs. rewrite <- assoc.
    apply strong_repl. apply IMP_IntGeT. simpl. auto.
    transitivity((update x o lookup y) o
    (update x o constant 10) o (update y o constant 3)).
    repeat apply strong_subs. apply strong_coproj_copi1_rwrw.
    transitivity(update x o lookup y o update y o constant 3
    o update x o constant 10). apply strong_sym.
    repeat rewrite <- assoc. repeat apply strong_repl. rewrite assoc.    
    specialize(@IMP_ex1 x y 10 3). unfold defCommand.
    unfold defBoolExp. unfold defArithExp. intros.
    apply H0. assumption.
    transitivity(update x o constant 3 o update y o constant 3
    o update x o constant 10).
    apply strong_subs. apply strong_subs. repeat rewrite <- assoc.
    apply strong_repl. specialize(@commutation_lookup_constant y 3).
    intros. repeat rewrite assoc. apply H0.
    transitivity(update x o constant 3 o update x o constant 10
    o update y o constant 3). repeat rewrite <- assoc.
    repeat apply strong_repl. rewrite assoc.
    apply strong_sym. rewrite assoc. specialize(@IMP_ex1 y x 3 10).
    unfold defCommand. unfold defBoolExp. unfold defArithExp.
    intros. apply H0. auto.
    transitivity(update x o constant 3 o update y o constant 3).
    repeat apply strong_subs. rewrite <- assoc.
    specialize(@IMP_ex3 x 10 3). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. apply H0. rewrite <- assoc.
    (*first program is reduced into following form: x ::= 3 ;; y ::= 3*)
    apply strong_sym.

    transitivity(copair id (update x o lookup y) o 
    ge o pair (lookup x) (mult o pair (constant 4) (constant 3)) o 
    update y o constant 3  o update x o constant 10).
    apply strong_sym. repeat rewrite <- assoc. apply strong_repl.
    repeat rewrite assoc. repeat apply strong_subs. 
    repeat rewrite <- assoc. apply strong_repl. apply strong_unicity. 
    transitivity(lookup x o update y o constant 3).
    rewrite assoc. rewrite assoc. repeat apply weak_subs. 
    apply weak_proj_pi1_rorw. auto. apply weak_sym. 
    repeat rewrite assoc. repeat apply weak_subs.
    apply weak_proj_pi1_rorw. auto.
    transitivity( (mult o pair (constant 4) (constant 3)) o 
    (update y o constant 3)). rewrite assoc. apply strong_subs.
    apply strong_proj_pi2_rorw. auto. apply strong_sym.
    transitivity((mult o pair (constant 4) (lookup y)) o 
    (update y o constant 3)). rewrite assoc. apply strong_subs.
    apply strong_proj_pi2_rorw. auto. rewrite <- assoc.
    rewrite <- assoc. apply strong_repl.
    specialize(@perm_strong_pair y 3 4). intros. repeat rewrite assoc.
    apply H0. transitivity(copair id (update x o lookup y) o ge o
    (pair (lookup x) (constant 12)) o update y o
    constant 3 o update x o constant 10).
    repeat apply strong_subs. apply strong_repl. apply strong_unicity.
    transitivity(lookup x). apply weak_proj_pi1_rorw. auto.
    apply weak_sym. apply weak_proj_pi1_rorw. auto.
    transitivity(mult o pair (constant 4) (constant 3)).
    apply strong_proj_pi2_rorw. auto. apply strong_sym.
    transitivity(constant 12). apply strong_proj_pi2_rorw. auto.
    apply strong_sym. apply IMP_IntMult.
    transitivity(copair id (update x o lookup y) o ge o 
    (pair (lookup x) (constant 12)) o (update x o constant 10) 
    o (update y o constant 3)). repeat rewrite <- assoc.
    repeat apply strong_repl. rewrite assoc. specialize(@IMP_ex1 x y 10 3).
    unfold defCommand. unfold defBoolExp. unfold defArithExp.
    intros. apply H0. assumption.
    transitivity((((copair id (update x o lookup y) o ge) o
    pair (constant 10) (constant 12)) o (update x o constant 10)) o
    (update y o constant 3)). apply strong_subs. repeat rewrite <- assoc.
    repeat apply strong_repl. specialize(@strong_pair x 10 12). intros.
    rewrite assoc. rewrite assoc. apply H0.
    transitivity((((copair id (update x o lookup y) o ffalse o 
    (update x o constant 10)) o (update y o constant 3)))).
    repeat apply strong_subs. rewrite <- assoc.
    apply strong_repl. apply IMP_IntGeF. simpl. auto.
    transitivity((update x o lookup y) o
    (update x o constant 10) o (update y o constant 3)).
    repeat apply strong_subs. apply strong_coproj_copi2_rwrw.
    transitivity(update x o lookup y o update y o constant 3
    o update x o constant 10). apply strong_sym.
    repeat rewrite <- assoc. repeat apply strong_repl.
    rewrite assoc. specialize(@IMP_ex1 x y 10 3). 
    unfold defCommand. unfold defBoolExp. unfold defArithExp.
    intros. apply H0. assumption.
    transitivity(update x o constant 3 o update y o constant 3
    o update x o constant 10).
    apply strong_subs. apply strong_subs. repeat rewrite <- assoc.
    apply strong_repl. specialize(@commutation_lookup_constant y 3).
    intros. repeat rewrite assoc. apply H0.
    transitivity(update x o constant 3 o update x o constant 10
    o update y o constant 3). repeat rewrite <- assoc.
    repeat apply strong_repl. rewrite assoc. apply strong_sym.
    rewrite assoc. specialize(@IMP_ex1 y x 3 10).
    unfold defCommand. unfold defBoolExp. unfold defArithExp.
    intros. apply H0. auto.
    transitivity(update x o constant 3 o update y o constant 3).
    repeat apply strong_subs. rewrite <- assoc.
    specialize(@IMP_ex3 x 10 3). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. apply H0. rewrite <- assoc.
    (*second program is reduced into following form: x ::= 3 ;; y ::= 3*)
    apply strong_refl.
 Qed. 

 Lemma IMP_ex14: forall (x: Loc),
       {{x ::= (const 10) ;;
        IFB ((loc x) >>= (const 0)) 
          THEN (IFB ((loc x) === (const 10))
                  THEN (x ::= (const 20))
                ELSE (SKIP)
                FI)
        ELSE (x ::= (const 30)) 
        FI}}
        ==
       {{x ::= (const 20)}}.
 Proof.
    intros. unfold defCommand. unfold defBoolExp. 
    unfold defArithExp.
    transitivity((copair (copair (update x o constant 20) id o 
    (eq o pair (lookup x) (constant 10)))
    (update x o constant 30) o (ge o pair (constant 10) (constant 0))) o 
    (update x o constant 10)).
    repeat rewrite <- assoc. apply strong_repl. repeat rewrite <- assoc.
    apply strong_repl. specialize(@strong_pair x 10 0). intros.
    repeat rewrite assoc. apply H.
    transitivity((copair (copair (update x o constant 20) id o
    (eq o pair (lookup x) (constant 10))) (update x o constant 30) 
    o (ttrue) o (update x o constant 10))).
    repeat rewrite <- assoc. apply strong_repl. apply strong_subs.
    apply IMP_IntGeT. simpl. auto.
    transitivity((copair (update x o constant 20) id o 
    (eq o pair (lookup x) (constant 10))) o (update x o constant 10)).
    repeat rewrite assoc. repeat apply strong_subs. 
    apply strong_coproj_copi1_rwrw.
    transitivity((copair (update x o constant 20) id o 
    (eq o pair (constant 10) (constant 10))) o
    (update x o constant 10)). repeat rewrite <- assoc.
    apply strong_repl. repeat rewrite <- assoc. apply strong_repl.
    specialize(@strong_pair x 10 10). intros. repeat rewrite assoc.
    apply H. 
    transitivity((copair (update x o constant 20) id o 
    (ttrue) o (update x o constant 10))). apply strong_subs.
    apply strong_repl. apply IMP_IntEqT. simpl. auto.
    transitivity((update x o constant 20) o (update x o constant 10)).
    apply strong_subs. apply strong_coproj_copi1_rwrw.
    specialize(@IMP_ex3 x 10 20). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. apply H.    
 Qed.

 Lemma IMP_ex15: forall (x: Loc),
	{{x ::= (const 2) ;;
	  WHILE ((loc x) << (const 11))
	    DO (x ::= ((loc x) +++ (const 4)))}}
	==
	{{x ::= (const 14)}}.
 Proof.
    intros. unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. 
    transitivity((copair (loopdec o (update x o 
    (plus o pair (lookup x) (constant 4)))) id o 
    (lt o pair (constant 2) (constant 11))) o (update x o constant 2)).
    repeat rewrite <- assoc. apply strong_repl. repeat rewrite <- assoc.
    apply strong_repl. specialize(@strong_pair x 2 11). intros.
    repeat rewrite assoc. apply H. 
    transitivity((copair (loopdec o (update x o 
    (plus o pair (lookup x) (constant 4)))) id o 
    (ttrue) o (update x o constant 2))).
    apply strong_subs. apply strong_repl. apply IMP_IntLtT. simpl. auto.
    transitivity(loopdec o (update x o (plus o pair (lookup x) (constant 4))) o 
    update x o constant 2). rewrite assoc. repeat apply strong_subs.
    apply strong_coproj_copi1_rwrw. rewrite <- assoc.
    transitivity(loopdec o update x o plus o (pair (constant 2) (constant 4)) o
    update x o constant 2). apply strong_sym. repeat rewrite <- assoc. 
    apply strong_repl. rewrite <- assoc. apply strong_repl. rewrite <- assoc. 
    apply strong_repl. specialize(@strong_pair x 2 4). intros. apply strong_sym.
    repeat rewrite assoc. apply H. 
    transitivity(loopdec o update x o constant 6 o update x o constant 2).
    repeat apply strong_subs. rewrite <- assoc. apply strong_repl.
    apply IMP_IntAdd.
    transitivity(loopdec o update x o constant 6).
    repeat rewrite <- assoc. apply strong_repl. rewrite assoc.
    specialize(@IMP_ex3 x 2 6). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. apply H. 

    transitivity((copair (loopdec o (update x o 
    (plus o pair (lookup x) (constant 4)))) id o 
    (lt o pair (lookup x) (constant 11))) o (update x o constant 6)).

    remember IMP_Loop.

    specialize(@IMP_Loop (lt o pair (lookup x) (constant 11)) 
    (update x o (plus o pair (lookup x) (constant 4))) (loopdec)).
    intros. rewrite assoc. repeat apply strong_subs. apply H.

    transitivity((copair (loopdec o (update x o 
    (plus o pair (lookup x) (constant 4)))) id o 
    (lt o pair (constant 6) (constant 11))) o (update x o constant 6)).
    repeat rewrite <- assoc. apply strong_repl. repeat rewrite <- assoc.
    apply strong_repl. specialize(@strong_pair x 6 11). intros.
    repeat rewrite assoc. apply H. 
    transitivity((copair (loopdec o (update x o 
    (plus o pair (lookup x) (constant 4)))) id o 
    (ttrue) o (update x o constant 6))).
    apply strong_subs. apply strong_repl. apply IMP_IntLtT. simpl. auto.
    transitivity(loopdec o (update x o (plus o pair (lookup x) (constant 4))) o 
    update x o constant 6). rewrite assoc. repeat apply strong_subs.
    apply strong_coproj_copi1_rwrw. rewrite <- assoc.
    transitivity(loopdec o update x o plus o (pair (constant 6) (constant 4)) o
    update x o constant 6). apply strong_sym. repeat rewrite <- assoc. 
    apply strong_repl. rewrite <- assoc. apply strong_repl. rewrite <- assoc. 
    apply strong_repl. specialize(@strong_pair x 6 4). intros. apply strong_sym.
    repeat rewrite assoc. apply H. 
    transitivity(loopdec o update x o constant 10 o update x o constant 6).
    repeat apply strong_subs. rewrite <- assoc. apply strong_repl.
    apply IMP_IntAdd.
    transitivity(loopdec o update x o constant 10).
    repeat rewrite <- assoc. apply strong_repl. rewrite assoc.
    specialize(@IMP_ex3 x 6 10). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. apply H. 

    transitivity((copair (loopdec o (update x o 
    (plus o pair (lookup x) (constant 4)))) id o 
    (lt o pair (lookup x) (constant 11))) o (update x o constant 10)).

    remember IMP_Loop.

    specialize(@IMP_Loop (lt o pair (lookup x) (constant 11)) 
    (update x o (plus o pair (lookup x) (constant 4))) (loopdec)).
    intros. rewrite assoc. repeat apply strong_subs. apply H.

    transitivity((copair (loopdec o (update x o 
    (plus o pair (lookup x) (constant 4)))) id o 
    (lt o pair (constant 10) (constant 11))) o (update x o constant 10)).
    repeat rewrite <- assoc. apply strong_repl. repeat rewrite <- assoc.
    apply strong_repl. specialize(@strong_pair x 10 11). intros.
    repeat rewrite assoc. apply H. 
    transitivity((copair (loopdec o (update x o 
    (plus o pair (lookup x) (constant 4)))) id o 
    (ttrue) o (update x o constant 10))).
    apply strong_subs. apply strong_repl. apply IMP_IntLtT. simpl. auto.
    transitivity(loopdec o (update x o (plus o pair (lookup x) (constant 4))) o 
    update x o constant 10). rewrite assoc. repeat apply strong_subs.
    apply strong_coproj_copi1_rwrw. rewrite <- assoc.
    transitivity(loopdec o update x o plus o (pair (constant 10) (constant 4)) o
    update x o constant 10). apply strong_sym. repeat rewrite <- assoc. 
    apply strong_repl. rewrite <- assoc. apply strong_repl. rewrite <- assoc. 
    apply strong_repl. specialize(@strong_pair x 10 4). intros. apply strong_sym.
    repeat rewrite assoc. apply H. 
    transitivity(loopdec o update x o constant 14 o update x o constant 10).
    repeat apply strong_subs. rewrite <- assoc. apply strong_repl.
    apply IMP_IntAdd.
    transitivity(loopdec o update x o constant 14).
    repeat rewrite <- assoc. apply strong_repl. rewrite assoc.
    specialize(@IMP_ex3 x 10 14). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. apply H. 

    transitivity((copair (loopdec o (update x o 
    (plus o pair (lookup x) (constant 4)))) id o 
    (lt o pair (lookup x) (constant 11))) o (update x o constant 14)).

    remember IMP_Loop.

    specialize(@IMP_Loop (lt o pair (lookup x) (constant 11)) 
    (update x o (plus o pair (lookup x) (constant 4))) (loopdec)).
    intros. rewrite assoc. repeat apply strong_subs. apply H.

    transitivity((copair (loopdec o (update x o 
    (plus o pair (lookup x) (constant 4)))) id o 
    (lt o pair (constant 14) (constant 11))) o (update x o constant 14)).
    repeat rewrite <- assoc. apply strong_repl. repeat rewrite <- assoc.
    apply strong_repl. specialize(@strong_pair x 14 11). intros.
    repeat rewrite assoc. apply H. 
    transitivity((copair (loopdec o (update x o 
    (plus o pair (lookup x) (constant 4)))) id o 
    (ffalse) o (update x o constant 14))).
    apply strong_subs. apply strong_repl. apply IMP_IntLtF. simpl. auto.
    transitivity(id o (update x o constant 14)). apply strong_subs.
    apply strong_coproj_copi2_rwrw. rewrite id_tgt. apply strong_refl.
 Qed.
       

 Lemma IMP_ex16: orB o (pair (le o (pair (@constant Z 80) (@constant Z 80)))
 (lt o (pair (@constant Z 180) (@constant Z 80))))
       == 
      ttrue.
 Proof.
    apply IMP_IntOrT. left.
    transitivity((le o pair (constant 80) (constant 80))).
    apply strong_proj_pi1_purepure. auto. auto.
    apply IMP_IntLeT. simpl. auto.
 Qed.

 Lemma IMP_ex17: orB o (pair (lt o (pair (@constant Z 80) (@constant Z 80)))
 (lt o (pair (@constant Z 180) (@constant Z 80))))
       == 
      ffalse.
 Proof.
    apply IMP_IntOrF. 
    transitivity((lt o pair (constant 80) (constant 80))).
    apply strong_proj_pi1_purepure. auto. auto.
    apply IMP_IntLtF. simpl. auto.
    transitivity((lt o pair (constant 180) (constant 80))).
    apply strong_proj_pi2_purepure. auto. auto.
    apply IMP_IntLtF. simpl. auto.
 Qed.

 Lemma IMP_ex18: andB o (pair (le o (pair (@constant Z 80) (@constant Z 80)))
 (lt o (pair (@constant Z 180) (@constant Z 80))))
       == 
      ffalse.
 Proof.
    apply IMP_IntAndF. right.
    transitivity((lt o pair (constant 180) (constant 80))).
    apply strong_proj_pi2_purepure. auto. auto.
    apply IMP_IntLtF. simpl. auto.
 Qed.

 Lemma IMP_ex19: andB o (pair (le o (pair (@constant Z 80) (@constant Z 80)))
 (gt o (pair (@constant Z 180) (@constant Z 80))))
       == 
      ttrue.
 Proof.
    apply IMP_IntAndT. 
    transitivity((le o pair (constant 80) (constant 80))).
    apply strong_proj_pi1_purepure. auto. auto.
    apply IMP_IntLeT. simpl. auto.
    transitivity((gt o pair (constant 180) (constant 80))).
    apply strong_proj_pi2_purepure. auto. auto.
    apply IMP_IntGtT. simpl. auto.
 Qed.

 Lemma IMP_ex20: forall (x: Loc),
       {{x ::= (const 50) ;;
         IFB ((loc x) << (const 70) &&& (loc x) >> (const 40))
           THEN (x ::= (const 10))
         ELSE (SKIP)
         FI}}
       ==
       {{x ::= (const 10)}}.
 Proof.
    intros. unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. 
    transitivity((copair (update x o constant 10) id o 
    (andB o pair (lt o pair (constant 50) (constant 70))
    (gt o pair (constant 50) (constant 40)))) o (update x o constant 50)).
    repeat rewrite <- assoc. apply strong_repl. repeat rewrite <- assoc.
    apply strong_repl. apply strong_unicity.
    transitivity(lt o (pair (lookup x) (constant 70)) o
    (update x o constant 50)). rewrite assoc.
    apply weak_subs. apply weak_proj_pi1_rorw. auto.
    apply weak_sym.
    transitivity(lt o (pair (constant 50) (constant 70)) o
    (update x o constant 50)). rewrite assoc. apply weak_subs.
    apply weak_proj_pi1_rorw. auto. apply strong_to_weak. apply strong_sym.
    specialize(@strong_pair x 50 70). intros.
    repeat rewrite <- assoc. apply strong_repl. repeat rewrite assoc. apply H.
    
    transitivity((gt o pair (lookup x) (constant 40)) o (update x o constant 50)).
    rewrite assoc. apply strong_subs. apply strong_proj_pi2_rorw. auto.
    transitivity((gt o pair (constant 50) (constant 40)) o (update x o constant 50)).
    specialize(@strong_pair x 50 40). intros.
    repeat rewrite <- assoc. apply strong_repl. repeat rewrite assoc. apply H.
    apply strong_sym. rewrite assoc. apply strong_subs.
    apply strong_proj_pi2_rorw. auto.

    transitivity((copair (update x o constant 10) id o (andB
    o (pair ttrue ttrue) o (update x o constant 50)))).
    rewrite <- assoc. apply strong_repl. apply strong_subs.
    apply strong_repl. apply strong_unicity.
    transitivity(lt o pair (constant 50) (constant 70)).
    apply weak_proj_pi1_rorw. auto. transitivity(ttrue).
    apply strong_to_weak. apply IMP_IntLtT. simpl. auto.
    apply weak_sym. apply weak_proj_pi1_rorw. apply is_pure_ro. apply is_ttrue.
    transitivity(gt o pair (constant 50) (constant 40)).
    apply strong_proj_pi2_rorw. auto. transitivity(ttrue).
    apply IMP_IntGtT. simpl. auto. apply strong_sym.
    apply strong_proj_pi2_rorw. apply is_pure_ro. apply is_ttrue.
    
    transitivity(copair (update x o constant 10) id o 
    ttrue o (update x o constant 50)).
    apply strong_sym. rewrite <- assoc. apply strong_repl.
    apply strong_subs. apply strong_sym. apply IMP_IntAndT.
    apply strong_proj_pi1_purepure. apply is_ttrue. apply is_ttrue.
    apply strong_proj_pi2_purepure. apply is_ttrue. apply is_ttrue.

    transitivity((update x o constant 10) o (update x o constant 50)).
    apply strong_subs. apply strong_coproj_copi1_rwrw.
   
    specialize(@IMP_ex3 x 50 10). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. apply H.    
 Qed.

End Make.
