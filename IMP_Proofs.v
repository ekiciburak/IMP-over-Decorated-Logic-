(**************************************************************************)
(*  This is part of IMP-STATES, it is distributed under the terms of the  *)
(*              GNU Lesser General Public License version 3               *)
(*                  (see file LICENSE for more details)                   *)
(*                                                                        *)
(*       Copyright 2014: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory Terms Decorations Derived_Terms Axioms
Derived_Rules IMP_to_COQ.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.

Module Make(Import M: Memory.T).
  Module Export ConversionExp := IMP_to_COQ.Make(M).

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
         ENDIF}}
       ==
       {{IFB (constF ffalse) 
           THEN (SKIP) 
         ELSE (m ::= const (-30))
         ENDIF}}.
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
     apply observation. intros. destruct(Loc_dec i x). rewrite e.
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
     transitivity(lookup i o forget o constant q o update x o constant p).
     rewrite assoc. rewrite assoc. apply weak_subs. apply weak_subs.
     rewrite assoc. apply weak_subs. apply axiom_2. auto.
     transitivity(lookup i o id o update x o constant p).
     apply weak_subs. apply weak_subs. apply strong_to_weak. 
     rewrite <- assoc. apply strong_repl. apply zero_weak_to_strong.
     auto. auto. apply weak_final_unique.
     transitivity(lookup i o forget o constant p).
     apply weak_subs.
     transitivity(lookup i o update x).
     apply weak_subs. rewrite id_src. apply weak_refl.
     apply axiom_2. auto.
     transitivity(lookup i o id). apply strong_to_weak.
     rewrite <- assoc. apply strong_repl. apply zero_weak_to_strong.
     auto. auto. apply weak_final_unique. apply weak_sym.
     transitivity(lookup i o forget o constant q).
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
     apply one_weak_to_strong. auto. auto.
     apply weak_proj_pi1_rorw. auto.
     remember commutation_lookup_constant.
     specialize(@commutation_lookup_constant x p). intros.
     apply strong_sym. apply H.
     transitivity(constant q o update x o constant p).
     rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
     apply strong_proj_pi2_rorw. auto. apply strong_sym.
     transitivity(constant q o update x o constant p).
     rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
     apply strong_proj_pi2_rorw. auto. apply strong_refl.
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
     apply one_weak_to_strong. auto. auto.
     apply weak_proj_pi1_rorw. auto.
     remember commutation_lookup_constant.
     specialize(@commutation_lookup_constant x p). intros.
     apply strong_sym. apply H.
     transitivity(constant q o update x o constant p).
     rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
     apply strong_proj_pi2_rorw. auto. apply strong_sym.
     transitivity(constant q o update x o constant p).
     rewrite assoc. rewrite assoc. apply strong_subs. apply strong_subs.
     apply strong_proj_pi2_rorw. auto. apply strong_refl.
     transitivity((update x o constant (p*q) o (update x o constant p))).
     apply strong_subs. apply strong_repl. apply IMP_IntMult.
     
     remember IMP_ex3.
     specialize(@IMP_ex3 x p (p*q)). intros. simpl in H. apply H.
 Qed.

 Lemma IMP_ex6: forall (x: Loc),
      {{WHILE (constF ffalse) 
          DO (x ::= (const 2))
	ENDWHILE ;; 
        SKIP}}
      ==
      {{SKIP}}.
 Proof.
     intros. unfold defCommand. unfold defArithExp.
     unfold defBoolExp. rewrite id_tgt.
     apply strong_coproj_copi2_rwrw.
 Qed.

 Lemma IMP_ex7: forall (x: Loc),
      {{x ::= (const 10) ;;
        IFB ((loc x) >> (const 5)) 
          THEN (x ::= (const 2)) 
        ELSE SKIP 
        ENDIF}}
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
        ENDIF}}
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
        ENDIF}}
      ==
      {{x ::= (const 10) ;;
        IFB ((loc x) <<= (const 0))
          THEN (x ::= (loc x *** (const (-1)))) 
        ELSE (SKIP) 
        ENDIF}}.
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
        ENDIF}}
      ==
      {{x ::= (const (-10)) ;;
        IFB ((loc x) <<= (const 0)) 
          THEN (x ::= ( loc x *** (const (-1)))) 
        ELSE (SKIP) 
        ENDIF}}.
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
        ENDIF}}
      ==
      {{x ::= (const 0) ;;
        IFB ((loc x) <<= (const 0))
          THEN (x ::= ( loc x *** (const (-1)))) 
        ELSE (SKIP) 
        ENDIF}}.
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
        ENDIF}}
      ==
      {{x ::= (const 0) ;;
        IFB ((loc x) <<= (const 0))
          THEN (x ::= ((const (-1)) *** loc x)) 
        ELSE (SKIP) 
        ENDIF}}.
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
        ENDIF}}
        ==
       {{x ::= (const 10) ;;
         y ::= (const 3) ;;
        IFB ((loc x) >>= (const 4) *** (loc y)) 
          THEN (SKIP) 
        ELSE (x ::= (loc y)) 
        ENDIF}}.
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
                ENDIF)
        ELSE (x ::= (const 30)) 
        ENDIF}}
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
	    DO (x ::= ((loc x) +++ (const 4)))
	  ENDWHILE}}
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

 Lemma IMP_ex16: forall (x: Loc),
       {{x ::= (const 50) ;;
         IFB ((loc x) << (const 70) &&& (loc x) >> (const 40))
           THEN (x ::= (const 10))
         ELSE (SKIP)
         ENDIF}}
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
    apply one_weak_to_strong. auto. apply is_comp. auto.
    apply is_pair. repeat apply is_pure_ro; apply is_ttrue.
    repeat apply is_pure_ro; apply is_ttrue.
    repeat apply is_pure_ro; apply is_ttrue. apply weak_proj_pi1_rorw. 
    repeat apply is_pure_ro; apply is_ttrue.
    apply strong_proj_pi2_rorw. repeat apply is_pure_ro; apply is_ttrue.
    transitivity((update x o constant 10) o (update x o constant 50)).
    apply strong_subs. apply strong_coproj_copi1_rwrw.
   
    specialize(@IMP_ex3 x 50 10). unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. intros. apply H.    
 Qed.

 Lemma IMP_ex17: forall (x: Loc), forall (p: Z),
         {{ IFB ((const p) << (const 0))
           THEN (x ::= (const 100))
         ELSE (x ::= (const p))
         ENDIF}}
         ==
         {{ IFB ((const p) >>= (const 0))
           THEN (x ::= (const p))
         ELSE (x ::= (const 100))
         ENDIF}}.
 Proof.
    intros. unfold defCommand. unfold defBoolExp. 
    unfold defArithExp. induction p.
    transitivity(copair (update x o constant 100) (update x o constant 0) o ffalse).
    apply strong_repl. apply IMP_IntLtF. simpl. auto.
    transitivity(update x o constant 0).
    apply strong_coproj_copi2_rwrw. apply strong_sym.
    transitivity(copair (update x o constant 0) (update x o constant 100) o ttrue).
    apply strong_repl. apply IMP_IntGeT. simpl. auto.
    transitivity(update x o constant 0).
    apply strong_coproj_copi1_rwrw. apply strong_refl.
    transitivity(copair (update x o constant 100) (update x o constant (Zpos p)) o ffalse).
    apply strong_repl. apply IMP_IntLtF. simpl. auto.
    transitivity(update x o constant (Zpos p)). apply strong_coproj_copi2_rwrw.
    apply strong_sym.
    transitivity(copair (update x o constant (Zpos p)) (update x o constant 100) o ttrue).
    apply strong_repl. apply IMP_IntGeT. simpl. auto.
    transitivity(update x o constant (Zpos p)). apply strong_coproj_copi1_rwrw.
    apply strong_refl.
    transitivity(copair (update x o constant 100) (update x o constant (Zneg p)) o ttrue).
    apply strong_repl. apply IMP_IntLtT. simpl. auto.
    transitivity(update x o constant 100). apply strong_coproj_copi1_rwrw.
    apply strong_sym.
    transitivity(copair (update x o constant (Zneg p)) (update x o constant 100) o ffalse).
    apply strong_repl. apply IMP_IntGeF. simpl. auto.
    transitivity(update x o constant 100). apply strong_coproj_copi2_rwrw.
    apply strong_refl.
 Qed.

End Make.
