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
Require Memory Terms Decorations Derived_Terms Axioms.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.

Module Make(Import M: Memory.T).
  Module Export Derived_RulesExp := Axioms.Make(M). 

(* --- Derived Rules --- *)

 Lemma weak_refl: forall X Y (f: term Y X), f ~~ f.
 Proof.
     intros. apply strong_to_weak. apply strong_refl.
 Qed.
 
 Lemma zero_weak_to_strong: forall X Y (f g: term Y X),
 is pure f -> is pure g -> f ~~ g  -> f == g.
 Proof.
     intros. apply one_weak_to_strong.
     apply is_pure_ro. assumption.
     apply is_pure_ro. assumption.
     assumption.
 Qed.

 Lemma weak_final_unit: forall X (f: term unit X), f ~~ forget.
 Proof.
     intros. remember weak_final_unique.
     specialize(@weak_final_unique _ f forget).
     intros. assumption.
 Qed.

Lemma E_1_1: forall X (f g: term unit X),
 is ro f -> is ro g -> f == g.
 Proof.
     intros. apply one_weak_to_strong.
     assumption. assumption. 
     remember weak_final_unique.
     apply weak_final_unique.
 Qed.

 Lemma E_0_1: forall X (f g : term unit X),
 is pure f -> is pure g -> f == g.
 Proof.
     intros. apply one_weak_to_strong.
     apply is_pure_ro. assumption.
     apply is_pure_ro. assumption.
     apply weak_final_unique.
 Qed.

 Lemma E_1_2: forall X (f: term unit X), is ro f -> f == forget.
 Proof.
     intros. apply one_weak_to_strong. assumption.
     apply is_pure_ro. apply is_forget. 
     apply weak_final_unique.
 Qed.
 
 Lemma E_0_2: forall X (f: term unit X), is pure f -> f == forget.
 Proof.
     intros. apply one_weak_to_strong. apply is_pure_ro.
     assumption. apply is_pure_ro.
     apply is_forget. apply weak_final_unique.
 Qed.

 Lemma E_1_3: forall X Y (g: term unit Y) (h: term unit X) 
 (f: term Y X),  is ro g -> is ro h -> is ro f -> h == g o f.
 Proof.
     intros. apply one_weak_to_strong. assumption.
     apply is_comp. assumption. assumption.
     specialize(@weak_final_unique _ h forget).
     specialize(@weak_final_unique _ (g o f) forget).
     intros. setoid_rewrite H3 at 1. setoid_rewrite H2 at 1.
     apply weak_refl.
 Qed.

 Lemma E_0_3: forall X Y (g: term unit Y) (h: term unit X) 
 (f: term Y X), is pure g -> is pure h -> is pure f -> h == g o f.
 Proof.
     intros. apply one_weak_to_strong. apply is_pure_ro. assumption.
     apply is_comp. apply is_pure_ro. assumption.
     apply is_pure_ro. assumption.
     specialize(@weak_final_unique _ h forget).
     specialize(@weak_final_unique _ (g o f) forget).
     intros. setoid_rewrite H3 at 1. setoid_rewrite H2 at 1.
     apply weak_refl.
 Qed.

 Lemma E_1_4: forall X (f: term X unit), is ro f -> forget o f == (@id unit).
 Proof.
     intros. apply one_weak_to_strong. apply is_comp. 
     apply is_pure_ro. apply is_forget.
     assumption. apply is_pure_ro. apply is_id.
     remember weak_final_unique.
     specialize(@weak_final_unique _ (forget o f) forget). intros.
     specialize(@weak_final_unique _ id forget). intros.
     setoid_rewrite H0 at 1. setoid_rewrite H1 at 1.
     apply weak_refl.
 Qed.

 Lemma E_0_4: forall X (f: term X unit),
 is pure f -> forget o f == (@id unit).
 Proof.
     intros. apply one_weak_to_strong. apply is_comp. 
     apply is_pure_ro. apply is_forget.
     apply is_pure_ro. assumption. apply is_pure_ro. apply is_id.
     specialize(@weak_final_unique _ (forget o f) forget).
     specialize(@weak_final_unique _ id forget).
     intros. setoid_rewrite H1 at 1.
     setoid_rewrite H0 at 1. apply weak_refl.     
 Qed.

 Lemma strong_unicity: forall X Y Y'(f g: term (Y/*/Y') X),
   (pi1 o f ~~ pi1 o g) -> (pi2 o f == pi2 o g) -> f == g.
 Proof.
     intros.
     remember comp_final_unique.
     remember unicity.
     apply comp_final_unique.
     transitivity (forget o pi2 o f).
     apply strong_subs.
     apply E_0_1. apply is_forget. 
     apply is_comp.
     apply is_forget. apply is_pi2.
     apply strong_sym.

     transitivity (forget o pi2 o g).
     apply strong_subs.
     apply E_0_1. apply is_forget.
     apply is_comp.
     apply is_forget. apply is_pi2.
     setoid_rewrite <- assoc at 1.
     setoid_rewrite <- assoc at 1.
     
     apply strong_repl.
     apply strong_sym. assumption.

     apply unicity.
     assumption.
     apply strong_to_weak.
     assumption.
 Qed.
 
 Lemma strong_unicity_rect: forall X X' Y Y'(f g: term (Y/*/Y') (X/*/X')),
   (pi1 o f ~~ pi1 o g) -> (pi2 o f == pi2 o g) -> f == g.
 Proof.
     intros. remember strong_unicity.
     specialize (@strong_unicity _ _ _ f g).
     intros. apply H1. assumption. assumption.
 Qed.

 Lemma annihilation_update_lookup: forall i: Loc,
 update i o lookup i == id. (* Prop: 2.1: All Cases *)
 Proof.
     intros. apply observation. intro k. intros.
     destruct (Loc_dec i k). rewrite <- e.
     (*Case k = i*)
     rewrite assoc.
     setoid_rewrite -> id_src. setoid_rewrite <- id_tgt at 6.
     apply weak_subs. apply axiom_1.
     (*Case k <> i*)
     rewrite assoc.
     transitivity (lookup k o forget o lookup i).
     apply weak_subs. apply axiom_2. assumption.
     apply strong_to_weak. rewrite <- assoc.
     apply strong_repl. apply E_1_4. apply is_lookup.
 Qed.

 Lemma interaction_update_lookup: forall i: Loc,
  lookup i o update i ~~ id. (* Prop: 2.4: All Cases *)
 Proof.
     intros. apply axiom_1.
 Qed.

 Lemma commutation_lookup_constant: forall i: Loc, forall c: Z, 
 lookup i o update i o (@constant Z c)
 == 
 (@constant Z c) o update i o (@constant Z c). (*Prop 2.8: All Cases*)
 Proof.
     intros. remember comp_final_unique.
     specialize (@comp_final_unique _ _
     ((lookup i o update i) o (@constant Z c)) (((@constant Z c) o update i) o (@constant Z c))).
     intros. apply H.
     (* Case 1: <> o f == <> o g *)
     (*Step 1*)
     transitivity (update i o (@constant Z c)).
     setoid_rewrite -> assoc at 1.
     apply strong_subs.
     setoid_rewrite -> assoc at 1.
     setoid_rewrite <- id_tgt at 6.
     apply strong_subs.
     remember E_1_4.
     specialize (@E_1_4 _ (lookup i)).
     intros. apply H0. apply is_lookup.
     (*Step 2*)
     apply strong_sym.
     setoid_rewrite -> assoc at 1.
     apply strong_subs.
     setoid_rewrite <- id_tgt at 6.
     setoid_rewrite -> assoc at 1.
     apply strong_subs.
     remember E_0_4.
     specialize (@E_0_4 _ (@constant Z c)).
     intros. apply H0. apply is_constant.
     (* Case 2: f ~~ g *)
     (*Step 1*)
     transitivity ((@constant Z c)).
     setoid_rewrite <- id_tgt at 6.
     apply weak_subs. apply axiom_1.
     (*Step 2*)
     apply weak_sym.
     setoid_rewrite <- id_src at 6.
     setoid_rewrite <- assoc at 1.
     apply zero_weak_repl. apply is_constant.
     remember weak_final_unique.
     specialize (@weak_final_unique _ (update i o (@constant Z c)) (id)).
     intros. apply H0.
 Qed.

 Lemma commutation_update_x_update_y: forall {x y: Loc}, forall (n m: Z), x<>y -> 
	(update y) o (@constant Z m) o (update x) o (@constant Z n) == 
        (update x) o (@constant Z n) o (update y) o (@constant Z m).
 Proof.
    intros. apply observation. intros.
    (* i = y *)
    destruct (Loc_dec i y). rewrite e.
    (*step 1*)
    transitivity(id o (@constant Z m) o (update x) o (@constant Z n)).
    rewrite assoc. apply weak_subs. rewrite assoc.
    apply weak_subs. rewrite assoc.  apply weak_subs.
    apply axiom_1.
    (*step 2*)
    transitivity ((@id Z) o (@constant Z m) o (@id (unit))).
    rewrite <-assoc. rewrite <- assoc. rewrite <- assoc.
    apply zero_weak_repl. apply is_id. apply zero_weak_repl.
    apply is_constant. apply weak_final_unique.
    apply weak_sym.
    (*step 3*)
    transitivity((lookup y) o forget o (@constant Z n) o (update y) o (@constant Z m)).
    rewrite assoc; apply weak_subs. rewrite assoc; apply weak_subs.
    rewrite assoc; apply weak_subs. apply axiom_2. assumption.
    (*step 4*)
    transitivity((lookup y) o (update y) o (@constant Z m)).
    apply weak_subs; apply weak_subs. apply strong_to_weak.
    remember E_0_3.
    setoid_rewrite <- id_src at 6. rewrite <- assoc.
    apply strong_repl. specialize(@E_0_3 _ _ forget id (@constant Z n)).
    intros. apply strong_sym. apply H0. apply is_forget.
    apply is_id. apply is_constant.
    (*step 5*)
    transitivity(id o (@constant Z m)).
    apply weak_subs. apply axiom_1.
    rewrite <- assoc. apply zero_weak_repl. auto.
    setoid_rewrite <- id_src at 1. apply weak_refl.
    (* i = x *)
    destruct (Loc_dec i x). rewrite e.
    (*step 1*)
    transitivity((lookup x) o forget o (@constant Z m) o (update x) o (@constant Z n)).
    rewrite assoc. apply weak_subs. rewrite assoc. apply weak_subs.
    rewrite assoc. apply weak_subs. apply axiom_2.  auto.
    (*step 2*)
    transitivity((lookup x) o (update x) o (@constant Z n)).
    apply weak_subs. apply weak_subs. apply strong_to_weak.
    setoid_rewrite <- id_src at 6. rewrite <- assoc.
    apply strong_repl. specialize(@E_0_3 _ _ forget id (@constant Z m)).
    intros. apply strong_sym. apply H0. apply is_forget.
    apply is_id. apply is_constant.    
    (*step 3*)
    transitivity(id o (@constant Z n)).
    apply weak_subs. apply axiom_1.
    apply weak_sym.
    (*step 4*)
    transitivity(id o (@constant Z n) o update y o (@constant Z m)).
    rewrite assoc. apply weak_subs. rewrite assoc.
    apply weak_subs. rewrite assoc.  apply weak_subs.
    apply axiom_1.
    (*step 5*)
    transitivity ((@id Z) o (@constant Z n) o (@id (unit))).
    rewrite <-assoc. rewrite <- assoc. rewrite <- assoc.
    apply zero_weak_repl. apply is_id. apply zero_weak_repl.
    apply is_constant. apply weak_final_unique.
    apply weak_sym.
    rewrite <- assoc. apply zero_weak_repl. auto.
    setoid_rewrite <- id_src at 1. apply weak_refl.
    (* i <> x and i <> y *)
    (*step 1*)
    transitivity((lookup i) o forget o (@constant Z m) o (update x) o (@constant Z n)).
    rewrite assoc. apply weak_subs. rewrite assoc. apply weak_subs.
    rewrite assoc. apply weak_subs. apply axiom_2. auto.
    (*step 2*)
    transitivity((lookup i) o (update x) o (@constant Z n)).
    apply weak_subs. apply weak_subs. apply strong_to_weak.
    setoid_rewrite <- id_src at 6. rewrite <- assoc.
    apply strong_repl. specialize(@E_0_3 _ _ forget id (@constant Z m)).
    intros. apply strong_sym. apply H0. apply is_forget.
    apply is_id. apply is_constant.
    (*step 3*)
    transitivity(lookup i o forget o (@constant Z n)).
    apply weak_subs. apply axiom_2. auto.
    (*step 4*)
    transitivity(lookup i o (@id (unit))).
    apply strong_to_weak. rewrite <- assoc. apply strong_repl.
    specialize(@E_0_3 _ _ forget id (@constant Z n)).
    intros. apply strong_sym. apply H0. apply is_forget.
    apply is_id. apply is_constant.
    apply weak_sym.
    (*step 5*)
    transitivity((lookup i) o forget o (@constant Z n) o (update y) o (@constant Z m)).
    rewrite assoc. apply weak_subs. rewrite assoc. apply weak_subs.
    rewrite assoc. apply weak_subs. apply axiom_2.  auto.
    (*step 6*)
    transitivity((lookup i) o (update y) o (@constant Z m)).
    apply weak_subs. apply weak_subs. apply strong_to_weak.
    setoid_rewrite <- id_src at 6. rewrite <- assoc.
    apply strong_repl. specialize(@E_0_3 _ _ forget id (@constant Z n)).
    intros. apply strong_sym. apply H0. apply is_forget.
    apply is_id. apply is_constant.
    (*step 7*)
    transitivity(lookup i o forget o (@constant Z m)).
    apply weak_subs. apply axiom_2. auto.
    apply strong_to_weak. rewrite <- assoc.
    apply strong_repl. specialize(@E_0_3 _ _ forget id (@constant Z m)).
    intros. apply strong_sym. apply H0. apply is_forget.
    apply is_id. apply is_constant.
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

 Lemma or_ex1: orB o (pair (le o (pair (@constant Z 80) (@constant Z 80)))
 (lt o (pair (@constant Z 180) (@constant Z 80))))
       == 
      ttrue.
 Proof.
    apply IMP_IntOrT. left.
    transitivity((le o pair (constant 80) (constant 80))).
    apply one_weak_to_strong. auto. apply is_comp. auto.
    apply is_pair. auto. auto. auto.
    apply weak_proj_pi1_rorw. auto.
    apply IMP_IntLeT. simpl. auto.
 Qed.

 Lemma or_ex2: orB o (pair (lt o (pair (@constant Z 80) (@constant Z 80)))
 (lt o (pair (@constant Z 180) (@constant Z 80))))
       == 
      ffalse.
 Proof.
    apply IMP_IntOrF. 
    transitivity((lt o pair (constant 80) (constant 80))).
    apply one_weak_to_strong. auto. apply is_comp. auto.
    apply is_pair. auto. auto. auto.
    apply weak_proj_pi1_rorw. auto. apply IMP_IntLtF. simpl. auto.
    transitivity((lt o pair (constant 180) (constant 80))).
    apply strong_proj_pi2_rorw. auto. apply IMP_IntLtF. simpl. auto.
 Qed.

 Lemma and_ex1: andB o (pair (le o (pair (@constant Z 80) (@constant Z 80)))
 (lt o (pair (@constant Z 180) (@constant Z 80))))
       == 
      ffalse.
 Proof.
    apply IMP_IntAndF. right.
    transitivity((lt o pair (constant 180) (constant 80))).
    apply strong_proj_pi2_rorw. auto. apply IMP_IntLtF. simpl. auto.
 Qed.

 Lemma and_ex2: andB o (pair (le o (pair (@constant Z 80) (@constant Z 80)))
 (gt o (pair (@constant Z 180) (@constant Z 80))))
       == 
      ttrue.
 Proof.
    apply IMP_IntAndT. 
    transitivity((le o pair (constant 80) (constant 80))).
    apply one_weak_to_strong. auto. apply is_comp. auto.
    apply is_pair. auto. auto. auto.
    apply weak_proj_pi1_rorw. auto.
    apply IMP_IntLeT. simpl. auto.
    transitivity((gt o pair (constant 180) (constant 80))).
    apply strong_proj_pi2_rorw. auto. apply IMP_IntGtT. simpl. auto.
 Qed.

(* -------------------- End of Derived Rules -------------------- *)

End Make.
