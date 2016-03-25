(**************************************************************************)
(*  This is part of STATES, it is distributed under the terms of the      *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2014: Jean-Guillaume Dumas, Dominique Duval            *)
(*			 Burak Ekici, Damien Pous.                        *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory Terms Decorations Axioms Derived_Terms Derived_Pairs
        Derived_Products Derived_Rules.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.


Module Make(Import M: Memory.T).
  Module Export ProofsExp := Derived_Rules.Make(M). 

(* --- Main Proofs --- *)

 Theorem annihilation_update_lookup: forall i: Loc, 
         update i o lookup i == id.
         (* Prop: 2.1: All Cases *)
 Proof.
     intro. remember observation. apply observation. intro k.
     destruct (Loc_dec i k). rewrite <- e.
     (*Case k = i*)
     rewrite assoc. setoid_rewrite -> id_src. setoid_rewrite <- id_tgt at 6.
     apply wsc. apply axiom_1. apply strong_refl.
     (*Case k <> i*)
     rewrite assoc. remember wsc. rewrite axiom_2; try decorate.
     apply strong_to_weak. rewrite <- assoc. apply sc. apply strong_refl.
     apply E_1_4; decorate.
 Qed.

 Theorem interaction_lookup_lookup: forall i,
         lookup i o forget o lookup i == lookup i.
         (* Prop: 2.2: All Cases: Simplified Version *)
 Proof.
     intros. setoid_rewrite <- id_src at 6. rewrite <- assoc. apply sc.
     apply strong_refl. apply E_1_4; decorate.
 Qed.

 Theorem interaction_update_lookup: forall i: Loc,
         lookup i o update i ~~ id. (* Prop: 2.4: All Cases *)
 Proof. intros. apply axiom_1. Qed.

 Theorem commutation_lookup_lookup: forall i j: Loc, i<>j ->
         (prod id (lookup j)) o (inv_pi1 o lookup i)
         == 
         permut o ((prod id (lookup i)) o (inv_pi1 o lookup j)). 
         (* Prop: 2.5: All Cases *)
 Proof.
    intros. remember strong_unicity.
    specialize (@strong_unicity _ _ _
    (prod id (lookup j) o (inv_pi1 o lookup i)) 
    ((permut) o ((prod id (lookup i)) o (inv_pi1 o lookup j)))).
    intros. apply H0.
    (*Case pi1*)
    setoid_rewrite assoc at 1. remember wsc.
    rewrite strong_proj_pi1_purero_rect; try decorate. rewrite id_tgt.
    rewrite assoc. unfold inv_pi1. rewrite strong_proj_pi1_purero; try decorate.
    rewrite id_tgt. apply weak_sym.
    (*Step 2*)
    rewrite assoc. apply strong_to_weak. remember sc.
    rewrite strong_pi1_permut__pi2. rewrite assoc. 
    rewrite strong_proj_pi2_purero_rect; try decorate. rewrite assoc.
    setoid_rewrite <- assoc at 2. rewrite strong_proj_pi2_purero; try decorate.
    rewrite <- assoc. rewrite E_1_4; try decorate. rewrite id_src. apply strong_refl.
    (*Case pi2*)
    rewrite assoc. remember sc. rewrite strong_proj_pi2_purero_rect; try decorate.
    rewrite assoc. setoid_rewrite <- assoc at 2. rewrite strong_pi2_inv_pi1__unit.
    rewrite <- assoc. rewrite E_1_4; try decorate. rewrite id_src. apply strong_sym.
    (*Step 2*)
    rewrite assoc. rewrite strong_pi2_permut__pi1. rewrite assoc.
    rewrite strong_proj_pi1_purero_rect; try decorate. rewrite id_tgt.
    rewrite assoc. unfold inv_pi1. rewrite strong_proj_pi1_purero; try decorate.
    rewrite id_tgt. apply strong_refl.
 Qed.

 Theorem commutation_lookup_constant: forall i: Loc, forall c: Z, 
         (lookup i o (update i o (constant c)))
         == 
         (constant c) o update i o (constant c).
         (*Prop 2.8: All Cases*)
 Proof.
     intros. remember comp_final_unique. specialize (@comp_final_unique _ _
     (lookup i o (update i o (constant c))) 
     ((constant c) o (update i o (constant c)))).
     intros. setoid_rewrite <- assoc at 1. apply H.
     (* Case 1: <> o f == <> o g *)
     rewrite assoc. specialize (@E_1_4 _ (lookup i)). intros. remember sc. 
     rewrite H0; try decorate. rewrite id_tgt. apply strong_sym. rewrite assoc.
     specialize (@E_0_4 _ (constant c)).  intros. rewrite H1; try decorate. 
     rewrite id_tgt. apply strong_refl. 
     (* Case 2: f ~ g *)
     rewrite assoc. remember wsc. rewrite axiom_1. rewrite id_tgt.
     rewrite <- id_src at 1. apply wrc; try decorate. apply weak_final_unique.
 Qed.

 Lemma commutation_lookup_constant_update: forall (m: Loc) (p q: Z),
      (pair (lookup m) (constant q)) o (update m o constant p)
      ==
      (pair (constant p) (constant q)) o (update m o constant p).
 Proof.
      intros. apply strong_unicity. repeat rewrite assoc. remember wrc. 
      rewrite weak_proj_pi1_rorw;  try decorate. rewrite axiom_1.
      rewrite id_tgt. apply weak_sym.
      repeat rewrite assoc. rewrite weak_proj_pi1_rorw;  try decorate.
      setoid_rewrite <- id_src at 6. rewrite <- assoc.
      apply wrc; (solve[decorate] || idtac). apply weak_final_unique.
      repeat rewrite assoc. remember sc. 
      rewrite strong_proj_pi2_rorw;  try decorate. apply strong_sym.
      rewrite strong_proj_pi2_rorw;  try decorate. apply strong_refl.     
 Qed.

 Lemma commutation_constant_lookup_update: forall (m: Loc) (p q: Z),
      (pair (constant q) (lookup m)) o (update m o constant p)
      ==
      (pair (constant q) (constant p)) o (update m o constant p).
 Proof.
      intros. apply strong_unicity. repeat rewrite assoc. remember wrc.
      rewrite weak_proj_pi1_rorw;  try decorate. apply weak_sym.
      rewrite weak_proj_pi1_rorw;  try decorate. apply weak_refl.
      repeat rewrite assoc. remember sc.
      rewrite strong_proj_pi2_rorw;  try decorate.  
      specialize(@commutation_lookup_constant m p). intros.
      rewrite <- assoc. rewrite H. apply strong_sym.
      rewrite strong_proj_pi2_rorw;  try decorate. apply strong_refl.
 Qed. 

Lemma commutation_update_update: forall {x y: Loc}, forall (n m: Z), x<>y -> 
	(update y o constant m) o (update x o constant n) == 
        (update x o constant n) o (update y o constant m).
 Proof.
    intros. apply observation. intros.
    (* i = y *)
    destruct (Loc_dec i y). rewrite e. repeat rewrite assoc. rewrite axiom_1. 
    intros. apply weak_sym. rewrite  axiom_2; try decorate. specialize(@E_0_4 _ (constant n)). 
    intros. setoid_rewrite <- assoc at 3. rewrite H0; try decorate.
    setoid_rewrite id_src. rewrite axiom_1. rewrite id_tgt. apply weak_sym.
    specialize(@weak_final_unique _ (update x o (constant n)) (@id unit)).
    intros. rewrite <- assoc. rewrite H1. rewrite id_src. apply weak_refl.
    (* i = x *)
    destruct (Loc_dec i x). rewrite e. repeat rewrite assoc. rewrite  axiom_2.
    specialize(@E_0_4 _ (constant m)). intros. setoid_rewrite <- assoc at 3.
    rewrite H0; try decorate. setoid_rewrite id_src. rewrite axiom_1. rewrite id_tgt.
    setoid_rewrite <- id_src at 1. rewrite <- assoc. apply wrc; try decorate.
    apply weak_final_unique. auto.
    (* i <> x and i <> y *)
    repeat rewrite assoc. rewrite axiom_2; (auto || idtac). specialize(@E_0_4 _ (constant m)).
    intros. setoid_rewrite <- assoc at 3. rewrite H0; (solve[decorate] || idtac).
    rewrite id_src. rewrite axiom_2; (auto || idtac). rewrite <- assoc. apply weak_sym.
    remember E_0_4. specialize(@E_0_4 _ (constant n)). intros.
    remember wsc. rewrite H1 at 1; try decorate. rewrite id_src. rewrite assoc. 
    rewrite axiom_2; auto. repeat rewrite <- assoc. apply strong_to_weak. apply sc.
    apply strong_refl. apply one_weak_to_strong; try decorate. apply weak_final_unique.
 Qed.

(* -------------------- End of Main Proofs -------------------- *)

End Make.
