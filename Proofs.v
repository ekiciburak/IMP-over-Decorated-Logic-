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
Derived_Products Derived_Rules.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.

Module Make(Import M: Memory.T).
  Module Export ProofsExp := Derived_Rules.Make(M).

 Axiom unify: forall (i: Loc) (Y Y': Set), Y = Y'.  

(* --- Main Proofs --- *)

 Theorem annihilation_update_lookup: forall i: Loc,
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

 Theorem interaction_lookup_lookup_lver: forall i: Loc,
 lookup i o forget o lookup i == lookup i. (* Prop: 2.2: All Cases: Long Version *)
 Proof.
    intros.   
    remember obs_local_global_2.
    specialize(@obs_local_global_2 _ _ 
    (lookup i o forget o lookup i) (lookup i)).
    intros. apply H. intro k. intros.
    destruct (Loc_dec k i). rewrite e.
    (*Case k = i*)    
    transitivity (lookup i o forget o lookup i).
    apply strong_to_weak. apply strong_repl.
    rewrite <- assoc. setoid_rewrite <- id_src at 6.
    apply strong_repl. apply E_1_4. apply is_lookup.
    transitivity (lookup i). apply strong_to_weak.
    setoid_rewrite <- id_src at 6. rewrite <- assoc.
    apply strong_repl. apply E_1_4. apply is_lookup.
    apply strong_to_weak. setoid_rewrite <- id_src at 1.
    rewrite <- assoc. apply strong_repl. apply strong_sym. 
    apply E_1_4. apply is_lookup.
    (*Case k <> i*)
    transitivity (lookup k o forget o lookup i).
    apply strong_to_weak. apply strong_repl.
    rewrite <- assoc. setoid_rewrite <- id_src at 6.
    apply strong_repl. apply E_1_4. apply is_lookup.
    transitivity (lookup k). apply strong_to_weak.
    setoid_rewrite <- id_src at 6. rewrite <- assoc.
    apply strong_repl. apply E_1_4. apply is_lookup.
    apply strong_to_weak. setoid_rewrite <- id_src at 1.
    rewrite <- assoc. apply strong_repl. apply strong_sym. 
    apply E_1_4. apply is_lookup.
    (*Case f ~~ g*)
    transitivity (lookup i). apply strong_to_weak.
    rewrite <- assoc. setoid_rewrite <- id_src at 6.    
    apply strong_repl. apply E_1_4. apply is_lookup.
    apply strong_to_weak. apply strong_refl.
 Qed.

 Theorem interaction_lookup_lookup: forall i,
 lookup i o forget o lookup i == lookup i. (* Prop: 2.2: All Cases: Simplified Version *)
 Proof.
     intros. setoid_rewrite <- id_src at 6.
     rewrite <- assoc. apply strong_repl.
     apply E_1_4. apply is_lookup.
 Qed.

 Theorem interaction_update_update: forall i: Loc,
 update i o pi2 o (perm_prod (update i) (@id Z)) (* Prop: 2.3: All Cases *)
 == 
 update i o (@pi2 Z Z).
 Proof.
    intros. remember observation.
    apply observation.
    intro k. intros.
    destruct (Loc_dec i k). rewrite <- e. 
    (*Case k = i*) 
    (*Step 1*)    
    transitivity (pi2 o (perm_prod (update i) (@id Z))).
    rewrite -> assoc.  apply weak_subs. rewrite -> assoc. 
    setoid_rewrite <- id_tgt at 6. 
    apply weak_subs. apply axiom_1.
    (*Step 2*)
    transitivity (@pi2 Z Z).
    setoid_rewrite <- id_tgt at 6.
    apply weak_perm_proj_pi2_rwpure_rect. apply is_id. 
    (*Step 3*)
    apply weak_sym.  setoid_rewrite <- id_tgt at 6.
    rewrite assoc. apply weak_subs. apply axiom_1.
    (*Case k <> i*) 
    (*Step 1*)
    transitivity (lookup k o forget o pi2 o (perm_prod (update i) (@id Z))).
    rewrite -> assoc. apply weak_subs. rewrite -> assoc.
    apply weak_subs. apply axiom_2. assumption.
    (*Step 2*)
    transitivity (lookup k o pi1 o (perm_prod (update i) (@id Z))).
    apply strong_to_weak. rewrite <- assoc.
    rewrite <- assoc. rewrite <- assoc.
    apply strong_repl. rewrite -> assoc.
    apply strong_subs. remember E_0_3.
    specialize(@E_0_3 _ _ forget pi1 (@pi2 unit Z)).
    intros. apply strong_sym. apply H. apply is_forget. 
    apply is_pi1. apply is_pi2. 
    (*Step 3*)
    transitivity (lookup k o update i o (@pi1 Z Z)).
    rewrite <- assoc. apply strong_to_weak.
    rewrite <- assoc. apply strong_repl.
    apply strong_perm_proj_pi1_rwpure_rect. apply is_id.
    (*Step 4*)
    transitivity (lookup k o forget o (@pi1 Z Z)).
    apply weak_subs. apply axiom_2.
    assumption.
    (*Step 5*)
    transitivity (lookup k o (@prod_forget Z Z)).
    rewrite <- assoc. apply strong_to_weak.
    apply strong_repl. apply strong_unit_pi1__prod_forget.
    (*Step 6*)
    apply weak_sym.
    transitivity (lookup k o forget o (@pi2 Z Z)).
    rewrite assoc. apply weak_subs. 
    apply axiom_2. assumption.
    (*Step 7*)
    rewrite <- assoc. apply strong_to_weak. apply strong_repl.
    apply strong_unit_pi2__prod_forget.
 Qed.

 Theorem interaction_update_lookup: forall i: Loc,
 lookup i o update i ~~ id. (* Prop: 2.4: All Cases *)
 Proof.
     intros. apply axiom_1.
 Qed.

 Theorem commutation_lookup_lookup: forall i j: Loc, 
 i<>j -> (prod id (lookup j)) o inv_pi1 o lookup i
 == permut o (prod (id) (lookup i)) o inv_pi1 o lookup j. (* Prop: 2.5: All Cases *)
 Proof.
    intros. remember strong_unicity.
    specialize (@strong_unicity _ _ _
    ((prod id (lookup j)) o inv_pi1 o lookup i) 
    (permut o (prod id (lookup i)) o inv_pi1 o lookup j)).
    intros. apply H0.
    (*Case pi1*)
    apply weak_sym.
    (*Step 1*)
    transitivity (pi2 o (prod id (lookup i)) o inv_pi1 o lookup j).
    apply strong_to_weak. rewrite assoc. apply strong_subs. 
    rewrite assoc. apply strong_subs.
    rewrite assoc. apply strong_subs.
    apply strong_pi1_permut__pi2. 
    (*Step 2*)
    transitivity (lookup i o pi2 o inv_pi1 o lookup j).
    apply strong_to_weak. apply strong_subs. apply strong_subs.
    apply strong_proj_pi2_purero_rect. apply is_id. apply is_lookup. 
    (*Step 3*)
    transitivity (lookup i o forget o lookup j).
    apply strong_to_weak. apply strong_subs.
    rewrite <- assoc. apply strong_repl.
    apply strong_pi2_inv_pi1__unit.
    (*Step 4*)
    transitivity (lookup i).
    apply strong_to_weak. setoid_rewrite <- id_src at 6.
    rewrite <- assoc. apply strong_repl.
    apply E_1_4. apply is_lookup.
    (*Step 5*)
    apply weak_sym.
    transitivity (pi1 o inv_pi1 o lookup i).
    rewrite assoc.
    apply weak_subs. rewrite assoc. apply weak_subs.
    setoid_rewrite <- id_tgt at 6. apply strong_to_weak.
    apply strong_proj_pi1_purero_rect. apply is_id. apply is_lookup.  
    (*Step 6*)
    apply strong_to_weak. setoid_rewrite <- id_tgt at 6.
    apply strong_subs. apply strong_pi1_inv_pi1__id.
    (*Case pi2*)
    apply strong_sym.
    (*Step 1*)
    transitivity (pi1 o (prod (id) (lookup i)) o inv_pi1 o lookup j).
    rewrite assoc.
    apply strong_subs. rewrite assoc. apply strong_subs. 
    rewrite assoc. apply strong_subs. 
    apply strong_pi2_permut__pi1.
    (*Step 2*)
    transitivity (pi1 o inv_pi1 o lookup j).
    apply strong_subs. apply strong_subs. 
    setoid_rewrite <- id_tgt at 6. 
    apply strong_proj_pi1_purero_rect.
    apply is_id. apply is_lookup.
    (*Step 3*) 
    transitivity (lookup j).
    setoid_rewrite <- id_tgt at 6.
    apply strong_subs. apply strong_pi1_inv_pi1__id.
    apply strong_sym.
    (*Step 4*) 
    transitivity (lookup j o pi2 o inv_pi1 o lookup i).
    rewrite assoc. apply strong_subs. 
    rewrite assoc. apply strong_subs. 
    apply strong_proj_pi2_purero_rect.
    apply is_id. apply is_lookup.
    (*Step 5*) 
    transitivity (lookup j o forget o lookup i). 
    apply strong_subs. setoid_rewrite <- assoc at 1.
    apply strong_repl. apply strong_pi2_inv_pi1__unit.
    (*Step 6*)
    setoid_rewrite <- id_src at 6.
    setoid_rewrite <- assoc at 1. apply strong_repl.
    apply E_1_4. apply is_lookup. 
 Qed.

 (*Theorem commutation_update_update: forall i j: Loc, i<>j ->
   update bool j o (@constant bool true) o update nat i o (@constant nat 50) 
   == update nat i o (@constant nat 50) o update bool j o (@constant bool true).

  or 

  Theorem commutation_update_update: forall i j: Loc, forall Y Z: Set, forall c: Y, forall n: Z,
   i<>j ->
   update Z j o (@constant Z n) o update i o (@constant Y c) 
                               == 
   update i o (@constant Y c) o update Z j o (@constant Z n).

                               ==

 Theorem commutation_update_update: forall i j: Loc, i<>j ->
   update bool j o pi2 o (perm_prod (update nat i) (@id bool)) 
   == update nat i o pi1 o (prod (@id nat) (update bool j)).*)

 Theorem commutation_update_update: forall i j: Loc, i<>j ->
   update j o pi2 o (perm_prod (update i) (@id Z)) 
   == update i o pi1 o (prod (@id Z) (update j)). (*Prop 2.6: All Cases.*)
 Proof.
     intros. apply observation. intro k. 
     intros. destruct (Loc_dec k i) as [->|Dki].
       (* case i=k<>j *)
       (*Step 1*)
       transitivity (lookup i o forget o pi2 o (perm_prod (update i) (@id Z))).
       setoid_rewrite -> assoc at 1. apply weak_subs. setoid_rewrite -> assoc at 1.
       apply weak_subs. apply axiom_2. auto.
       (*Step 2*)
       transitivity (lookup i o pi1 o (perm_prod (update i) (@id Z))).
       apply strong_to_weak. apply strong_subs. setoid_rewrite <- assoc at 1.
       apply strong_repl. remember E_0_3. 
       specialize(@E_0_3 _ _ forget pi1 (@pi2 unit Z)).
       intros. apply strong_sym. apply H0. apply is_forget. 
       apply is_pi1. apply is_pi2.
       (*Step 3*)
       transitivity (lookup i o update i o (@pi1 Z Z)).
       apply strong_to_weak. setoid_rewrite <- assoc at 1. setoid_rewrite <- assoc at 1.
       apply strong_repl. apply strong_perm_proj_pi1_rwpure_rect. apply is_id. 
       (*Step 4*)
       transitivity (id o (@pi1 Z Z)).
       apply weak_subs.
       apply axiom_1. setoid_rewrite -> id_tgt.  
       (*Step 5*)
       apply weak_sym. 
       transitivity (pi1 o (prod (@id Z) (update j))).
       setoid_rewrite -> assoc at 1.
       apply weak_subs. setoid_rewrite <- id_tgt at 6.
       setoid_rewrite -> assoc at 1. apply weak_subs. apply axiom_1.
       (*Step 6*)
       setoid_rewrite <- id_tgt at 6.
       apply weak_proj_pi1_purerw_rect. apply is_id. 
       destruct (Loc_dec k j) as [->|Dkj].
       (* case i<>j=k *)
       apply weak_sym.
       (*Step 1*)
       transitivity (lookup j o forget o pi1 o (prod (@id Z) (update j))).
       setoid_rewrite -> assoc at 1. apply weak_subs. setoid_rewrite -> assoc at 1.
       apply weak_subs. apply axiom_2. congruence.
       (*Step 2*)
       transitivity (lookup j o pi2 o (prod (@id Z) (update j))).
       apply strong_to_weak. apply strong_subs. setoid_rewrite <- assoc at 1.
       apply strong_repl.
       specialize(@E_0_3 _ _ forget pi2 (@pi1 Z unit)).
       intros. apply strong_sym. apply H0. apply is_forget. 
       apply is_pi2. apply is_pi1.
       (*Step 3*)
       transitivity (lookup j o update j o (@pi2 Z Z)).
       apply strong_to_weak. setoid_rewrite <- assoc at 1.
       setoid_rewrite <- assoc at 1. apply strong_repl.
       apply strong_proj_pi2_purerw_rect. apply is_id.
       (*Step 4*)
       transitivity (id o (@pi2 Z Z)).
       apply weak_subs. apply axiom_1. setoid_rewrite -> id_tgt at 1. 
       (*Step 5*)
       apply weak_sym.
       transitivity (pi2 o perm_prod (update i) (@id Z)).
       setoid_rewrite -> assoc at 1. apply weak_subs. setoid_rewrite -> assoc at 1.
       setoid_rewrite <- id_tgt at 6. apply weak_subs. apply axiom_1.
       (*Step 6*)
       setoid_rewrite <- id_tgt at 6. apply weak_perm_proj_pi2_rwpure_rect. apply is_id.
      (* case i<>j<>k<>i *)
        (*Step 1*)
        transitivity (lookup k o forget o pi2 o perm_prod (update i) (@id Z)).
        setoid_rewrite -> assoc at 1. apply weak_subs. setoid_rewrite -> assoc at 1.
        apply weak_subs. apply axiom_2. congruence.
        (*Step 2*)
        transitivity (lookup k o pi1 o perm_prod (update i) (@id Z)).
        apply strong_to_weak. apply strong_subs. setoid_rewrite <- assoc at 1.
        apply strong_repl.
        specialize(@E_0_3 _ _ forget pi1 (@pi2 unit Z)).
        intros. apply strong_sym. apply H0. apply is_forget. 
        apply is_pi1. apply is_pi2.
        (*Step 3*)
        transitivity (lookup k o update i o (@pi1 Z Z)).
        apply strong_to_weak. setoid_rewrite <- assoc at 1.
        setoid_rewrite <- assoc at 1. apply strong_repl.
        apply strong_perm_proj_pi1_rwpure_rect. apply is_id.
        (*Step 4*)
        transitivity (lookup k o forget o (@pi1 Z Z)).
        apply weak_subs. apply axiom_2. congruence.
        (*Step 5*)
        transitivity (lookup k o (@prod_forget Z Z)).
        apply strong_to_weak. setoid_rewrite <- assoc at 1.
        apply strong_repl. apply strong_unit_pi1__prod_forget. 
        (*Step 6*)
        apply weak_sym.
        transitivity (lookup k o forget o pi1 o (prod (@id Z) (update j))).
        setoid_rewrite -> assoc at 1. apply weak_subs. setoid_rewrite -> assoc at 1.
        apply weak_subs. apply axiom_2. congruence.
        (*Step 7*)
        transitivity (lookup k o pi2 o (prod (@id Z) (update j))).
        apply strong_to_weak. apply strong_subs. setoid_rewrite <- assoc at 1.
        apply strong_repl.
        specialize(@E_0_3 _ _ forget pi2 (@pi1 Z unit)).
        intros. apply strong_sym. apply H0. apply is_forget. 
        apply is_pi2. apply is_pi1.
        (*Step 8*)
        transitivity (lookup k o update j o (@pi2 Z Z)).
        apply strong_to_weak. setoid_rewrite <- assoc at 1.
        setoid_rewrite <- assoc at 1. apply strong_repl. 
        apply strong_proj_pi2_purerw_rect. apply is_id.
        (*Step 9*)
        transitivity (lookup k o forget o (@pi2 Z Z)).
        apply weak_subs. apply axiom_2. congruence.
        (*Step 10*)
        apply strong_to_weak. setoid_rewrite <- assoc at 1.
        apply strong_repl. apply strong_unit_pi2__prod_forget.
  Qed. 

 Theorem commutation_update_lookup_lver: forall i j: Loc, 
 i<>j -> lookup j o update i o pi1 
 == pi2 o (perm_prod (update i) id) o (prod (@id Z) (lookup j)). (*Prop 2.7: All Cases: Long Version*)
 Proof.
     intros. remember comp_final_unique.
     specialize (@comp_final_unique _ _
     (lookup j o update i o pi1) (pi2 o (perm_prod (update i) id) o (prod id (lookup j)))).
     intros. apply H0.
     remember observation.
     specialize (@observation _
     (forget o ((lookup j o update i) o pi1)) 
     (forget o ((pi2 o perm_prod (update i) id) o prod id (lookup j)))).
     intros. apply H1. intro k. 
     destruct (Loc_dec k i). intros. rewrite e. 
     (*Case k = i /\ k <> j*)
     apply weak_sym. 
     transitivity (lookup i o pi1 o (perm_prod (update i) id) o (prod (@id Z) (lookup j))).
     apply strong_to_weak. rewrite assoc. setoid_rewrite assoc at 1.
     apply strong_subs.
     rewrite assoc. apply strong_subs. rewrite <- assoc.
     apply strong_repl.
     specialize(@E_0_3 _ _ forget pi1 (@pi2 unit Z)).
     intros. apply strong_sym. apply H2. apply is_forget. 
     apply is_pi1. apply is_pi2.
     transitivity (lookup i o update i o pi1 o (prod (@id Z) (lookup j))).
     apply strong_to_weak. apply strong_subs. rewrite <- assoc.
     rewrite <- assoc. apply strong_repl.
     apply strong_perm_proj_pi1_rwpure_rect. apply is_id. 
     transitivity (lookup i o update i o (@pi1 Z unit)).
     apply strong_to_weak. rewrite <- assoc. apply strong_repl.
     apply one_weak_to_strong. apply is_comp. apply is_pure_ro. apply is_pi1.
     apply is_prod. apply is_pure_ro. apply is_id. apply is_lookup. 
     apply is_pure_ro. apply is_pi1.
     setoid_rewrite <- id_tgt at 6. apply weak_proj_pi1_purerw_rect.
     apply is_id.
     transitivity ((@pi1 Z unit)). setoid_rewrite <- id_tgt at 6.
     apply weak_subs. apply axiom_1.
     apply weak_sym. 
     transitivity (lookup i o update i o (@pi1 Z unit)).
     apply strong_to_weak. rewrite assoc. setoid_rewrite assoc at 1.
     apply strong_subs.
     rewrite <- assoc. apply strong_repl.
     setoid_rewrite <- id_tgt at 6. rewrite assoc.
     apply strong_subs. apply E_1_4. apply is_lookup.
     setoid_rewrite <- id_tgt at 6. apply weak_subs.
     apply axiom_1.
     destruct (Loc_dec k j). intros. rewrite e. 
     (*Case k = j /\ k <> i*)
     apply weak_sym. 
     transitivity (lookup j o pi1 o (perm_prod (update i) id) o (prod (@id Z) (lookup j))).
     apply strong_to_weak. rewrite assoc. setoid_rewrite assoc at 1.
     apply strong_subs.
     rewrite assoc. apply strong_subs. rewrite <- assoc.
     apply strong_repl. 
     specialize(@E_0_3 _ _ forget pi1 (@pi2 unit Z)).
     intros. apply strong_sym. apply H2. apply is_forget. 
     apply is_pi1. apply is_pi2.
     transitivity (lookup j o update i o pi1 o (prod (@id Z) (lookup j))).
     apply strong_to_weak. apply strong_subs. rewrite <- assoc.
     rewrite <- assoc. apply strong_repl. 
     apply strong_perm_proj_pi1_rwpure_rect. apply is_id.
     transitivity (lookup j o update i o (@pi1 Z unit)).
     apply strong_to_weak. rewrite <- assoc. apply strong_repl.
     apply one_weak_to_strong. apply is_comp. apply is_pure_ro. apply is_pi1.
     apply is_prod. apply is_pure_ro. apply is_id. apply is_lookup. 
     apply is_pure_ro. apply is_pi1.
     setoid_rewrite <- id_tgt at 6. apply weak_proj_pi1_purerw_rect.
     apply is_id.
     apply weak_sym. 
     transitivity (lookup j o update i o (@pi1 Z unit)).
     apply strong_to_weak. rewrite assoc. setoid_rewrite assoc at 1. 
     apply strong_subs.
     rewrite <- assoc. apply strong_repl.
     setoid_rewrite <- id_tgt at 6. rewrite assoc.
     apply strong_subs. apply E_1_4. apply is_lookup. 
     apply strong_to_weak. apply strong_refl.
     (*Case k <> i /\ k <> j /\ i <> j*)
     intros. apply weak_sym. 
     transitivity (lookup k o pi1 o (perm_prod (update i) id) o (prod (@id Z) (lookup j))).
     apply strong_to_weak. rewrite assoc. setoid_rewrite assoc at 1.
     apply strong_subs.
     rewrite assoc. apply strong_subs. rewrite <- assoc.
     apply strong_repl. 
     specialize(@E_0_3 _ _ forget pi1 (@pi2 unit Z)).
     intros. apply strong_sym. apply H2. apply is_forget. 
     apply is_pi1. apply is_pi2.
     transitivity (lookup k o update i o pi1 o (prod (@id Z) (lookup j))).
     apply strong_to_weak. apply strong_subs. rewrite <- assoc.
     rewrite <- assoc. apply strong_repl.
     apply strong_perm_proj_pi1_rwpure_rect. apply is_id.
     transitivity (lookup k o forget o pi1 o (prod (@id Z) (lookup j))).
     apply weak_subs. apply weak_subs. apply axiom_2. congruence.
     transitivity (lookup k o prod_forget o (prod (@id Z) (lookup j))).
     apply strong_to_weak. apply strong_subs. rewrite <- assoc.
     apply strong_repl. apply strong_unit_pi1__prod_forget.
     transitivity (lookup k o forget o (@pi1 Z unit)).
     apply strong_to_weak. rewrite <- assoc. rewrite <- assoc.
     apply strong_repl. 
     apply one_weak_to_strong. apply is_comp. 
     apply is_pure_ro. apply is_prod_forget.
     apply is_prod. apply is_pure_ro. apply is_id. apply is_lookup. apply is_comp.
     apply is_pure_ro. apply is_forget. apply is_pure_ro. apply is_pi1.
     transitivity (forget o pi1 o (prod (@id Z) (lookup j))).
     apply strong_to_weak. apply strong_subs.
     apply strong_sym. apply strong_unit_pi1__prod_forget.
     rewrite <- assoc. apply zero_weak_repl. apply is_forget.
     setoid_rewrite <- id_tgt at 6. apply weak_proj_pi1_purerw_rect. apply is_id.
     apply weak_sym.
     transitivity (lookup k o update i o (@pi1 Z unit)).
     apply strong_to_weak. rewrite assoc. setoid_rewrite assoc at 1.
     apply strong_subs. rewrite assoc. apply strong_subs.
     setoid_rewrite <- id_src at 6. rewrite <- assoc.
     apply strong_repl. apply E_1_4. apply is_lookup.
     transitivity (lookup k o forget o (@pi1 Z unit)).
     apply weak_subs. apply axiom_2. congruence.
     apply strong_to_weak. apply strong_refl.
     (*Case: f ~~ g*)
     transitivity (lookup j o forget o (@pi1 Z unit)).
     apply weak_subs. apply axiom_2. assumption.
     transitivity (lookup j o (@pi2 Z unit)).
     apply strong_to_weak. rewrite <- assoc. apply strong_repl.
     specialize(@E_0_3 _ _ forget pi2 (@pi1 Z unit)).
     intros. apply strong_sym. apply H1. apply is_forget. 
     apply is_pi2. apply is_pi1.
     apply weak_sym.
     transitivity (pi2 o (prod (@id Z) (lookup j))).
     apply weak_subs. setoid_rewrite <- id_tgt at 6.
     apply weak_perm_proj_pi2_rwpure_rect. apply is_id. 
     transitivity (lookup j o (@pi2 Z unit)).
     apply strong_to_weak. apply strong_proj_pi2_purerw_rect. apply is_id.
     apply strong_to_weak. apply strong_refl.     
 Qed. 

  Theorem commutation_update_lookup: forall i j: Loc, i<>j -> lookup j o update i 
 == pi2 o (perm_prod (update i) id) o (prod (@id Z) (lookup j)) o inv_pi1. (*Prop 2.7: All Cases: Simplified Version*)
 Proof.
     intros. remember comp_final_unique.
     specialize (@comp_final_unique _ _
     (lookup j o update i) (pi2 o (perm_prod (update i) id) o (prod id (lookup j)) o inv_pi1)).
     intros. apply H0.
     (* Case 1: <> o f == <> o g *)
     apply strong_sym.
     (*Step 1*)
     transitivity (pi1 o (perm_prod (update i) id) o (prod id (lookup j)) o (@inv_pi1 Z)).
     setoid_rewrite -> assoc at 1. apply strong_subs.
     setoid_rewrite -> assoc at 1. apply strong_subs.
     setoid_rewrite -> assoc at 1. apply strong_subs. (**)
     specialize(@E_0_3 _ _ forget pi1 (@pi2 unit Z)).
     intros. apply strong_sym. apply H1. apply is_forget. 
     apply is_pi1. apply is_pi2.
     (*Step 2*)
     transitivity (update i o pi1 o (prod id (lookup j)) o (@inv_pi1 Z)).
     apply strong_subs. apply strong_subs. (**)
     apply strong_perm_proj_pi1_rwpure_rect. apply is_id. 
     (*Step 3*)
     transitivity (update i o pi1 o (@inv_pi1 Z)).
     setoid_rewrite <- assoc at 1. setoid_rewrite <- assoc at 1.
     setoid_rewrite <- assoc at 1. apply strong_repl. 
     setoid_rewrite -> assoc at 1. apply strong_subs. (**)
     setoid_rewrite <- id_tgt at 6.
     apply one_weak_to_strong. apply is_comp. apply is_pure_ro. apply is_pi1. 
     apply is_prod. apply is_pure_ro. apply is_id. apply is_lookup. 
     apply is_comp. apply is_pure_ro. apply is_id. apply is_pure_ro. apply is_pi1.
     apply weak_proj_pi1_purerw_rect. apply is_id. 
     (*Step 4*)
     transitivity (update i o (@id Z)). (**)
     setoid_rewrite <- assoc at 1. (**)
     apply strong_repl. (**)
     unfold inv_pi1. apply strong_proj_pi1_purepure.
     apply is_id. apply is_forget.
     (*Step 5*)
     apply strong_sym.
     setoid_rewrite -> id_src at 1. (**)
     setoid_rewrite -> assoc at 1.
     setoid_rewrite <- id_tgt at 6. apply strong_subs. 
     apply E_1_4. apply is_lookup. 
     (* Case 2: f ~~ g *)
     (*Step 1*)
     transitivity (lookup j o (@forget Z)). (**)
     apply axiom_2. assumption.
     (*Step 2*)
     transitivity (lookup j o pi2 o (@inv_pi1 Z)).
     apply strong_to_weak. rewrite <- assoc. 
     apply strong_repl. apply strong_sym. 
     unfold inv_pi1.
     apply strong_proj_pi2_purepure. (**)
     apply is_id. apply is_forget.
     (*Step 3*)
     apply weak_sym.
     transitivity (pi2 o (prod id (lookup j)) o (@inv_pi1 Z)).
     apply weak_subs. apply weak_subs. (**) setoid_rewrite <- id_tgt at 6.
     apply weak_perm_proj_pi2_rwpure_rect. apply is_id.
     (*step 4*)
     apply strong_to_weak.
     apply strong_subs. (**)
     apply strong_proj_pi2_purerw_rect. apply is_id.      
 Qed.

 Theorem commutation_lookup_constant: forall i: Loc, forall c: Z, 
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

 Theorem commutation_update_x_update_y: forall {x y: Loc}, forall (n m: Z), x<>y -> 
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

(* Lemma conditionals: forall (b: bool) (X Y: Type) (f: term Y X), IF_THEN_ELSE b f f == f.
 Proof.
     intros. destruct b. simpl.
     apply strong_refl.
     simpl. apply strong_refl.
 Qed.

 Lemma conditionals_embed_coq: forall (b: bool) (X Y: Type) (f: term Y X), (if b then f else f) == f.
 Proof.
     intros. destruct b. 
     apply strong_refl.
     apply strong_refl.
 Qed.*)
 

(* -------------------- End of Main Proofs -------------------- *)

End Make.
