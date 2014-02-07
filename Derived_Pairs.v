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
Require Memory Terms Decorations Axioms Derived_Terms.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export Derived_PairsExp := Derived_Terms.Make(M). 

(* --- Derived Pair Existencies --- *)

 (* --- A pair of modifiers: Existence --- *) 

 Lemma dec_pair_exists_rwrw: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is rw f1 -> is rw f2 -> is rw (pair f1 f2).
 Proof.
     intros. apply is_pair. assumption. assumption.
 Qed.

 Lemma dec_perm_pair_exists_rwrw: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is rw f2 -> is rw f1 -> is rw (perm_pair f1 f2).
 Proof.
     intros. apply is_perm_pair. assumption. assumption.
 Qed.

 (* --- An accessor and a modifier: Existence --- *)

 Lemma dec_pair_exists_rorw: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is ro f1 -> is rw f2 -> is rw (pair f1 f2).
 Proof.
     intros. apply is_pair. apply is_ro_rw. 
     assumption. assumption.
 Qed.

 Lemma dec_perm_pair_exists_rwro: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is ro f2 -> is rw f1 -> is rw (perm_pair f1 f2).
 Proof.
     intros. apply is_perm_pair.  
     assumption. apply is_ro_rw. assumption.
 Qed.

 (* --- A pure function and a modifier: Existence*)

 Lemma dec_pair_exists_purerw: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is pure f1 -> is rw f2 -> is rw (pair f1 f2).
 Proof.
     intros. apply is_pair. apply is_ro_rw. apply is_pure_ro.
     assumption. assumption.
 Qed.

 Lemma dec_perm_pair_exists_rwpure: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is pure f2 -> is rw f1 -> is rw (perm_pair f1 f2).
 Proof.
     intros. apply is_perm_pair.  
     assumption. apply is_ro_rw. apply is_pure_ro. assumption.
 Qed.

 (* --- A pair of accessors: Existence --- *) 

 Lemma dec_pair_exists_roro: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is ro f1 -> is ro f2 -> is ro (pair f1 f2).
 Proof.
     intros. apply is_pair. assumption. assumption.
 Qed.

 Lemma dec_perm_pair_exists_roro: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is ro f2 -> is ro f1 -> is ro (perm_pair f1 f2).
 Proof.
     intros. apply is_perm_pair. assumption. assumption.
 Qed.

 (* --- A pure function and an accessor: Existence --- *) 

 Lemma dec_pair_exists_purero: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is pure f1 -> is ro f2 -> is ro (pair f1 f2).
 Proof.
     intros. apply is_pair. apply is_pure_ro.
     assumption. assumption.
 Qed.

 Lemma dec_perm_pair_exists_ropure: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is pure f2 -> is ro f1 -> is ro (perm_pair f1 f2).
 Proof.
     intros. apply is_perm_pair. 
     assumption. apply is_pure_ro.
     assumption.
 Qed.

 (* --- A pair of pure functions: Existence --- *) 

 Lemma dec_pair_exists_purepure: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is pure f1 -> is pure f2 -> is pure (pair f1 f2).
 Proof.
     intros. apply is_pair. assumption. assumption.
 Qed.

 Lemma dec_perm_pair_exists_purepure: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 is pure f2 -> is pure f1 -> is pure (perm_pair f1 f2).
 Proof.
     intros. apply is_perm_pair. assumption. assumption.
 Qed.

(* -------------------- End of Derived Pair Existencies -------------------- *)

(* --- Derived Pair Projections: --- *)

(* --- A pair of modifiers: Projections --- *) 

 (* ...Nothing to be proven... *)

(* --- An accessor and a modifier: Projections --- *) 

 Lemma strong_perm_proj_pi1_rwro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is ro f2 -> pi1 o perm_pair f1 f2 == f1.
 Proof.
     intros. unfold perm_pair. 
     transitivity (pi2 o pair f2 f1).
     rewrite assoc. apply strong_subs. unfold permut.
     apply one_weak_to_strong. apply is_comp.
     apply is_pure_ro. apply is_pi1.
     apply is_pair. apply is_pure_ro. apply is_pi2.
     apply is_pure_ro. apply is_pi1.
     apply is_pure_ro. apply is_pi2.
     remember weak_proj_pi1_rorw.
     specialize(@weak_proj_pi1_rorw _ _ _
     (@pi2 Y' Y) (pi1)).
     intros. apply H0. 
     apply is_pure_ro. apply is_pi2.
     apply strong_proj_pi2_rorw. assumption. 
 Qed.

 Lemma weak_perm_proj_pi2_rwro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is ro f2 -> pi2 o perm_pair f1 f2 ~~ f2.
 Proof.
     intros. unfold perm_pair. rewrite assoc.
     transitivity (pi1 o  pair f2 f1). unfold permut.
     apply weak_subs. apply strong_to_weak.
     specialize(@strong_proj_pi2_rorw _ _ _
     (@pi2 Y' Y) (pi1)).
     intros. apply H0.
     apply is_pure_ro. apply is_pi2.
     apply weak_proj_pi1_rorw. assumption.
 Qed.

 (* --- A pure function and a modifier: Projections --- *) 

 Lemma weak_proj_pi1_purerw: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is pure f1 -> pi1 o pair f1 f2 ~~ f1.
 Proof.
     intros. remember weak_proj_pi1_rorw.
     apply weak_proj_pi1_rorw.
     apply is_pure_ro. assumption.
 Qed.

 Lemma strong_proj_pi2_purerw: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is pure f1 -> pi2 o pair f1 f2 == f2.
 Proof.
     intros. remember strong_proj_pi2_rorw.
     apply strong_proj_pi2_rorw.
     apply is_pure_ro. assumption.
 Qed.

 Lemma strong_perm_proj_pi1_rwpure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is pure f2 -> pi1 o perm_pair f1 f2 == f1.
 Proof.
     intros. remember strong_perm_proj_pi1_rwro.
     apply strong_perm_proj_pi1_rwro.
     apply is_pure_ro. assumption.
 Qed.

 Lemma weak_perm_proj_pi2_rwpure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is pure f2 -> pi2 o perm_pair f1 f2 ~~ f2.
 Proof.
     intros. remember weak_perm_proj_pi2_rwro.
     apply weak_perm_proj_pi2_rwro.
     apply is_pure_ro. assumption.
 Qed.

 (* --- A pair of accessors: Projections --- *) 

 Lemma strong_proj_pi1_roro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is ro f1 ->  is ro f2 -> pi1 o pair f1 f2 == f1.
 Proof.
     intros. remember weak_proj_pi1_rorw.
     apply one_weak_to_strong. apply is_comp.
     apply is_pure_ro. apply is_pi1.
     apply is_pair. assumption. assumption.
     assumption. apply weak_proj_pi1_rorw.
     assumption.
 Qed.

 Lemma strong_proj_pi2_roro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is ro f1 ->  is ro f2 -> pi2 o pair f1 f2 == f2.
 Proof.
     intros. remember strong_proj_pi2_rorw.
     apply strong_proj_pi2_rorw.
     assumption.
 Qed.

 Lemma strong_perm_proj_pi1_roro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is ro f2 ->  is ro f1 -> pi1 o perm_pair f1 f2 == f1.
 Proof.
     intros. remember strong_perm_proj_pi1_rwro.
     apply strong_perm_proj_pi1_rwro.
     assumption.
 Qed.

 Lemma strong_perm_proj_pi2_roro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
  is ro f2 ->  is ro f1 -> pi2 o perm_pair f1 f2 == f2.
 Proof.
     intros. remember weak_perm_proj_pi2_rwro.
     apply one_weak_to_strong. apply is_comp.
     apply is_pure_ro. apply is_pi2.
     apply is_perm_pair. assumption. assumption.
     assumption. apply weak_perm_proj_pi2_rwro.
     assumption.
 Qed.

 (* --- A pure function and an accessor: Projections --- *) 

 Lemma strong_proj_pi1_purero: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is pure f1 -> is ro f2 -> pi1 o pair f1 f2 == f1.
 Proof.
     intros. remember weak_proj_pi1_purerw.
     apply one_weak_to_strong. apply is_comp.
     apply is_pure_ro. apply is_pi1.
     apply is_pair. apply is_pure_ro. 
     assumption. assumption. apply is_pure_ro.
     assumption. apply weak_proj_pi1_purerw.
     assumption.
 Qed.

 Lemma strong_proj_pi2_purero: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is pure f1 ->  is ro f2 -> pi2 o pair f1 f2 == f2.
 Proof.
     intros. remember strong_proj_pi2_purerw.
     apply strong_proj_pi2_purerw.
     assumption.
 Qed.

 Lemma strong_perm_proj_pi1_ropure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is pure f2 -> is ro f1 -> pi1 o perm_pair f1 f2 == f1.
 Proof.
     intros. remember strong_perm_proj_pi1_rwpure.
     apply strong_perm_proj_pi1_rwpure.
     assumption.
 Qed.

 Lemma strong_perm_proj_pi2_ropure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
  is pure f2 ->  is ro f1 -> pi2 o perm_pair f1 f2 == f2.
 Proof.
     intros. remember weak_perm_proj_pi2_rwpure.
     apply one_weak_to_strong. apply is_comp.
     apply is_pure_ro. apply is_pi2.
     apply is_perm_pair. assumption. apply is_pure_ro.
     assumption. apply is_pure_ro. assumption.
     apply weak_perm_proj_pi2_rwpure.
     assumption.
 Qed.

 (* --- A pair of pure functions: Projections --- *) 

 Lemma strong_proj_pi1_purepure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is pure f1 -> is pure f2 -> pi1 o pair f1 f2 == f1.
 Proof.
     intros. apply strong_proj_pi1_purero.
     assumption. apply is_pure_ro. assumption.
 Qed.

 Lemma strong_proj_pi2_purepure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is pure f1 ->  is pure f2 -> pi2 o pair f1 f2 == f2.
 Proof.
     intros. remember strong_proj_pi2_purero.
     apply strong_proj_pi2_purero.
     assumption. apply is_pure_ro. assumption.
 Qed.

 Lemma strong_perm_proj_pi1_purepure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is pure f2 -> is pure f1 -> pi1 o perm_pair f1 f2 == f1.
 Proof.
     intros. remember strong_perm_proj_pi1_ropure.
     apply strong_perm_proj_pi1_ropure.
     assumption. apply is_pure_ro. assumption.
 Qed.

 Lemma strong_perm_proj_pi2_purepure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
  is pure f2 ->  is pure f1 -> pi2 o perm_pair f1 f2 == f2.
 Proof.
     intros. remember strong_perm_proj_pi2_ropure.
     apply strong_perm_proj_pi2_ropure.
     assumption. apply is_pure_ro. assumption.
 Qed.

(* -------------------- End of Derived Pair Projections -------------------- *)

End Make.
