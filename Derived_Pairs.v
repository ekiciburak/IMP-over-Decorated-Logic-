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
Require Memory Terms Decorations Derived_Terms Axioms.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.
Require Import Bool.

Module Make(Import M: Memory.T).
  Module Export Derived_PairsExp := Axioms.Make(M). 

(* --- Derived Pair Existencies --- *)

 (* --- A pair of modifiers: Existence --- *) 

 Lemma dec_pair_exists_rwrw: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 RW f1 -> RW f2 -> RW (pair f1 f2).
 Proof. intros. decorate. Qed.

 Lemma dec_perm_pair_exists_rwrw: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 RW f2 -> RW f1 -> RW (perm_pair f1 f2).
 Proof. intros. decorate. Qed.

 (* --- An accessor and a modifier: Existence --- *)

 Lemma dec_pair_exists_rorw: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 RO f1 -> RW f2 -> RW (pair f1 f2).
 Proof. intros. decorate. Qed.

 Lemma dec_perm_pair_exists_rwro: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 RO f2 -> RW f1 -> RW (perm_pair f1 f2).
 Proof. intros. decorate. Qed.

 (* --- A pure function and a modifier: Existence*)

 Lemma dec_pair_exists_purerw: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 PURE f1 -> RW f2 -> RW (pair f1 f2).
 Proof. intros. decorate. Qed.

 Lemma dec_perm_pair_exists_rwpure: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 PURE f2 -> RW f1 -> RW (perm_pair f1 f2).
 Proof. intros. decorate. Qed.

 (* --- A pair of accessors: Existence --- *) 

 Lemma dec_pair_exists_roro: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 RO f1 -> RO f2 -> RO (pair f1 f2).
 Proof. intros. decorate. Qed.

 Lemma dec_perm_pair_exists_roro: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 RO f2 -> RO f1 -> RO (perm_pair f1 f2).
 Proof. intros. decorate. Qed.

 (* --- A pure function and an accessor: Existence --- *) 

 Lemma dec_pair_exists_purero: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 PURE f1 -> RO f2 -> RO (pair f1 f2).
 Proof. intros. decorate. Qed.

 Lemma dec_perm_pair_exists_ropure: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 PURE f2 -> RO f1 -> RO (perm_pair f1 f2).
 Proof. intros. decorate. Qed.

 (* --- A pair of pure functions: Existence --- *) 

 Lemma dec_pair_exists_purepure: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 PURE f1 -> PURE f2 -> PURE (pair f1 f2).
 Proof. intros. decorate. Qed.

 Lemma dec_perm_pair_exists_purepure: forall X Y Y' (f1: term Y X) (f2: term Y' X),
 PURE f2 -> PURE f1 -> PURE (perm_pair f1 f2).
 Proof. intros. decorate. Qed.

(* -------------------- End of Derived Pair Existencies -------------------- *)

(* --- Derived Pair Projections: --- *)

(* --- A pair of modifiers: Projections --- *) 

 (* ...Nothing to be proven... *)


 (* --- A pair of pure functions: Projections --- *) 

 Lemma strong_proj_pi1_purepure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   PURE f1 -> PURE f2 -> pi1 o pair f1 f2 == f1.
 Proof.
     intros. apply one_weak_to_strong; (decorate || idtac).
     apply weak_proj_pi1_rorw; decorate.
 Qed.

 Lemma strong_proj_pi2_purepure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   PURE f1 ->  PURE f2 -> pi2 o pair f1 f2 == f2.
 Proof. intros. apply strong_proj_pi2_rorw; decorate. Qed.

 Lemma strong_perm_proj_pi1_purepure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   PURE f2 -> PURE f1 -> pi1 o perm_pair f1 f2 == f1.
 Proof.
     intros. unfold perm_pair. unfold permut.
     apply one_weak_to_strong; try decorate. rewrite assoc.
     remember wsc. rewrite weak_proj_pi1_rorw; (solve[decorate] || idtac).
     apply strong_to_weak. apply strong_proj_pi2_rorw; decorate.
 Qed.

 Lemma strong_perm_proj_pi2_purepure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
  PURE f2 ->  PURE f1 -> pi2 o perm_pair f1 f2 == f2.
 Proof.
     intros. unfold perm_pair. unfold permut. rewrite assoc.
     remember sc. rewrite strong_proj_pi2_rorw; (solve[decorate] || idtac).
     apply one_weak_to_strong; (solve[decorate] || idtac).
     apply weak_proj_pi1_rorw; decorate.
 Qed.

 (* --- A pure function and an accessor: Projections --- *) 

 Lemma strong_proj_pi1_purero: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   PURE f1 -> RO f2 -> pi1 o pair f1 f2 == f1.
 Proof.
     intros. apply one_weak_to_strong; (solve[decorate] || idtac).
     apply weak_proj_pi1_rorw; decorate.
 Qed.

 Lemma strong_proj_pi2_purero: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   PURE f1 ->  RO f2 -> pi2 o pair f1 f2 == f2.
 Proof. intros. apply strong_proj_pi2_rorw; decorate. Qed.

 Lemma strong_perm_proj_pi1_ropure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   PURE f2 -> RO f1 -> pi1 o perm_pair f1 f2 == f1.
 Proof.
     intros. (*unfold perm_pair. unfold permut. rewrite assoc.    
     remember sc. apply one_weak_to_strong; (solve[decorate] || idtac).
     rewrite weak_proj_pi1_rorw; (solve[decorate] || idtac).
     apply strong_to_weak. apply strong_proj_pi2_rorw; decorate. *)
     unfold perm_pair. unfold permut. rewrite assoc.    
     remember sc. rewrite strong_proj_pi1_purepure; (solve[decorate] || idtac).
     apply strong_proj_pi2_rorw; decorate. 
 Qed.

 Lemma strong_perm_proj_pi2_ropure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
  PURE f2 -> RO f1 -> pi2 o perm_pair f1 f2 == f2.
 Proof.
     intros. unfold perm_pair. unfold permut. rewrite assoc.
     remember sc. rewrite strong_proj_pi2_purepure; try decorate.
     apply one_weak_to_strong; try decorate.
     apply weak_proj_pi1_rorw; decorate.
 Qed.

 (* --- A pair of accessors: Projections --- *) 

 Lemma strong_proj_pi1_roro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   RO f1 ->  RO f2 -> pi1 o pair f1 f2 == f1.
 Proof.
     intros. apply one_weak_to_strong; (solve[decorate] || idtac).
     apply weak_proj_pi1_rorw; decorate.
 Qed.

 Lemma strong_proj_pi2_roro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   RO f1 ->  RO f2 -> pi2 o pair f1 f2 == f2.
 Proof. intros. apply strong_proj_pi2_rorw; decorate. Qed.

 Lemma strong_perm_proj_pi1_roro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   RO f2 ->  RO f1 -> pi1 o perm_pair f1 f2 == f1.
 Proof.
     intros. unfold perm_pair. unfold permut. rewrite assoc.
     remember sc. rewrite strong_proj_pi1_purepure; (solve[decorate] || idtac). 
     apply strong_proj_pi2_rorw; decorate. 
 Qed.

 Lemma strong_perm_proj_pi2_roro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
  RO f2 ->  RO f1 -> pi2 o perm_pair f1 f2 == f2.
 Proof.
     intros. unfold perm_pair. unfold permut. rewrite assoc.
     remember sc. rewrite strong_proj_pi2_purepure; (solve[decorate] || idtac).
     apply one_weak_to_strong; (solve[decorate] || idtac).
     apply weak_proj_pi1_rorw; decorate. 
 Qed.

(* --- An accessor and a modifier: Projections --- *) 

 Lemma strong_perm_proj_pi1_rwro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   RO f2 -> pi1 o perm_pair f1 f2 == f1.
 Proof.
     intros. unfold perm_pair. unfold permut. rewrite assoc.
     remember sc. rewrite strong_proj_pi1_purepure; (solve[decorate] || idtac). 
     apply strong_proj_pi2_rorw; decorate. 
 Qed.

 Lemma weak_perm_proj_pi2_rwro: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   RO f2 -> pi2 o perm_pair f1 f2 ~~ f2.
 Proof.
     intros. unfold perm_pair. unfold permut. rewrite assoc.
     remember wsc. rewrite strong_proj_pi2_purepure; (solve[decorate] || idtac). 
     apply weak_proj_pi1_rorw; decorate.
 Qed.

 (* --- A pure function and a modifier: Projections --- *) 

 Lemma weak_proj_pi1_purerw: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   PURE f1 -> pi1 o pair f1 f2 ~~ f1.
 Proof. intros. apply weak_proj_pi1_rorw; decorate. Qed.

 Lemma strong_proj_pi2_purerw: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   PURE f1 -> pi2 o pair f1 f2 == f2.
 Proof. intros. apply strong_proj_pi2_rorw;decorate. Qed.

 Lemma strong_perm_proj_pi1_rwpure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   PURE f2 -> pi1 o perm_pair f1 f2 == f1.
 Proof.
     intros. unfold perm_pair. unfold permut. rewrite assoc.
     remember sc. rewrite strong_proj_pi1_purepure; (solve[decorate] || idtac). 
     apply strong_proj_pi2_rorw;decorate.
 Qed.

 Lemma weak_perm_proj_pi2_rwpure: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   PURE f2 -> pi2 o perm_pair f1 f2 ~~ f2.
 Proof.
     intros. unfold perm_pair. unfold permut. rewrite assoc. 
     remember wsc; rewrite strong_proj_pi2_purepure; (solve[decorate] || idtac). 
     apply weak_proj_pi1_rorw; decorate.
 Qed.

(* -------------------- End of Derived Pair Projections -------------------- *)

End Make.

