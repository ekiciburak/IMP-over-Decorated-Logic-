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
Require Memory Terms Decorations Axioms Derived_Terms Derived_Pairs.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export Derived_ProductsExp := Derived_Pairs.Make(M). 

(* --- Derived product Existencies --- *)

 (* --- A pair of modifiers: Existencies  --- *) 

 Lemma dec_prod_exists_rwrw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is rw f1 -> is rw f2 -> is rw (prod f1 f2).
 Proof.
     intros. apply is_prod. 
     assumption. assumption.
 Qed.

 Lemma dec_perm_prod_exists_rwrw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is rw f2 -> is rw f1 -> is rw (perm_prod f1 f2).
 Proof.
     intros. apply is_perm_prod. 
     assumption. assumption.
 Qed.

 (* --- An accessor and a modifier: Existencies  --- *) 

 Lemma dec_prod_exists_rorw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is ro f1 -> is rw f2 -> is rw (prod f1 f2).
 Proof.
     intros. apply is_prod.
     apply is_ro_rw. assumption. assumption.
 Qed.

 Lemma dec_perm_prod_exists_rorw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is ro f2 -> is rw f1 -> is rw (perm_prod f1 f2).
 Proof.
     intros. apply is_perm_prod.
     assumption.  apply is_ro_rw. assumption.
 Qed.

 (* --- A pure function and a modifier: Existencies  --- *) 

 Lemma dec_prod_exists_purerw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is pure f1 -> is rw f2 -> is rw (prod f1 f2).
 Proof.
     intros. apply is_prod.
     apply is_ro_rw. apply is_pure_ro.
     assumption. assumption.
 Qed.

 Lemma dec_perm_prod_exists_purerw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is pure f2 -> is rw f1 -> is rw (perm_prod f1 f2).
 Proof.
     intros. apply is_perm_prod.
     assumption. apply is_ro_rw.
     apply is_pure_ro. assumption.
 Qed.

 (* --- A pair of accessors: Existencies  --- *) 

 Lemma dec_prod_exists_roro: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is ro f1 -> is ro f2 -> is ro (prod f1 f2).
 Proof.
     intros. apply is_prod. 
     assumption. assumption.
 Qed.

 Lemma dec_perm_prod_exists_roro: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is ro f2 -> is ro f1 -> is ro (perm_prod f1 f2).
 Proof.
     intros. apply is_perm_prod. 
     assumption. assumption.
 Qed.

 (* --- A pure function and an accessor: Existencies  --- *)

 Lemma dec_prod_exists_purero: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is pure f1 -> is ro f2 -> is ro (prod f1 f2).
 Proof.
     intros. apply is_prod. 
     apply is_pure_ro. assumption. assumption.
 Qed.

 Lemma dec_perm_prod_exists_purero: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is pure f2 -> is ro f1 -> is ro (perm_prod f1 f2).
 Proof.
     intros. apply is_perm_prod. 
     assumption.  apply is_pure_ro. assumption.
 Qed.

 (* --- A pair of pure functions: Existencies  --- *) 

 Lemma dec_prod_exists_purepure: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is pure f1 -> is pure f2 -> is pure (prod f1 f2).
 Proof.
     intros. apply is_prod. 
     assumption. assumption.
 Qed.

 Lemma dec_perm_prod_exists_purepure: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 is pure f2 -> is pure f1 -> is pure (perm_prod f1 f2).
 Proof.
     intros. apply is_perm_prod. 
     assumption. assumption.
 Qed.

(* --- Derived Product Projections: Rectangular Shape --- *)
 
 (* --- Product Pair Rectangle: A pair of modifiers: Projections --- *)

   (* ...Nothing to be proven... *)

 (* --- An accessor and a modifier: Projections --- *)

 Lemma weak_proj_pi1_rorw_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is ro f -> pi1 o (prod f g) ~~ f o pi1.
 Proof.
     intros. remember weak_proj_pi1_rorw.
     apply weak_proj_pi1_rorw.
     apply is_comp. assumption.
     apply is_pure_ro. apply is_pi1.
 Qed.

 Lemma strong_proj_pi2_rorw_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is ro f -> pi2 o (prod f g) == g o pi2.
 Proof.
     intros. remember strong_proj_pi2_rorw.
     apply strong_proj_pi2_rorw.
     apply is_comp. assumption.
     apply is_pure_ro. apply is_pi1.
 Qed.

 Lemma strong_perm_proj_pi1_rwro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is ro g -> pi1 o (perm_prod f g) == f o pi1.
 Proof.
     intros. remember strong_perm_proj_pi1_rwro. 
     apply strong_perm_proj_pi1_rwro.
     apply is_comp. assumption.
     apply is_pure_ro. apply is_pi2.
 Qed.

 Lemma weak_perm_proj_pi2_rwro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is ro g -> pi2 o (perm_prod f g) ~~ g o pi2.
 Proof.
     intros. remember weak_perm_proj_pi2_rwro.
     apply weak_perm_proj_pi2_rwro.
     apply is_comp. assumption.
     apply is_pure_ro. apply is_pi2.
 Qed.

 (* --- A pure function and a modifier: Projections --- *)
 
 Lemma weak_proj_pi1_purerw_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure f -> pi1 o (prod f g) ~~ f o pi1.
 Proof.
     intros. remember weak_proj_pi1_purerw.
     apply weak_proj_pi1_purerw.
     apply is_comp. assumption. apply is_pi1.
 Qed.

 Lemma strong_proj_pi2_purerw_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure f -> pi2 o (prod f g) == g o pi2.
 Proof.
     intros. remember strong_proj_pi2_purerw.
     apply strong_proj_pi2_purerw.
     apply is_comp. assumption. apply is_pi1.
 Qed.

 Lemma strong_perm_proj_pi1_rwpure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure g -> pi1 o (perm_prod f g) == f o pi1.
 Proof.
     intros. remember strong_perm_proj_pi1_rwpure.
     apply strong_perm_proj_pi1_rwpure.
     apply is_comp. assumption. apply is_pi2.
 Qed.

 Lemma weak_perm_proj_pi2_rwpure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure g -> pi2 o (perm_prod f g) ~~ g o pi2.
 Proof.
     intros. remember weak_perm_proj_pi2_rwpure.
     apply weak_perm_proj_pi2_rwpure.
     apply is_comp. assumption. apply is_pi2.
 Qed.

 (* --- A pair of accessors: Projections --- *)

 Lemma strong_proj_pi1_roro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is ro f -> is ro g -> pi1 o (prod f g) == f o pi1.
 Proof.
     intros. remember strong_proj_pi1_roro.
     apply strong_proj_pi1_roro.
     apply is_comp. assumption. apply is_pure_ro. apply is_pi1.
     apply is_comp. assumption. apply is_pure_ro. apply is_pi2.
 Qed.

 Lemma strong_proj_pi2_roro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is ro g -> is ro f -> pi2 o (prod f g) == g o pi2.
 Proof.
     intros. remember strong_proj_pi2_roro.
     apply strong_proj_pi2_roro.
     apply is_comp. assumption. apply is_pure_ro. apply is_pi1.
     apply is_comp. assumption. apply is_pure_ro. apply is_pi2.
 Qed.

 Lemma strong_perm_proj_pi1_roro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is ro g -> is ro f -> pi1 o (perm_prod f g) == f o pi1.
 Proof.
     intros. remember strong_perm_proj_pi1_roro.
     apply strong_perm_proj_pi1_roro.
     apply is_comp. assumption. apply is_pure_ro. apply is_pi2.
     apply is_comp. assumption. apply is_pure_ro. apply is_pi1.
 Qed.

 Lemma strong_perm_proj_pi2_roro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is ro g -> is ro f -> pi2 o (perm_prod f g) == g o pi2.
 Proof.
     intros. remember strong_perm_proj_pi2_roro.
     apply strong_perm_proj_pi2_roro.
     apply is_comp. assumption. apply is_pure_ro. apply is_pi2.
     apply is_comp. assumption. apply is_pure_ro. apply is_pi1.
 Qed.

 (* --- A pure function and an accessor: Projections --- *)

 Lemma strong_proj_pi1_purero_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure f -> is ro g -> pi1 o (prod f g) == f o pi1.    
 Proof.
     intros. remember strong_proj_pi1_purero.
     apply strong_proj_pi1_purero.
     apply is_comp. assumption. apply is_pi1.
     apply is_comp. assumption. 
     apply is_pure_ro. apply is_pi2.
 Qed.

 Lemma strong_proj_pi2_purero_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure f -> is ro g -> pi2 o (prod f g) == g o pi2. 
 Proof.
     intros. remember strong_proj_pi2_purero.
     apply strong_proj_pi2_purero.
     apply is_comp. assumption. apply is_pi1.
     apply is_comp. assumption. 
     apply is_pure_ro. apply is_pi2.
 Qed.

 Lemma strong_perm_proj_pi1_ropure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure g -> is ro f -> pi1 o (perm_prod f g) == f o pi1.    
 Proof.
     intros. remember strong_perm_proj_pi1_ropure.
     apply strong_perm_proj_pi1_ropure.
     apply is_comp. assumption. apply is_pi2.
     apply is_comp. assumption. 
     apply is_pure_ro. apply is_pi1.
 Qed.

 Lemma strong_perm_proj_pi2_ropure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure g -> is ro f -> pi2 o (perm_prod f g) == g o pi2. 
 Proof.
     intros. remember strong_perm_proj_pi2_ropure.
     apply strong_perm_proj_pi2_ropure.
     apply is_comp. assumption. apply is_pi2.
     apply is_comp. assumption. 
     apply is_pure_ro. apply is_pi1.
 Qed.

 (* --- A pair of pure functions: Projections --- *)

 Lemma strong_proj_pi1_purepure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure f -> is pure g -> pi1 o (prod f g) == f o pi1.
 Proof.
     intros. remember strong_proj_pi1_purepure.
     apply strong_proj_pi1_purepure.
     apply is_comp. assumption. apply is_pi1.
     apply is_comp. assumption. apply is_pi2.
 Qed.

 Lemma strong_proj_pi2_purepure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure f -> is pure g -> pi2 o (prod f g) == g o pi2.
 Proof.
     intros. remember strong_proj_pi2_purepure.
     apply strong_proj_pi2_purepure.
     apply is_comp. assumption. apply is_pi1.
     apply is_comp. assumption. apply is_pi2.
 Qed.

 Lemma strong_perm_proj_pi1_purepure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure g -> is pure f -> pi1 o (perm_prod f g) == f o pi1.
 Proof.
     intros. remember strong_perm_proj_pi1_purepure.
     apply strong_perm_proj_pi1_purepure.
     apply is_comp. assumption. apply is_pi2.
     apply is_comp. assumption. apply is_pi1.
 Qed.

 Lemma strong_perm_proj_pi2_purepure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   is pure g -> is pure f -> pi2 o (perm_prod f g) == g o pi2.
 Proof.
     intros. remember strong_perm_proj_pi2_purepure.
     apply strong_perm_proj_pi2_purepure.
     apply is_comp. assumption. apply is_pi2.
     apply is_comp. assumption. apply is_pi1.
 Qed.

End Make.
