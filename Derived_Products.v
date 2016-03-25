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
Require Memory Terms Decorations Axioms Derived_Terms Derived_Pairs.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export Derived_ProductsExp := Derived_Pairs.Make(M). 

(* --- Derived product Existencies --- *)

 (* --- A pair of modifiers: Existencies  --- *) 

 Lemma dec_prod_exists_rwrw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 RW f1 -> RW f2 -> RW (prod f1 f2).
 Proof. intros. decorate. Qed.

 Lemma dec_perm_prod_exists_rwrw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 RW f2 -> RW f1 -> RW (perm_prod f1 f2).
 Proof. intros. decorate. Qed.

 (* --- An accessor and a modifier: Existencies  --- *) 

 Lemma dec_prod_exists_rorw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 RO f1 -> RW f2 -> RW (prod f1 f2).
 Proof. intros. decorate. Qed.

 Lemma dec_perm_prod_exists_rorw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 RO f2 -> RW f1 -> RW (perm_prod f1 f2).
 Proof. intros. decorate. Qed.

 (* --- A pure function and a modifier: Existencies  --- *) 

 Lemma dec_prod_exists_purerw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 PURE f1 -> RW f2 -> RW (prod f1 f2).
 Proof. intros. decorate. Qed.

 Lemma dec_perm_prod_exists_purerw: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 PURE f2 -> RW f1 -> RW (perm_prod f1 f2).
 Proof. intros. decorate. Qed.

 (* --- A pair of accessors: Existencies  --- *) 

 Lemma dec_prod_exists_roro: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 RO f1 -> RO f2 -> RO (prod f1 f2).
 Proof. intros. decorate. Qed.

 Lemma dec_perm_prod_exists_roro: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 RO f2 -> RO f1 -> RO (perm_prod f1 f2).
 Proof. intros. decorate. Qed.

 (* --- A pure function and an accessor: Existencies  --- *)

 Lemma dec_prod_exists_purero: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 PURE f1 -> RO f2 -> RO (prod f1 f2).
 Proof. intros. decorate. Qed.

 Lemma dec_perm_prod_exists_purero: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 PURE f2 -> RO f1 -> RO (perm_prod f1 f2).
 Proof. intros. decorate. Qed.

 (* --- A pair of pure functions: Existencies  --- *) 

 Lemma dec_prod_exists_purepure: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 PURE f1 -> PURE f2 -> PURE (prod f1 f2).
 Proof. intros. solve[decorate]. Qed.

 Lemma dec_perm_prod_exists_purepure: forall X X' Y Y' (f1: term Y X) (f2: term Y' X'),
 PURE f2 -> PURE f1 -> PURE (perm_prod f1 f2).
 Proof. intros. decorate. Qed.

(* --- Derived Product Projections: Rectangular Shape --- *)
 
 (* --- Product Pair Rectangle: A pair of modifiers: Projections --- *)

   (* ...Nothing to be proven... *)

 (* --- An accessor and a modifier: Projections --- *)

 Lemma weak_proj_pi1_rorw_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   RO f -> pi1 o (prod f g) ~~ f o pi1.
 Proof. intros. apply weak_proj_pi1_rorw; decorate. Qed.

 Lemma strong_proj_pi2_rorw_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   RO f -> pi2 o (prod f g) == g o pi2.
 Proof. intros. apply strong_proj_pi2_rorw; decorate. Qed.

 Lemma strong_perm_proj_pi1_rwro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   RO g -> pi1 o (perm_prod f g) == f o pi1.
 Proof. intros. apply strong_perm_proj_pi1_rwro; decorate. Qed.

 Lemma weak_perm_proj_pi2_rwro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   RO g -> pi2 o (perm_prod f g) ~~ g o pi2.
 Proof. intros. apply weak_perm_proj_pi2_rwro; decorate. Qed.

 (* --- A pure function and a modifier: Projections --- *)
 
 Lemma weak_proj_pi1_purerw_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   PURE f -> pi1 o (prod f g) ~~ f o pi1.
 Proof. intros. apply weak_proj_pi1_purerw; decorate. Qed.

 Lemma strong_proj_pi2_purerw_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   PURE f -> pi2 o (prod f g) == g o pi2.
 Proof. intros. apply strong_proj_pi2_purerw; decorate. Qed.

 Lemma strong_perm_proj_pi1_rwpure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   PURE g -> pi1 o (perm_prod f g) == f o pi1.
 Proof. intros. apply strong_perm_proj_pi1_rwpure; decorate. Qed.

 Lemma weak_perm_proj_pi2_rwpure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
  PURE g -> pi2 o (perm_prod f g) ~~ g o pi2.
 Proof. intros. apply weak_perm_proj_pi2_rwpure; decorate. Qed.

 (* --- A pair of accessors: Projections --- *)

 Lemma strong_proj_pi1_roro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   RO f -> RO g -> pi1 o (prod f g) == f o pi1.
 Proof. intros. apply strong_proj_pi1_roro; decorate. Qed.

 Lemma strong_proj_pi2_roro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   RO g -> RO f -> pi2 o (prod f g) == g o pi2.
 Proof. intros. apply strong_proj_pi2_roro; decorate. Qed.

 Lemma strong_perm_proj_pi1_roro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   RO g -> RO f -> pi1 o (perm_prod f g) == f o pi1.
 Proof. intros. apply strong_perm_proj_pi1_roro; decorate. Qed.

 Lemma strong_perm_proj_pi2_roro_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   RO g -> RO f -> pi2 o (perm_prod f g) == g o pi2.
 Proof. intros. apply strong_perm_proj_pi2_roro; decorate. Qed.

 (* --- A pure function and an accessor: Projections --- *)

 Lemma strong_proj_pi1_purero_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   PURE f -> RO g -> pi1 o (prod f g) == f o pi1.    
 Proof. intros. apply strong_proj_pi1_purero; decorate. Qed.

 Lemma strong_proj_pi2_purero_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   PURE f -> RO g -> pi2 o (prod f g) == g o pi2. 
 Proof. intros. apply strong_proj_pi2_purero; decorate. Qed.

 Lemma strong_perm_proj_pi1_ropure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   PURE g -> RO f -> pi1 o (perm_prod f g) == f o pi1.    
 Proof. intros. apply strong_perm_proj_pi1_ropure; decorate. Qed.

 Lemma strong_perm_proj_pi2_ropure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   PURE g -> RO f -> pi2 o (perm_prod f g) == g o pi2. 
 Proof. intros. apply strong_perm_proj_pi2_ropure; decorate. Qed.

 (* --- A pair of pure functions: Projections --- *)

 Lemma strong_proj_pi1_purepure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   PURE f -> PURE g -> pi1 o (prod f g) == f o pi1.
 Proof. intros. apply strong_proj_pi1_purepure; decorate. Qed.

 Lemma strong_proj_pi2_purepure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   PURE f -> PURE g -> pi2 o (prod f g) == g o pi2.
 Proof. intros. apply strong_proj_pi2_purepure; decorate. Qed.

 Lemma strong_perm_proj_pi1_purepure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   PURE g -> PURE f -> pi1 o (perm_prod f g) == f o pi1.
 Proof. intros. apply strong_perm_proj_pi1_purepure; decorate. Qed.

 Lemma strong_perm_proj_pi2_purepure_rect: forall X' X Y' Y (f: term X' X) (g: term Y' Y),
   PURE g -> PURE f -> pi2 o (perm_prod f g) == g o pi2.
 Proof. intros. apply strong_perm_proj_pi2_purepure; decorate. Qed.

 Hint Rewrite -> weak_proj_pi1_purerw
	         strong_proj_pi2_purerw 
                 weak_proj_pi1_purerw_rect
                 strong_proj_pi2_purerw_rect
		 strong_perm_proj_pi1_rwpure
		 weak_perm_proj_pi2_rwpure
		 strong_perm_proj_pi1_rwpure_rect
		 weak_perm_proj_pi2_rwpure_rect: simplify_rw.

 Hint Rewrite -> strong_proj_pi1_purero
	         strong_proj_pi2_purero 
                 strong_proj_pi1_purero_rect
                 strong_proj_pi2_purero_rect
		 strong_perm_proj_pi1_ropure
		 strong_perm_proj_pi2_ropure
		 strong_perm_proj_pi1_ropure_rect
		 strong_perm_proj_pi2_ropure_rect: simplify_ro.

 Ltac simpl_rw :=  autorewrite with simplify_rw.
 Ltac simpl_ro :=  autorewrite with simplify_ro.

 Ltac catpermpr :=
   match goal with
      | H: _ |-  pi1 o perm_pair ?f1 ?f2 == ?f1
        => apply strong_perm_proj_pi1_rwro; decorate
      | H: _ |-  pi2 o perm_pair ?f1 ?f2 ~~ ?f2
        => apply weak_perm_proj_pi2_rwro; decorate
      | H: _ |-  pi1 o perm_prod ?f ?g == ?f o pi1
        => apply strong_perm_proj_pi1_rwro_rect; decorate
      | H: _ |-  pi2 o perm_prod ?f ?g ~~ ?g o pi2
        => apply weak_perm_proj_pi2_rwro_rect; decorate
   end. 

(*                 

 || (apply one_weak_to_strong; try decorate; simpl_pairs)
                 strong_proj_pi1_purero_rect
strong_proj_pi1_purepure_rect   

          strong_proj_pi1_purepure 
                 strong_proj_pi1_purepure_rect
                 strong_proj_pi1_purero
                 strong_proj_pi1_purero_rect
strong_proj_pi1_roro
                 strong_proj_pi1_roro_rect*)

End Make.

