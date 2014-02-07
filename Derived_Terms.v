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
Require Memory Terms Decorations Axioms.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export Derived_TermsExp := Axioms.Make(M). 

 Definition prod_forget {X Y}: term unit (X/*/Y) := (@forget (X/*/Y)).
 Definition iso {X}: term (X/*/unit) X := pair (@id X) (@forget X). 
 Definition inv_pi1 {X}: term (X/*/unit) X := pair (@id X) (@forget X). 
 Definition permut {X Y}: term (X/*/Y) (Y/*/X) := pair (@pi2 Y X) (@pi1 Y X).
 
 Definition perm_pair {X Y Z} (f: term Y X) (g: term Z X): term (Y/*/Z) X
 := permut o pair g f.
 Definition prod {X Y X' Y'} (f: term X X') (g: term Y Y'): term (X/*/Y) (X'/*/Y')
 := pair (f o (@pi1 X' Y')) (g o (@pi2 X' Y')).
 Definition perm_prod {X Y X' Y'} (f: term X X') (g: term Y Y'): term (X/*/Y) (X'/*/Y')
 := perm_pair (f o (@pi1 X' Y')) (g o (@pi2 X' Y')).

 Check boolT.

 (*For exceptions*)

 Definition throw (X: Type) (t2: EName) := (@empty X) o tag t2.
 Definition exc_iso {X}: term (X/+/empty_set) X := (@copi1 X empty_set).
 Definition TRY {X Y} (f: term Y X) (k: term Y empty_set)
  := (copair id k) o exc_iso o f.
 Definition TRY_CATCH (X Y: Type) (t: EName) (f: term Y X) (g: term Y unit)
  := downcast((copair (@id Y) (g o (untag t))) o exc_iso o f).

 Lemma is_ttrue: is pure (@copi1 unit unit).
 Proof. auto. Qed.

 Lemma is_ffalse: is pure (@copi2 unit unit).
 Proof. auto. Qed.
 
 Lemma is_prod_forget X Y: is pure (@prod_forget X Y).
 Proof.
     unfold prod_forget. apply is_forget.
 Qed.

 Lemma is_inv_pi1 X: is pure (@inv_pi1 X).
 Proof.
     unfold inv_pi1. apply is_pair.
     apply is_id. apply is_forget.
 Qed.
 
 Lemma is_permut X Y: is pure (@permut X Y).
 Proof.
     unfold permut. apply is_pair. 
     apply is_pi2. apply is_pi1.
 Qed.

 Lemma is_perm_pair: forall k X Y Z (f: term Y X) (g: term Z X),
 is k f -> is k g -> is k (perm_pair f g).
 Proof.
     intros. unfold perm_pair. apply is_comp.
     induction k. apply is_permut. apply is_pure_ro.
     apply is_permut. apply is_ro_rw. apply is_pure_ro.
     apply is_permut. apply is_pair.
     assumption. assumption.
 Qed.

 Lemma is_prod: forall k X' X Y' Y (f: term X X') (g: term Y Y'), 
 is k f -> is k g -> is k (prod f g).
 Proof.
     intros. apply is_pair. apply is_comp. assumption.
     induction k. apply is_pi1. apply is_pure_ro. apply is_pi1. 
     apply is_ro_rw. apply is_pure_ro. apply is_pi1.
     apply is_comp. assumption.
     induction k. apply is_pi2. apply is_pure_ro. apply is_pi2. 
     apply is_ro_rw. apply is_pure_ro. apply is_pi2.
 Qed. 

 Lemma is_perm_prod: forall k X' X Y' Y (f: term X X') (g: term Y Y'), 
 is k f -> is k g -> is k (perm_pair (f o (@pi1 X' Y')) (g o (@pi2 X' Y'))).
 Proof.
     intros. apply is_perm_pair. apply is_comp. assumption.
     induction k. apply is_pi1. apply is_pure_ro. apply is_pi1. 
     apply is_ro_rw. apply is_pure_ro. apply is_pi1.
     apply is_comp. assumption.
     induction k. apply is_pi2. apply is_pure_ro. apply is_pi2. 
     apply is_ro_rw. apply is_pure_ro. apply is_pi2.
 Qed.

End Make.
