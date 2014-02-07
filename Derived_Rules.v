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
Require Memory Terms Decorations Axioms Derived_Terms Derived_Pairs Derived_Products.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export Derived_RulesExp := Derived_Products.Make(M). 

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

 Lemma strong_unit_pi1__prod_forget: forall Y Z: Set,
	 forget o pi1 == (@prod_forget Y Z).
 Proof.
     intros. remember E_0_3. 
     specialize(@E_0_3 _ _ forget prod_forget (@pi1 Y Z)).
     intros. apply strong_sym. apply H. apply is_forget. 
     apply is_prod_forget. apply is_pi1.
 Qed.

 Lemma strong_unit_pi2__prod_forget: forall (Y Z: Set),
 forget o pi2 == (@prod_forget Y Z).
 Proof.
     intros. remember E_0_3. 
     specialize(@E_0_3 _ _ forget prod_forget (@pi2 Y Z)).
     intros. apply strong_sym. apply H. apply is_forget. 
     apply is_prod_forget. apply is_pi2.
 Qed.

Lemma strong_pi1_inv_pi1__id: forall Y: Set,
pi1 o inv_pi1 == (@id Y).
 Proof.
     intros. unfold inv_pi1.
     remember strong_proj_pi1_purepure.
     specialize(@strong_proj_pi1_purepure _ _ _
     id (@forget Y)). 
     intros. apply H. apply is_id. apply is_forget.
 Qed.

 Lemma strong_pi2_inv_pi1__unit: forall Y: Set,
 pi2 o inv_pi1 == (@forget Y).
 Proof.
     intros. remember strong_proj_pi2_purepure.
     specialize(@strong_proj_pi2_purepure _ _ _
     id (@forget Y)). unfold inv_pi1. 
     intros. apply H. apply is_id. apply is_forget.
 Qed.

 Lemma strong_pi1_permut__pi2: forall Y Z: Set,
 pi1 o permut == (@pi2 Y Z).
 Proof.
     intros. unfold permut.
     remember strong_proj_pi1_purepure.
     specialize(@strong_proj_pi1_purepure _ _ _
     (@pi2 Y Z) (pi1)).
     intros. apply H. 
     apply is_pi2. apply is_pi1. 
 Qed.

 Lemma strong_pi2_permut__pi1: forall Y Z: Set,
 pi2 o permut == (@pi1 Y Z).
 Proof.
     intros. remember strong_proj_pi2_purepure.
     specialize(@strong_proj_pi2_purepure _ _ _
     (@pi2 Y Z) (pi1)). unfold permut. 
     intros. apply H.
     apply is_pi2. apply is_pi1. 
 Qed.
 
 Lemma unicity_rect: forall X X' Y Y'(f g: term (Y/*/Y') (X/*/X')),
   (pi1 o f ~~ pi1 o g) -> (pi2 o f ~~ pi2 o g) -> f ~~ g.
 Proof.
     intros. remember unicity. apply unicity.
     assumption. assumption.
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
 
 Lemma strong_perm_unicity: forall X Y Y'(f g: term (Y'/*/Y) X),
   (pi1 o f == pi1 o g) -> (pi2 o f ~~ pi2 o g) -> f == g.
 Proof.
     intros.
     remember comp_final_unique.
     remember unicity.
     apply comp_final_unique.
     transitivity (forget o pi1 o f).
     apply strong_subs.
     apply E_0_1. apply is_forget. 
     apply is_comp.
     apply is_forget. apply is_pi1.
     apply strong_sym.

     transitivity (forget o pi1 o g).
     apply strong_subs.
     apply E_0_1. apply is_forget.
     apply is_comp.
     apply is_forget. apply is_pi1.
     setoid_rewrite <- assoc at 1.
     setoid_rewrite <- assoc at 1.
     apply strong_repl.
     apply strong_sym. assumption.

     apply unicity.
     apply strong_to_weak.
     assumption.
     assumption.
 Qed.

 Lemma strong_unicity_rect: forall X X' Y Y'(f g: term (Y/*/Y') (X/*/X')),
   (pi1 o f ~~ pi1 o g) -> (pi2 o f == pi2 o g) -> f == g.
 Proof.
     intros. remember strong_unicity.
     specialize (@strong_unicity _ _ _ f g).
     intros. apply H1. assumption. assumption.
 Qed.

 Lemma strong_perm_unicity_rect: forall X X' Y Y'(f g: term (Y/*/Y') (X/*/X')),
   (pi1 o f == pi1 o g) -> (pi2 o f ~~ pi2 o g) -> f == g.
 Proof.
     intros. remember strong_perm_unicity.
     specialize (@strong_perm_unicity _ _ _ f g).
     intros. apply H1. assumption. assumption.
 Qed.

 Lemma permuted_pair: forall X Y' Y (f1: term Y X) (f2: term Y' X), 
  is ro f1 -> permut o perm_pair f2 f1 == pair f1 f2.
 Proof.
     intros. remember strong_unicity.
     specialize (@strong_unicity _ _ _ (permut o perm_pair f2 f1) (pair f1 f2)).
     intros. apply H0.
     transitivity (pi2 o perm_pair f2 f1).
     rewrite -> assoc. apply weak_subs.

     remember weak_proj_pi1_rorw.
     specialize(@weak_proj_pi1_rorw _ _ _
     (@pi2 Y' Y) (pi1)).
     intros. apply H1.
     apply is_pure_ro. apply is_pi2.
 
     transitivity (f1).
     apply weak_perm_proj_pi2_rwro. assumption.
     apply weak_sym.
     apply weak_proj_pi1_rorw. assumption.
     
     transitivity (pi1 o  perm_pair f2 f1).
     rewrite assoc. apply strong_subs.
     
     remember strong_proj_pi2_rorw.
     specialize(@strong_proj_pi2_rorw _ _ _
     (@pi2 Y' Y) (pi1)). unfold permut. 
     intros. apply H1.
     apply is_pure_ro. apply is_pi2.
     
     transitivity (f2).
     apply strong_perm_proj_pi1_rwro. assumption.

     apply strong_sym.
     apply strong_proj_pi2_rorw. assumption.
 Qed. 

 Lemma obs_local_global_2: forall X Y (f g : term Y X),
 (forall i: Loc, lookup i o forget o f ~~ lookup i o forget o g) ->  f ~~ g -> f == g.
 Proof.
     intros. remember comp_final_unique.
     specialize (@comp_final_unique _ _ f g).
     intros. apply H1.
     remember observation.
     specialize (@observation _ (forget o f) (forget o g)).
     intros. apply H2. 
     setoid_rewrite assoc at 1. 
     setoid_rewrite assoc at 1.
     assumption. assumption.
 Qed.

(* -------------------- End of Derived Rules -------------------- *)

End Make.
