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
Require Memory Terms Decorations Derived_Terms Axioms Derived_Pairs Derived_Products.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export Derived_RulesExp := Derived_Products.Make(M). 

(* --- Derived Rules --- *)

 Lemma weak_refl: forall X Y (f: term Y X), f ~~ f.
 Proof. intros. apply strong_to_weak. apply strong_refl. Qed.
 
 Lemma zero_weak_to_strong: forall X Y (f g: term Y X),
 PURE f -> PURE g -> f ~~ g  -> f == g.
 Proof. intros. apply one_weak_to_strong; decorate. Qed.

 Lemma weak_final_unit: forall X (f: term unit X), f ~~ forget.
 Proof. intros. apply weak_final_unique. Qed.

 Lemma E_1_1: forall X (f g: term unit X), RO f -> RO g -> f == g.
 Proof. intros. apply one_weak_to_strong; (solve[decorate] || idtac). apply weak_final_unique. Qed.

 Lemma E_0_1: forall X (f g : term unit X), PURE f -> PURE g -> f == g.
 Proof. intros. apply one_weak_to_strong; try decorate. apply weak_final_unique. Qed.

 Lemma E_1_2: forall X (f: term unit X), RO f -> f == forget.
 Proof. intros. apply one_weak_to_strong; (solve[decorate] || idtac). apply weak_final_unique. Qed.
 
 Lemma E_0_2: forall X (f: term unit X), PURE f -> f == forget.
 Proof. intros. apply one_weak_to_strong; (solve[decorate] || idtac). apply weak_final_unique. Qed.

 Lemma E_1_3: forall X Y (g: term unit Y) (h: term unit X) 
 (f: term Y X),  RO g -> RO h -> RO f -> h == g o f.
 Proof. intros. apply one_weak_to_strong; (solve[decorate] || idtac). apply weak_final_unique. Qed.

 Lemma E_0_3: forall X Y (g: term unit Y) (h: term unit X) 
 (f: term Y X), PURE g -> PURE h -> PURE f -> h == g o f.
 Proof. intros. apply one_weak_to_strong; (solve[decorate] || idtac). apply weak_final_unique. Qed.

 Lemma E_1_4: forall X (f: term X unit), RO f -> forget o f == (@id unit).
 Proof. intros. apply one_weak_to_strong; (solve[decorate] || idtac). apply weak_final_unique. Qed.

 Lemma E_0_4: forall X (f: term X unit), PURE f -> forget o f == (@id unit).
 Proof. intros. apply one_weak_to_strong; (solve[decorate] || idtac). apply weak_final_unique. Qed.

 Lemma strong_unit_pi1__prod_forget: forall X Y: Type, 
       forget o pi1 == (@prod_forget X Y).
 Proof.
     intros. specialize(@E_0_3 _ _ forget prod_forget (@pi1 X Y)).
     intros. apply strong_sym. apply H; decorate.
 Qed.

 Lemma strong_unit_pi2__prod_forget: forall X Y: Type,
       forget o pi2 == (@prod_forget X Y).
 Proof.
     intros. specialize(@E_0_3 _ _ forget prod_forget (@pi2 X Y)).
     intros. apply strong_sym. apply H; decorate.
 Qed.

Lemma strong_pi1_inv_pi1__id: forall X: Type, pi1 o inv_pi1 == (@id X).
 Proof. intros. apply strong_proj_pi1_purepure; decorate. Qed.

 Lemma strong_pi2_inv_pi1__unit: forall X: Type, pi2 o inv_pi1 == (@forget X).
 Proof. intros. apply strong_proj_pi2_purepure; decorate. Qed.

 Lemma strong_pi1_permut__pi2: forall X Y: Type, pi1 o permut == (@pi2 X Y).
 Proof. intros. apply strong_proj_pi1_purepure; decorate. Qed.

 Lemma strong_pi2_permut__pi1: forall X Y: Type, pi2 o permut == (@pi1 X Y).
 Proof. intros. apply strong_proj_pi2_purepure; decorate. Qed.
 
 Lemma unicity_rect: forall X X' Y Y'(f g: term (Y*Y') (X*X')),
   (pi1 o f ~~ pi1 o g) -> (pi2 o f ~~ pi2 o g) -> f ~~ g.
 Proof. intros. apply unicity; assumption. Qed.
 
 Lemma strong_unicity: forall X Y Y'(f g: term (Y*Y') X),
   (pi1 o f ~~ pi1 o g) -> (pi2 o f == pi2 o g) -> f == g.
 Proof.
     intros. apply comp_final_unique. remember sc.
     specialize (@E_0_1 _ (forget) (forget o (@pi2 Y Y'))). intros.
     rewrite H1; (solve[decorate] || idtac). repeat rewrite <- assoc. apply sc. 
     apply strong_refl. assumption. 
     apply unicity. assumption. apply strong_to_weak. assumption.
 Qed.
 
 Lemma strong_perm_unicity: forall X Y Y'(f g: term (Y'*Y) X),
   (pi1 o f == pi1 o g) -> (pi2 o f ~~ pi2 o g) -> f == g.
 Proof.
     intros. apply comp_final_unique. remember sc.
     specialize (@E_0_1 _ (forget) (forget o (@pi1 Y' Y))). intros.
     rewrite H1; (solve[decorate] || idtac). repeat rewrite <- assoc. apply sc. 
     apply strong_refl. assumption. 
     apply unicity. apply strong_to_weak. assumption. assumption.
 Qed.

 Lemma strong_unicity_rect: forall X X' Y Y'(f g: term (Y*Y') (X*X')),
   (pi1 o f ~~ pi1 o g) -> (pi2 o f == pi2 o g) -> f == g.
 Proof. intros. apply strong_unicity; assumption. Qed.

 Lemma strong_perm_unicity_rect: forall X X' Y Y'(f g: term (Y*Y') (X*X')),
   (pi1 o f == pi1 o g) -> (pi2 o f ~~ pi2 o g) -> f == g.
 Proof. intros. apply strong_perm_unicity; assumption. Qed.

 Lemma permuted_pair: forall X Y' Y (f1: term Y X) (f2: term Y' X), 
  RO f1 -> permut o perm_pair f2 f1 == pair f1 f2.
 Proof.
     intros. apply strong_unicity. rewrite assoc. remember wsc.
     rewrite strong_pi1_permut__pi2. rewrite weak_perm_proj_pi2_rwro; (solve[decorate] || idtac).
     apply weak_sym. apply weak_proj_pi1_rorw; decorate.
     rewrite assoc. remember sc. rewrite strong_pi2_permut__pi1.
     rewrite strong_perm_proj_pi1_rwro; (solve[decorate] || idtac). apply strong_sym.
     apply strong_proj_pi2_rorw; decorate.
 Qed. 

 Lemma obs_local_global_2: forall X Y (f g : term Y X),
 (forall i: Loc, lookup i o forget o f ~~ lookup i o forget o g) ->  f ~~ g -> f == g.
 Proof.
     intros. apply comp_final_unique. apply observation. intros.
     rewrite assoc. rewrite assoc. apply H. assumption.
 Qed.

 (* additional lemmas about [passbool] and [copair] *)
 Lemma passbool_true: passbool o constant true == copi1.
 Proof.
     unfold passbool. unfold constant. rewrite pure_pure. unfold copi1.
     apply pure_eq. intros. simpl. rewrite x. reflexivity.
 Qed.

 Lemma passbool_false: passbool o constant false == copi2.
 Proof. 
    unfold passbool. unfold constant. setoid_rewrite pure_pure.
    apply pure_eq.  now intros [].
 Qed.

 Lemma copair_true A f g: @copair _ _ A f g o (passbool o constant true) == f.
 Proof. rewrite passbool_true. apply strong_coproj_copi1_rwrw. Qed.

 Lemma copair_false A f g: @copair _ _ A f g o (passbool o constant false) == g.
 Proof. rewrite passbool_false. apply strong_coproj_copi2_rwrw. Qed.

(* -------------------- End of Derived Rules -------------------- *)

End Make.
