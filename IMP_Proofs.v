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
Require Memory Terms Decorations Axioms Derived_Terms Derived_Pairs
        Derived_Products Derived_Rules Proofs IMP_to_COQ.
Set Implicit Arguments.
Require Import ZArith.
Require Import Bool.
Open Scope Z_scope.

Module Make(Import M: Memory.T).
  Module Export IMP_ProofsExp := IMP_to_COQ.Make(M).

 Lemma IMP_ex1: forall (x y: Loc) (p q: Z), x <> y ->
   {{x ::= const p ;; (y ::= const q)}} 
   ==
   {{y ::= const q ;;  (x ::= const p)}}.
 Proof. intros. simpl. now apply commutation_update_update. Qed.

 Lemma IMP_ex2: forall (m: Loc),
       {{IFB (const true) 
           THEN (m ::= const (-30)) 
         ELSE (SKIP)
         ENDIF}}
       ==
       {{IFB (const false) 
           THEN (SKIP) 
         ELSE (m ::= const (-30))
         ENDIF}}.
 Proof. intros. simpl. now rewrite copair_true, copair_false. Qed.

 Lemma IMP_ex3: forall (x: Loc) (p q: Z),
      {{x ::= (const p)  ;;
        (x ::= (const q))}}
      ==
      {{x ::= (const q)}}.
 Proof.
     intros. simpl. apply observation. intros. destruct(Loc_dec i x). rewrite e.
     repeat rewrite assoc. rewrite axiom_1. setoid_rewrite id_tgt.
     setoid_rewrite <- id_src at 6. rewrite <- assoc. apply wrc; try decorate.
     apply weak_final_unique.
     repeat rewrite assoc. rewrite axiom_2; try auto. specialize(@E_0_4 _ (constant q)). 
     intros. setoid_rewrite <- assoc at 3. rewrite H; try decorate. rewrite id_src.
     rewrite axiom_2; auto. repeat rewrite <- assoc. apply strong_to_weak. 
     apply sc; try reflexivity. apply zero_weak_to_strong; try decorate.
     apply weak_final_unique.
 Qed.

 Lemma IMP_ex4: forall (x: Loc) (p q: Z),
      {{x ::= (const p)  ;;
        (x ::= (loc x +++ const q))}}
      ==
      {{x ::= (const (p+q))}}.
 Proof.
 intros. simpl. do 2 setoid_rewrite <- assoc at 1.
 rewrite commutation_lookup_constant_update. setoid_rewrite assoc at 2.
 rewrite IMP_IntAdd. rewrite assoc. rewrite (@IMP_ex3 x p (add(p,q))). reflexivity. 
 Qed.

 Lemma IMP_ex5: forall (x: Loc),
      {{x ::= (const 10) ;;
        IFB (loc x >> const 5) 
          THEN (x ::= (const 2)) 
        ELSE SKIP 
        ENDIF}}
      ==
      {{x ::= (const 2)}}.
 Proof.
    intros. simpl. do 2 setoid_rewrite assoc at 2. setoid_rewrite <- assoc.
    rewrite commutation_lookup_constant_update. do 2 setoid_rewrite <- assoc at 1.
    do 2 setoid_rewrite assoc at 2. rewrite IMP_IntGtT by constructor. rewrite assoc.
    rewrite strong_coproj_copi1_rwrw. rewrite (@IMP_ex3 x 10 2). reflexivity.
 Qed.

 Lemma IMP_condEx: forall (b: bool) (f g: Command),
      {{IFB const b 
          THEN (IFB const b THEN f ELSE g ENDIF) 
        ELSE g 
        ENDIF}}
      ==
      {{IFB const b 
          THEN f 
        ELSE g 
        ENDIF}}.
 Proof.
      intros. simpl. induction b. rewrite copair_true; apply strong_refl.
      setoid_rewrite copair_false; apply strong_refl.
 Qed. 

 Lemma IMP_condEx2: forall (b: bool) (f g h: Command),
       {{IFB const b
          THEN (IFB const b THEN f ELSE g ENDIF)
        ELSE h
        ENDIF}}
      ==
      {{IFB const b
          THEN f
        ELSE h
        ENDIF}}.
 Proof.
      intros. simpl. induction b. rewrite copair_true. setoid_rewrite copair_true.
      apply strong_refl. setoid_rewrite copair_false; apply strong_refl.
 Qed. 

 Lemma IMP_ex6lbdyT: forall (x : Loc) (p q r: Z), Is_true(chklt (q, r)) -> (*(bool_to_prop (chklt (q, r))) ->*)
	{{x ::= const q ;;
	  WHILE (loc x << const r)
	    DO x ::= (loc x +++ const p)
	  ENDWHILE}}
	==
	{{x ::= const (q+p) ;;
	  WHILE (loc x << const r)
	    DO x ::= (loc x +++ const p)
	  ENDWHILE}}.
 Proof.
    intros. simpl. do 2 setoid_rewrite assoc at 2. setoid_rewrite <- assoc at 1. 
     rewrite commutation_lookup_constant_update. do 2 setoid_rewrite <- assoc at 1.
     do 3 setoid_rewrite assoc at 6. rewrite IMP_IntLtT by assumption. do 2 rewrite assoc.
     rewrite strong_coproj_copi1_rwrw. do 4 rewrite <- assoc.
     rewrite commutation_lookup_constant_update. do 3 rewrite assoc. 
     setoid_rewrite <- assoc at 2. rewrite IMP_IntAdd. setoid_rewrite <- assoc at 2.
     setoid_rewrite <- assoc at 1. rewrite (@IMP_ex3 x q (add(q,p))). simpl.
     setoid_rewrite (@IMP_Loop (passbool o (tpure chklt o pair (lookup x) (constant r)))
       (update x o (tpure add o pair (lookup x) (constant p)))) at 1. reflexivity.
 Qed. 

 Lemma IMP_ex6lbdyF: forall (x : Loc) (p q r: Z), Is_true(chkge (q, r)) ->
	{{x ::= const q ;;
	  WHILE (loc x << const r)
	    DO x ::= (loc x +++ const p)
	  ENDWHILE}}
    ==
        {{x ::= const q}}.
 Proof.
     intros. simpl. do 2 setoid_rewrite assoc at 2. setoid_rewrite <- assoc at 1. 
     rewrite commutation_lookup_constant_update. do 2 setoid_rewrite <- assoc at 1.
     do 3 setoid_rewrite assoc at 6. rewrite IMP_IntLtF by assumption. do 2 rewrite assoc.
     rewrite strong_coproj_copi2_rwrw. rewrite id_tgt. reflexivity.
 Qed.

 Lemma IMP_ex15: forall (x: Loc),
	{{x ::= const 2 ;;
	  WHILE (loc x << const 11)
	    DO x ::= (loc x +++ const 4)
	  ENDWHILE}}
	==
	{{x ::= const 14}}.
 Proof.
     intros; simpl.
     rewrite(@IMP_ex6lbdyT x 4 2 11) by constructor; simpl.
     rewrite(@IMP_ex6lbdyT x 4 6 11) by constructor; simpl.
     rewrite(@IMP_ex6lbdyT x 4 10 11) by constructor; simpl.
     rewrite(@IMP_ex6lbdyF x 4 14 11) by constructor; reflexivity.
 Qed.


End Make.

   
