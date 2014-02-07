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
Require Memory Terms Decorations.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.

Module Make(Import M: Memory.T).
  Module Export AxiomsExp := Decorations.Make(M). 

 Definition ttrue:  term boolT unit := (@copi1 unit unit).
 Definition ffalse: term boolT unit := (@copi2 unit unit). 

 Check ttrue.
 Check ffalse.

 Reserved Notation "x == y" (at level 80).
 Reserved Notation "x ~~ y" (at level 80).

 Fixpoint chk_lt (a1 a2: Z) : Prop :=
  match (a1 ?= a2)%Z with 
    | Lt => True
    | _  => False
  end.

 Fixpoint chk_le (a1 a2: Z) : Prop :=
  match (a1 ?= a2)%Z with 
    | Gt => False
    | _  => True
  end.

 Fixpoint chk_gt (a1 a2: Z) : Prop :=
  match (a1 ?= a2)%Z with 
    | Gt => True
    | _  => False
  end.

 Fixpoint chk_ge (a1 a2: Z) : Prop :=
  match (a1 ?= a2)%Z with 
    | Lt => False
    | _  => True
  end.

 Fixpoint chk_eq (a1 a2: Z) : Prop :=
  match (a1 ?= a2)%Z with 
    | Eq => True
    | _  => False
  end.

 Fixpoint chk_neq (a1 a2: Z) : Prop :=
  match (a1 ?= a2)%Z with 
    | Eq => False
    | _  => True
  end.

 Inductive strong: forall X Y, relation (term X Y) := 
 | strong_refl: forall X Y (f: term X Y), f == f 
 | assoc: forall X Y Z T (f: term X Y) (g: term Y Z) (h: term Z T),
   f o (g o h) == (f o g) o h
 | id_src: forall X Y (f: term X Y), f o (@id Y) == f
 | id_tgt: forall X Y (f: term X Y), (@id X) o f == f
 | strong_subs: forall X Y Z (g1 g2: term X Y) (f: term Y Z), g1 == g2 -> g1 o f == g2 o f
 | strong_repl: forall X Y Z (g1 g2: term X Y) (f: term Z X), g1 == g2 -> f o g1 == f o g2
 | one_weak_to_strong: forall X Y (f g: term X Y), is ro f -> is ro g -> f ~~ g -> f == g

 | strong_proj_pi2_rorw: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is ro f1 -> (@pi2 Y Y') o pair f1 f2 == f2

 | strong_coproj_copi1_rwrw: forall X Y' Y (f1: term X Y) (f2: term X Y'),
   copair f1 f2 o (@copi1 Y Y') == f1 

 | strong_coproj_copi2_rwrw: forall X Y' Y (f1: term X Y) (f2: term X Y'),
   copair f1 f2 o (@copi2 Y Y') == f2 

 | observation: forall X (f g: term unit X),
   (forall i: Loc, lookup i o f ~~ lookup i o g) -> f == g

 | comp_final_unique: forall X Y (f g: term Y X),
   ((@forget Y) o f == (@forget Y) o g) -> f ~~ g -> f == g

 | counicity: forall  X Y Y'(f g: term X (Y/+/Y')),
   (f o (@copi1 Y Y') ~~ g o (@copi1 Y Y')) -> (f o (@copi2 Y Y') ~~ g o (@copi2 Y Y')) -> f == g

 | IMP_IntAdd: forall p q: Z, 
   plus o (pair (@constant Z p) (@constant Z q)) == (@constant Z (p+q))
 | IMP_IntMult: forall p q: Z, 
   mult o (pair (@constant Z p) (@constant Z q)) == (@constant Z (p*q))
 | IMP_IntGtT: forall p q: Z,
   (chk_gt p q) -> gt o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntGeT: forall p q: Z,
   (chk_ge p q) -> ge o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntEqT: forall p q: Z,
   (chk_eq p q) -> eq o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntLtT: forall p q: Z,
   (chk_lt p q) -> lt o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntLeT: forall p q: Z,
   (chk_le p q) -> le o (pair (@constant Z p) (@constant Z q)) == ttrue

 | IMP_IntGtF: forall p q: Z,
   (chk_le p q) -> gt o (pair (@constant Z p) (@constant Z q)) == ffalse
 | IMP_IntGeF: forall p q: Z,
   (chk_lt p q) -> ge o (pair (@constant Z p) (@constant Z q)) == ffalse
 | IMP_IntEqF: forall p q: Z,
   (chk_neq p q) -> eq o (pair (@constant Z p) (@constant Z q)) == ffalse
 | IMP_IntLtF: forall p q: Z,
   (chk_ge p q) -> lt o (pair (@constant Z p) (@constant Z q)) == ffalse
 | IMP_IntLeF: forall p q: Z,
   (chk_gt p q) -> le o (pair (@constant Z p) (@constant Z q)) == ffalse

 | IMP_IntAndT: forall p q: term boolT unit,
   pi1 o (pair p q) == ttrue -> pi2 o (pair p q) == ttrue -> andB o (pair p q) == ttrue
 | IMP_IntAndF: forall p q: term boolT unit,
   pi1 o (pair p q) == ffalse \/ pi2 o (pair p q) == ffalse -> andB o (pair p q) == ffalse

 | IMP_IntOrF: forall p q: term boolT unit,
   pi1 o (pair p q) == ffalse -> pi2 o (pair p q) == ffalse -> orB o (pair p q) == ffalse
 | IMP_IntOrT: forall p q: term boolT unit,
   pi1 o (pair p q) == ttrue \/ pi2 o (pair p q) == ttrue -> orB o (pair p q) == ttrue

 | IMP_Loop: forall (b: term boolT unit) (f w: term unit unit),
   w == (copair (w o f) id) o b

 | strong_sym: forall X Y, Symmetric (@strong X Y)
 | strong_trans: forall X Y, Transitive (@strong X Y)
 with weak: forall X Y, relation (term X Y) := 
 | weak_subs: forall X Y Z (g1 g2: term X Y) (f: term Y Z), g1 ~~ g2 -> g1 o f ~~ g2 o f
 | zero_weak_repl: forall X Y Z (g: term X Y) (f1 f2: term Y Z),
   is pure g -> f1 ~~ f2 -> g o f1 ~~ g o f2

 | weak_final_unique: forall X (f g: term unit X), f ~~ g	

 | axiom_1: forall i, lookup i o update i ~~ (@id Z)
 | axiom_2: forall i j, i<>j -> lookup j o update i ~~ lookup j o (@forget Z)
 | strong_to_weak: forall  X Y (f g: term X Y), f == g -> f ~~ g

 | weak_proj_pi1_rorw: forall X Y' Y (f1: term Y X) (f2: term Y' X), 
   is ro f1 -> (@pi1 Y Y') o pair f1 f2 ~~ f1

 | unicity: forall  X Y Y'(f g: term (Y/*/Y') X),
   ((@pi1 Y Y') o f ~~ (@pi1 Y Y') o g) -> ((@pi2 Y Y') o f ~~ (@pi2 Y Y') o g) -> f ~~ g

 | weak_sym: forall X Y, Symmetric (@weak X Y)
 | weak_trans: forall X Y, Transitive (@weak X Y)

   where "x == y" := (strong x y)
   and "x ~~ y" := (weak x y).

 Instance strong_is_equivalence X Y: Equivalence (@strong X Y).
 Proof.
     constructor.
     intro. apply strong_refl.
     intro. apply strong_sym.
     intro. apply strong_trans.
 Qed.

 Instance weak_is_equivalence X Y: Equivalence (@weak X Y).
 Proof.
     constructor.
     intro. apply strong_to_weak. apply strong_refl.
     intro. apply weak_sym.
     intro. apply weak_trans.
 Qed.

 Instance strong_is_weak_equivalence: forall X Y, subrelation (@strong X Y) (@weak X Y).
 Proof.
     constructor. assumption.
 Qed.

End Make.
