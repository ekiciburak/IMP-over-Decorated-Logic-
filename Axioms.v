
(**************************************************************************)
(*  This is part of STATES, it is distributed under the terms of the      *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2014: Jean-Guillaume Dumas, Dominique Duval            *)
(*             Burak Ekici, Damien Pous.                                  *)
(**************************************************************************)

Require Import Relations Morphisms.
Require Import Program.
Require Memory Terms Decorations Derived_Terms.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.
Require Import Bool.

Module Make(Import M: Memory.T).
  Module Export AxiomsExp := Derived_Terms.Make(M).

 Reserved Notation "x == y" (at level 80).
 Reserved Notation "x ~~ y" (at level 80).

 Inductive strong: forall X Y, relation (term X Y) :=
 | strong_refl: forall X Y (f: term X Y), f == f
 | assoc: forall X Y Z T (f: term X Y) (g: term Y Z) (h: term Z T),
   f o (g o h) == (f o g) o h
 | id_src: forall X Y (f: term X Y), f o id == f
 | id_tgt: forall X Y (f: term X Y), id o f == f

 | sc: forall X Y Z, Proper (@strong X Y ==> @strong Y Z ==> @strong X Z) comp

 | one_weak_to_strong: forall X Y (f g: term X Y), is ro f -> is ro g -> f ~~ g -> f == g

 | pure_pure: forall X Y Z (f: Y -> Z) (g: X -> Y),
   tpure f o tpure g  == tpure (fun x => f (g x))

 | pure_eq: forall X Y (f g: Y -> X),
   (forall x, f x = g x) -> tpure f == tpure g

 | strong_proj_pi2_rorw: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is ro f1 -> pi2 o pair f1 f2 == f2

 | observation: forall X (f g: term unit X),
   (forall i: Loc, lookup i o f ~~ lookup i o g) -> f == g

 | comp_final_unique: forall X Y (f g: term Y X),
   forget o f == forget o g -> f ~~ g -> f == g
	
 | strong_coproj_copi1_rwrw: forall X Y' Y (f1: term X Y) (f2: term X Y'),
   copair f1 f2 o (@copi1 Y Y') == f1 

 | strong_coproj_copi2_rwrw: forall X Y' Y (f1: term X Y) (f2: term X Y'),
   copair f1 f2 o (@copi2 Y Y') == f2 

 | counicity: forall  X Y Y'(f g: term X (Y+Y')),
   (f o (@copi1 Y Y') ~~ g o (@copi1 Y Y')) -> (f o (@copi2 Y Y') ~~ g o (@copi2 Y Y')) -> f == g

 (* IMP Assumptions *)

 | IMP_IntAdd: forall p q: Z,
   tpure add o (pair (@constant Z p) (@constant Z q)) == (constant (add(p,q)))
 | IMP_IntMult: forall p q: Z,
   tpure mlt o (pair (@constant Z p) (@constant Z q)) == (constant (mlt(p,q)))

 | IMP_IntGtT: forall p q: Z,
   Is_true(chkgt(p, q)) -> passbool  o tpure chkgt o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntGeT: forall p q: Z,
    Is_true(chkge(p, q)) ->  passbool o tpure chkge o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntEqT: forall p q: Z,
   Is_true(chkeq(p, q)) -> passbool  o tpure chkeq o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntNeqT: forall p q: Z,
   Is_true(chkneq(p, q)) -> passbool  o tpure chkneq o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntLtT: forall p q: Z,
   Is_true(chklt(p, q)) -> passbool o tpure chklt o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntLeT: forall p q: Z,
   Is_true(chkle(p, q)) -> passbool o tpure chkle o (pair (@constant Z p) (@constant Z q)) == ttrue

 | IMP_IntGtF: forall p q: Z,
   Is_true(chkle(p, q)) -> passbool  o tpure chkgt o (pair (@constant Z p) (@constant Z q)) == ffalse

 | IMP_IntGeF: forall p q: Z,
   Is_true(chklt(p, q)) -> passbool  o tpure chkge o (pair (@constant Z p) (@constant Z q)) == ffalse
 | IMP_IntEqF: forall p q: Z,
   Is_true(chkneq(p, q)) -> passbool  o tpure chkeq o (pair (@constant Z p) (@constant Z q)) == ffalse
 | IMP_IntNeqF: forall p q: Z,
   Is_true(chkeq(p, q)) -> passbool  o tpure chkneq o (pair (@constant Z p) (@constant Z q)) == ffalse
 | IMP_IntLtF: forall p q: Z,
   Is_true(chkge(p, q)) -> passbool o tpure chklt o (pair (@constant Z p) (@constant Z q)) == ffalse

 | IMP_IntLeF: forall p q: Z,
   Is_true(chkgt(p, q)) -> passbool o tpure chkle o (pair (@constant Z p) (@constant Z q)) == ffalse

 | IMP_IntAndT: forall p q: bool,
   p = true -> q = true -> passbool  o tpure ve o (pair (@constant bool p) (@constant bool q)) == ttrue
 | IMP_IntAndF: forall p q: bool,
   p = false \/ q = false -> passbool  o tpure ve o (pair (@constant bool p) (@constant bool q)) == ffalse

 | IMP_IntOrF: forall p q: bool,
   p = false -> q = false -> passbool  o tpure yada o (pair (@constant bool p) (@constant bool q)) == ffalse
 | IMP_IntOrT: forall p q: bool,
   p = true \/ q = true -> passbool  o tpure yada o (pair (@constant bool p) (@constant bool q)) == ttrue 

 | IMP_Loop: forall (b: term (unit+unit) unit) (f : term unit unit),
   loopdec b f == (copair ((loopdec b f) o f) id) o b 

 (* \IMP Assumptions *)

 | strong_sym: forall X Y, Symmetric (@strong X Y)
 | strong_trans: forall X Y, Transitive (@strong X Y)
 with weak: forall X Y, relation (term X Y) :=
 | wsc: forall A B C,
               Proper (@weak C B ==> @strong  B A ==> @weak C A) comp
 | wrc: forall A B C (g: term C B), (PURE g) ->
               Proper (@weak B A ==> @weak C A) (comp g)

 | weak_final_unique: forall X (f g: term unit X), f ~~ g    

 | axiom_1: forall i, lookup i o update i ~~ id
 | axiom_2: forall i j, i<>j -> lookup j o update i ~~ lookup j o forget
 | strong_to_weak: forall  X Y (f g: term X Y), f == g -> f ~~ g

 | weak_proj_pi1_rorw: forall X Y' Y (f1: term Y X) (f2: term Y' X),
   is ro f1 -> pi1 o pair f1 f2 ~~ f1

 | unicity: forall  X Y Y'(f g: term (Y*Y') X),
   pi1 o f ~~ pi1 o g -> pi2 o f ~~ pi2 o g -> f ~~ g

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
 Proof. constructor. assumption. Qed.

 Existing Instance wsc.
 Existing Instance wrc.
 Existing Instance sc.

 Ltac catpr :=
   match goal with
      | H: _ |-  pi1 o pair ?f1 ?f2 ~~ ?f1
        => apply weak_proj_pi1_rorw; decorate
      | H: _ |-  pi2 o pair ?f1 ?f2 == ?f2
        => apply strong_proj_pi2_rorw; decorate
      | H: _ |-  pi1 o prod ?f ?g ~~ ?f o pi1
        => apply weak_proj_pi1_rorw; decorate
      | H: _ |-  pi2 o prod ?f ?g == ?g o pi2
        => apply strong_proj_pi2_rorw; decorate
   end. 
 
End Make.


(*

	(* IMP *)

 | IMP_IntGtT: forall p q: Z,
   (p > q) -> gt o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntGeT: forall p q: Z,
   (p > q) \/ (p = q) -> ge o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntEqT: forall p q: Z,
   (p = q) -> eq o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntNeqT: forall p q: Z,
   (p <> q) -> neq o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntLtT: forall p q: Z,
   (p < q) -> lt o (pair (@constant Z p) (@constant Z q)) == ttrue
 | IMP_IntLeT: forall p q: Z,
   (p < q) \/ (p = q) -> le o (pair (@constant Z p) (@constant Z q)) == ttrue

 | IMP_IntGtF: forall p q: Z,
   (p < q) \/ (p = q) -> gt o (pair (@constant Z p) (@constant Z q)) == ffalse

 | IMP_IntGeF: forall p q: Z,
   (p < q) -> ge o (pair (@constant Z p) (@constant Z q)) == ffalse
 | IMP_IntEqF: forall p q: Z,
   (p <> q) -> eq o (pair (@constant Z p) (@constant Z q)) == ffalse
 | IMP_IntNeqF: forall p q: Z,
   (p = q) -> neq o (pair (@constant Z p) (@constant Z q)) == ffalse
 | IMP_IntLtF: forall p q: Z,
   (p > q) \/ (p = q) -> lt o (pair (@constant Z p) (@constant Z q)) == ffalse

 | IMP_IntLeF: forall p q: Z,
   (p > q) -> le o (pair (@constant Z p) (@constant Z q)) == ffalse
 | IMP_IntAndT: forall p q: term boolT unit,
   pi1 o (pair p q) == ttrue -> pi2 o (pair p q) == ttrue -> andB o (pair p q) == ttrue
 | IMP_IntAndF: forall p q: term boolT unit,
   pi1 o (pair p q) == ffalse \/ pi2 o (pair p q) == ffalse -> andB o (pair p q) == ffalse

 | IMP_IntOrF: forall p q: term boolT unit,
   pi1 o (pair p q) == ffalse -> pi2 o (pair p q) == ffalse -> orB o (pair p q) == ffalse
 | IMP_IntOrT: forall p q: term boolT unit,
   pi1 o (pair p q) == ttrue \/ pi2 o (pair p q) == ttrue -> orB o (pair p q) == ttrue

 | IMP_Loop: forall (b: term boolT unit) (f : term unit unit),
   loopdec b f == (copair ((loopdec b f) o f) id) o b
   
	(* End IMP *)

*)

