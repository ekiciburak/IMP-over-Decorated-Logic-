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
Require Memory Terms Decorations.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.
Require Import Bool.

Module Make(Import M: Memory.T).
  Module Export Derived_TermsExp := Decorations.Make(M).

 Definition id  {X: Type}     : term X X       := tpure id.
 Definition pi1 {X Y: Type}   : term X (X*Y)   := tpure fst. 
 Definition pi2 {X Y: Type}   : term Y (X*Y)   := tpure snd.
 Definition forget {X}        : term unit X    := tpure (fun _ => tt).
(* Definition constant (v: Z)   : term Z unit    := tpure (fun _ => v).
   Definition constant {X Y: Type} (v: Y): term Y X := tpure (fun _ => v). *)

 Definition loopdec (b: term (unit+unit) unit) (f: term unit unit) : term unit unit  
    := tpure(fun tt => tt).

 Definition copi1 {X Y}       : term (X+Y) X  := tpure inl.
 Definition copi2 {X Y}       : term (X+Y) Y  := tpure inr. 
 Definition empty {X} (x: X)  : term X empty_set:= tpure (fun _ => x).
 Definition constant {X: Type} (v: X): term X unit := tpure (fun _ => v). 

 Definition add (p: Z * Z) := match p with
                                | (x, y) => x + y
                              end.

 Definition mlt (p: Z * Z) := match p with
                                | (x, y) => x * y
                              end.


 Definition chkgt (p: Z * Z) : bool := match p with
                                              | (a1, a2) => match (a1 ?= a2)%Z with 
                                                              | Gt => true
                                                              | _  => false
                                                            end
                                            end.



 Definition chkge (p: Z * Z) : bool := match p with
                                              | (a1, a2) => match (a1 ?= a2)%Z with 
                                                              | Lt => false
                                                              | _  => true
                                                           end
                                            end.

 Definition chklt (p: Z * Z) : bool := match p with
                                              | (a1, a2) => match (a1 ?= a2)%Z with 
                                                              | Lt => true
                                                              | _  => false
                                                            end
                                            end.

 Definition chkle (p: Z * Z) : bool := match p with
                                              | (a1, a2) => match (a1 ?= a2)%Z with 
                                                              | Gt => false
                                                              | _  => true
                                                            end
                                            end.

 Definition chkeq (p: Z * Z) : bool := match p with
                                              | (a1, a2) => match (a1 ?= a2)%Z with 
                                                              | Eq => true
                                                              | _  => false
                                                            end
                                            end.

 Definition chkneq (p: Z * Z) : bool := match p with
                                               | (a1, a2) => match (a1 ?= a2)%Z with 
                                                               | Eq => false
                                                               | _  => true
                                                             end
                                             end.

 Definition ve (p: bool * bool): bool := match p with
                                                | (x, y) => match (x && y) with 
                                                               | false => false
                                                               | true  => true
                                                             end
                                              end.

 Definition yada (p: bool * bool): bool := match p with
                                                  | (x, y) => match (x || y) with 
                                                                | false => false
                                                                | true  => true
                                                              end
                                                end.

 Definition bool_to_two (b: bool): unit + unit :=
    match b with
       | false => inr tt
       | true  => inl tt
    end.

 Definition bool_to_prop (b: bool): Prop :=
     match b with
       | false => False
       | true  => True
    end.

 Check tt.

 Definition passbool: term (unit + unit) bool := tpure bool_to_two.
 
 Definition prod_forget {X Y}: term unit (X*Y) := forget.
 Definition iso {X}: term (X*unit) X := pair id forget. 
 Definition inv_pi1 {X}: term (X*unit) X := pair id forget. 
 Definition permut {X Y}: term (X*Y) (Y*X) := pair pi2 pi1.
 
 Definition perm_pair {X Y Z} (f: term Y X) (g: term Z X): term (Y*Z) X
 := permut o pair g f.
 Definition prod {X Y X' Y'} (f: term X X') (g: term Y Y'): term (X*Y) (X'*Y')
 := pair (f o pi1) (g o pi2).
 Definition perm_prod {X Y X' Y'} (f: term X X') (g: term Y Y') := permut o pair (g o pi2) (f o pi1).
 (*Definition perm_prod {X Y X' Y'} (f: term X X') (g: term Y Y'): term (X*Y) (X'*Y')
 := perm_pair (f o pi1) (g o pi2).*)

 Definition ttrue  : term (unit+unit) unit := copi1.
 Definition ffalse : term (unit+unit) unit := copi2.

 Lemma is_loopdec: forall k (b: term (unit+unit) unit) (f: term unit unit),
 is k b -> is k f -> is pure (loopdec b f).
 Proof. intros. decorate. Qed.

 Lemma is_prod_forget X Y: is pure (@prod_forget X Y).
 Proof. decorate. Qed.

 Lemma is_inv_pi1 X: is pure (@inv_pi1 X).
 Proof. decorate. Qed.
 
 Lemma is_permut X Y: is pure (@permut X Y).
 Proof. decorate. Qed.

 Lemma is_perm_pair: forall k X Y Z (f: term Y X) (g: term Z X),
 is k f -> is k g -> is k (perm_pair f g).
 Proof. intros. induction k; decorate. Qed.

 Lemma is_prod: forall k X' X Y' Y (f: term X X') (g: term Y Y'), 
 is k f -> is k g -> is k (prod f g).
 Proof. intros. induction k; decorate. Qed. 

 Lemma is_perm_prod: forall k X' X Y' Y (f: term X X') (g: term Y Y'), 
 is k f -> is k g -> is k (perm_prod f g).
 Proof. intros. induction k; decorate. Qed.

 Lemma is_ttrue: is pure (@copi1 unit unit).
 Proof. decorate. Qed.

 Lemma is_ffalse: is pure (@copi2 unit unit).
 Proof. decorate. Qed.

 Lemma is_id X: is pure (@id X).
 Proof. decorate. Qed.

 Lemma is_pi1 X Y: is pure (@pi1 X Y).
 Proof. decorate. Qed.

 Lemma is_pi2 X Y: is pure (@pi2 X Y).
 Proof. decorate. Qed.

 Lemma is_forget X: is pure (@forget X).
 Proof. apply is_tpure. Qed.

 Lemma is_constant (v: Z): is pure (constant v).
 Proof. apply is_tpure. Qed.

 Lemma is_copi1 X Y: is pure (@copi1 X Y).
 Proof. decorate. Qed.

 Lemma is_copi2 X Y: is pure (@copi2 X Y).
 Proof. decorate. Qed.

 Lemma is_empty {X: Type} (x: X): is pure (@empty X x).
 Proof. decorate. Qed.

(* Lemma is_plus: is pure (plus).
 Proof. decorate. Qed.

 Lemma is_mult: is pure (mult).
 Proof. decorate. Qed.

 Lemma is_gt: is pure (gt).
 Proof. decorate. Qed.

 Lemma is_ge: is pure (ge).
 Proof. decorate. Qed.

 Lemma is_lt: is pure (lt).
 Proof. decorate. Qed.

 Lemma is_le: is pure (le).
 Proof. decorate. Qed.

 Lemma is_eq: is pure (eq).
 Proof. decorate. Qed.

 Lemma is_neq: is pure (neq).
 Proof. decorate. Qed.

 Lemma is_and: is pure (and).
 Proof. decorate. Qed.

 Lemma is_or: is pure (or).
 Proof. decorate. Qed. *)

 Lemma is_passbool: is pure (passbool).
 Proof. decorate. Qed.

End Make.
