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
Require Memory Terms Decorations.
Set Implicit Arguments.

Module Make(Import M: Memory.T).
  Module Export Derived_TermsExp := Decorations.Make(M). 

 (*For states*)

 Definition ttrue:  term boolT unit := (@copi1 unit unit).
 Definition ffalse: term boolT unit := (@copi2 unit unit). 

 Lemma is_ttrue: is pure (@copi1 unit unit).
 Proof. auto. Qed.

 Lemma is_ffalse: is pure (@copi2 unit unit).
 Proof. auto. Qed.
 
End Make.
