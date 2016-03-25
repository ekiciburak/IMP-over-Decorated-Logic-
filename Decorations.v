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
Require Memory Terms.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.

Module Make(Import M: Memory.T).
  Module Export DecorationsExp := Terms.Make(M). 

 Inductive kind := pure | ro | rw. 

Inductive is: kind -> forall X Y, term X Y -> Prop :=
 | is_id: forall X, is pure (@id X)
 | is_comp: forall k X Y Z (f: term X Y) (g: term Y Z), is k f -> is k g -> is k (f o g)
 | is_forget: forall X, is pure (@forget X)
 | is_pair: forall k X Y Z (f: term X Z) (g: term Y Z), is k f -> is k g -> is k (pair f g)
 | is_copair: forall k X Y Z (f: term Z X) (g: term Z Y), is k f -> is k g -> is k (copair f g) 
 | is_pi1: forall X Y, is pure (@pi1 X Y)
 | is_pi2: forall X Y, is pure (@pi2 X Y)
 | is_copi1: forall X Y, is pure (@copi1 X Y) 
 | is_copi2: forall X Y, is pure (@copi2 X Y)
 | is_plus: forall X, is pure (@plus X)
 | is_mult: forall X, is pure (@mult X)
 | is_gt: is pure gt
 | is_ge: is pure ge
 | is_lt: is pure lt
 | is_le: is pure le
 | is_eq: is pure eq
 | is_andB: is pure andB
 | is_orB: is pure orB
 | is_constant: forall X: Set, forall c: X, is pure (@constant X c)
 | is_lookup: forall i, is ro (lookup i)   
 | is_update: forall i, is rw (update i)
 | is_pure_ro: forall X Y (f: term X Y), is pure f -> is ro f
 | is_ro_rw: forall X Y  (f: term X Y), is ro f -> is rw f.

 Hint Constructors is.

End Make.
