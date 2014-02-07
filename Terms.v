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
Require Memory.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.

Module Make(Import M: Memory.T).

 Variable coproductT: Type -> Type -> Type.
 Notation "y '/+/' z" := (coproductT y z) (at level 70).

 Variable productT: Type -> Type -> Type.
 Notation "y '/*/' z" := (productT y z) (at level 70).

 Definition boolT: Type := (unit/+/unit).

 Inductive term: Type -> Type -> Type :=
  | id: forall {X}, term X X
  | comp: forall {X Y Z}, term X Y -> term Y Z -> term X Z
  | downcast: forall {X Y} (f: term X Y), term X Y 
  | forget: forall {X}, term unit X
  | empty: forall {X}, term X empty_set
  | pair: forall {X Y Z}, term X Z -> term Y Z -> term (X/*/Y) Z
  | copair: forall {X Y Z}, term Z X -> term Z Y -> term Z (X/+/Y) 	
  | pi1: forall {X Y}, term X (X/*/Y)
  | pi2: forall {X Y}, term Y (X/*/Y)
  | copi1: forall {X Y}, term (X/+/Y) X
  | copi2: forall {X Y}, term (X/+/Y) Y
  | loopdec: term unit unit
  | plus: forall {X}, term X (X/*/X) 
  | mult: forall {X}, term X (X/*/X)	
  | gt: term boolT (Z/*/Z)
  | lt: term boolT (Z/*/Z)
  | ge: term boolT (Z/*/Z)
  | le: term boolT (Z/*/Z)
  | eq: term boolT (Z/*/Z)
  | andB: term boolT (boolT/*/boolT)
  | orB: term boolT (boolT/*/boolT)
  | constant: forall (X: Set), X -> term X unit 
  | lookup: Loc -> term Z unit
  | update: Loc -> term unit Z
  | tag: EName -> term empty_set unit	
  | untag: EName -> term unit empty_set.

 Infix "o" := comp (at level 70).



End Make.
