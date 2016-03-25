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
Require Memory.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.
Require Import Bool.

Module Make(Import M: Memory.T).

 Inductive empty_set : Set :=.

 Inductive term: Type -> Type -> Type :=
  | comp:   forall {X Y Z: Type}, term X Y -> term Y Z -> term X Z
  | pair: forall {X Y Z: Type}, term X Z -> term Y Z -> term (X*Y) Z
  | copair: forall {X Y Z}, term Z X -> term Z Y -> term Z (X+Y) 
  | tpure:  forall {X Y: Type}, (X -> Y) -> term Y X
  | lookup: forall i:Loc, term Z unit    
  | update: forall i:Loc, term unit Z.

 Infix "o" := comp (at level 70).

End Make.

