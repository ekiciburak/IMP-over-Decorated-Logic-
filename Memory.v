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
Require Import Le Gt Minus Bool Setoid.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.

Module Type T.
 Parameter Loc: Type.
 Parameter Val: Loc -> Type.
 Parameter Loc_dec: forall i j: Loc, {i=j}+{i<>j}.

 Parameter EName: Type.
 Parameter EVal: EName -> Type.
 Parameter Exc_dec: forall i j: EName, {i=j}+{i<>j}.

 Parameter empty_set: Set.

End T.

