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
        Derived_Products Derived_Rules Proofs.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.
Require Import Bool.

Module Make(Import M: Memory.T).
  Module Export IMP_to_COQExp := Proofs.Make(M).

 Inductive Exp : Type -> Type :=
    | const    : forall A, A -> Exp A
    | loc      : Loc -> Exp Z
    | apply    : forall A B, (A -> B) -> Exp A -> Exp B
    | pairExp  : forall A B, Exp A    -> Exp B -> Exp (A * B).


 Fixpoint defExp A (e: Exp A): term A unit :=
  match e with
    | const Z n        => constant n
    | loc x            => lookup x
    | apply _ _ f x    => tpure f o (defExp x)
    | pairExp _ _  x y => pair (defExp x) (defExp y)
  end.

 Inductive Command : Type :=
    | skip       : Command
    | sequence   : Command  -> Command -> Command
    | assign     : Loc      -> Exp Z   -> Command 
    | ifthenelse : Exp bool -> Command -> Command -> Command
    | loops      : Exp bool -> Command -> Command.

 Fixpoint defCommand (c: Command): (term unit unit) :=
  match c with
    | skip                => (@id unit)
    | sequence c0 c1      => (defCommand c1) o (defCommand c0)
    | assign j e0         => (update j) o (defExp e0)
    | ifthenelse b c2 c3  => copair (defCommand c2) (defCommand c3) 
                              o (passbool o (defExp b))
    | loops b c4          => (copair (loopdec (passbool o (defExp b)) (defCommand c4) 
			      o (defCommand c4)) (@id unit)) o (passbool o (defExp b))
  end.

 Eval simpl in apply chkgt (pairExp (const 30) (const 40)).
 Eval simpl in  defExp(apply add (pairExp (const 30) (const 40))).
 Eval simpl in  defExp(apply chkgt (pairExp (const 30) (const 40))).

 Notation "j '::=' e0" := (assign j e0) (at level 60).
 Notation "c1 ';;' c2" := (sequence c1 c2) (at level 60).
 Notation "'SKIP'" := (skip) (at level 60).
 Notation "'IFB' b 'THEN' t1 'ELSE' t2 'ENDIF'" := (ifthenelse b t1 t2) (at level 60).
 Notation "'WHILE' b 'DO' c 'ENDWHILE'" := (loops b c) (at level 60).
 Notation " x '+++' y" :=  (apply add (pairExp x y)) (at level 60).
 Notation " x '***' y" := (apply mlt (pairExp x y)) (at level 60).
 Notation " x '>>' y" := (apply chkgt (pairExp x y)) (at level 60).
 Notation " x '>>=' y" := (apply chkge (pairExp x y)) (at level 60).
 Notation " x '<<' y" := (apply chklt (pairExp x y)) (at level 60).
 Notation " x '<<=' y" := (apply chkle (pairExp x y)) (at level 60).
 Notation " x '?==' y" := (apply chkeq (pairExp x y)) (at level 60).
 Notation " x '?&' y" := (apply ve (pairExp x y)) (at level 60).
 Notation " x '?|' y" := (apply yada (pairExp x y)) (at level 60). 
 Notation "'{{' c '}}'" := (defCommand c) (at level 60).
 Notation "'``' c '``'" := (defExp c) (at level 60).

(* -------------------- End of IMP to COQ conversion -------------------- *)

End Make.


