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
Require Memory Terms Decorations Derived_Terms Axioms Derived_Rules.
Set Implicit Arguments.
Require Import ZArith.
Open Scope Z_scope.

Module Make(Import M: Memory.T).
  Module Export ConversionExp := Derived_Rules.Make(M).

 Inductive ArithExp : Type :=
    | const    : Z -> ArithExp
    | loc      : Loc -> ArithExp
    | add      : ArithExp -> ArithExp -> ArithExp
    | multiply : ArithExp -> ArithExp -> ArithExp.

 Fixpoint defArithExp (a: ArithExp) : term Z unit :=
  match a with
    | const n        => (@constant Z n)
    | loc x          => (lookup x)
    | add t1 t2      => plus o (pair (defArithExp t1) (defArithExp t2))
    | multiply t3 t4 => mult o (pair (defArithExp t3) (defArithExp t4))
  end.

 Inductive BoolExp : Type :=
    | constT  : term boolT unit -> BoolExp
    | constF  : term boolT unit -> BoolExp
    | gtT     : ArithExp -> ArithExp -> BoolExp
    | geT     : ArithExp -> ArithExp -> BoolExp
    | ltT     : ArithExp -> ArithExp -> BoolExp
    | leT     : ArithExp -> ArithExp -> BoolExp
    | eqT     : ArithExp -> ArithExp -> BoolExp
    | andT    : BoolExp -> BoolExp -> BoolExp
    | orT     : BoolExp -> BoolExp -> BoolExp.

 Fixpoint defBoolExp (b: BoolExp) : term boolT unit :=
  match b with
    | constT ttrue  => ttrue
    | constF ffalse => ffalse
    | gtT a1 a2     => (gt o (pair (defArithExp a1) (defArithExp a2)))
    | geT a1 a2     => (ge o (pair (defArithExp a1) (defArithExp a2)))
    | ltT a1 a2     => (lt o (pair (defArithExp a1) (defArithExp a2)))
    | leT a1 a2     => (le o (pair (defArithExp a1) (defArithExp a2)))
    | eqT a1 a2     => (eq o (pair (defArithExp a1) (defArithExp a2)))
    | andT b1 b2    => (andB o (pair (defBoolExp b1) (defBoolExp b2)))
    | orT b3 b4     => (orB o (pair (defBoolExp b3) (defBoolExp b4)))
  end.

 Inductive Command : Type :=
    | skip       : Command
    | sequence   : Command -> Command -> Command
    | assign     : Loc -> ArithExp -> Command 
    | ifthenelse : BoolExp -> Command -> Command -> Command
    | loops      : BoolExp -> Command -> Command.

 Fixpoint defCommand (c: Command): (term unit unit) :=
  match c with
    | skip                => (@id unit)
    | sequence c0 c1      => (defCommand c1) o (defCommand c0)
    | assign i e0         => (update i) o (defArithExp e0)
    | ifthenelse b c2 c3  => (copair (defCommand c2) (defCommand c3)) o (defBoolExp b)
    | loops b c4          => (copair (loopdec o defCommand c4) (@id unit)) o (defBoolExp b)
  end.

 Notation "x '::=' a" := (assign x a) (at level 60).
 Notation "c1 ';;' c2" := (sequence c1 c2) (at level 65).
 Notation "'SKIP'" := (skip) (at level 60).
 Notation "'IFB' b 'THEN' t1 'ELSE' t2 'ENDIF'" := (ifthenelse b t1 t2) (at level 60).
 Notation "'WHILE' b 'DO' c 'ENDWHILE'" := (loops b c) (at level 60).
 Notation " x '+++' y" := (add x y) (at level 60).
 Notation " x '***' y" := (multiply x y) (at level 60).
 Notation " x '>>' y" := (gtT x y) (at level 63).
 Notation " x '>>=' y" := (geT x y) (at level 63).
 Notation " x '<<' y" := (ltT x y) (at level 63).
 Notation " x '<<=' y" := (leT x y) (at level 63).
 Notation " x '===' y" := (eqT x y) (at level 63).
 Notation " x '&&&' y" := (andT x y) (at level 64).
 Notation " x '|||' y" := (orT x y) (at level 64).
 Notation "'{{' c '}}'" := (defCommand c) (at level 67).
 Notation "'``' c '``'" := (defBoolExp c) (at level 67).

(* -------------------- End of IMP to COQ conversion -------------------- *)

End Make.

