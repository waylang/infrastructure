(*
  vim: filetype=coq
*)
(*
Copyright (C) 2016-2017 Philip H. Smith

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
*)

Require Import Way.StaleAtoms.
Require Import Way.Tactics.

Require Import Way.Open.
Require Import Way.Preterm.

(* A preterm is locally closed if every bound variable refers to some abstraction.

Local closure is the only criterion needed to establish a preterm as a term, so the type
here is named "term".

A proof of local closure reflects the shape of its preterm, with two key differences.

First, we transform abstraction bodies before demanding local closure of the result.  The
transformation is to open a "sufficiently fresh" free variable for the new bound variable.
This bound variable will therefore not appear in the preterm of the required subproof.
Since abstraction annotations should not refer to the new abstraction variable, no
substitution is performed on them.

Second, there is no local closure constructor for bound variables.

If all bound variables properly refer to some abstraction, then by the first point they
will all be replaced by free variables by the time we consider the proof of their local
closure.  Any bound variables that remain must be dangling.

By the second point, preterms with dangling bound variables will be unable to prove local
closure, due to the lack of a suitable constructor.  Preterms without dangling bound
variables will have no need of one.

"Sufficiently fresh" means exclusion from an arbitrary list of free variables, but think
"free variables of the abstraction body".  Leaving it unspecified here makes proofs
somewhat easier later, per the "cofinite induction" pattern.
*)
Inductive term : preterm -> Set :=

| free_variable : forall (a : atom), term (free_variable a)

| product :
  forall (l : list atom) (p q : preterm), term p ->
  (fresh (a : l), term (open_free a q)) ->
  term (product p q)

| abstraction :
  forall (l : list atom) (p q : preterm), term p ->
  (fresh (a : l), term (open_free a q)) ->
  term (abstraction p q)

| application : forall (p q : preterm), term p -> term q -> term (application p q)

| type : forall (n : nat), term (type n).

Hint Resolve free_variable application type : way.

Hint Extern 7 (term (Preterm.product _ _)) =>
  let stale := stale_atoms in apply (Term.product stale) : way.

Hint Extern 7 (term (Preterm.abstraction _ _)) =>
  let stale := stale_atoms in apply (Term.abstraction stale) : way.

Module Examples.

Import Aliases.

Example omega : term Preterm.Examples.omega.
Proof.
  unfold Preterm.Examples.omega; infer.
Defined.

Example polymorphic_identity : term (prod (type 0) (abs (bvar 0) (bvar 0))).
Proof.
  infer.
Defined.

Example fvar_is_term : forall (a : atom), term (fvar a).
Proof.
  infer.
Defined.

Example prod_can_be_term : term (prod (type 0) (bvar 0)).
Proof.
  infer.
Defined.

Example prod_can_be_not_term : notT (term (prod (type 0) (bvar 1))).
Proof.
  intro H;
  inversion H as [ | stale ? ? ? CFH | | | ];
  subst;
  destruct (fresh_atom stale) as [a Hfresh];
  pose proof (CFH a Hfresh) as Himpossible;
  infer.
Defined.

Example abs_can_be_term : term (abs (type 0) (bvar 0)).
Proof.
  infer.
Defined.

Example abs_can_be_not_term : notT (term (abs (type 0) (bvar 1))).
Proof.
  intro H;
  inversion H as [ | | stale ? ? ? CFH | | ];
  subst;
  destruct (fresh_atom stale) as [a Hfresh];
  pose proof (CFH a Hfresh) as Himpossible;
  infer.
Defined.

Example app_can_be_term : forall (a : atom), term (app (fvar a) (fvar a)).
Proof.
  infer.
Defined.

Example app_can_be_not_term : notT (term (app (bvar 0) (bvar 0))).
Proof.
  infer.
Defined.

Example type_is_term : term (type 0).
Proof.
  infer.
Defined.

End Examples.
