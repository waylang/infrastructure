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

Require Import Way.Tactics.

Require Import Way.List.
Require Import Way.Nat.

Require Export Way.Atom.

(*
Preterms are structurally identical to terms, but lack proofs of needed invariants.

The "locally nameless" pattern is used to manage variables.  This means that bound
variables are given de Bruijn indices instead of names.  This eliminates the need for
alpha conversion, but opens the possibility that bound variable indices may be invalid
(that is, may refer to abstractions which do not exist).  "Local closure" is the property
that all such indices are valid, see below.
*)
Inductive preterm : Set :=

(* A named variable in an open term *)
| free_variable : atom -> preterm

(* A nameless variable (a de Bruijn index over all binders) *)
| bound_variable : nat -> preterm

(* Introduce a lambda *)
| abstraction : preterm -> preterm

(* Introduce a dependent product *)
| product : preterm -> preterm

(* Eliminate an abstraction *)
| application : preterm -> preterm -> preterm

(* Eliminate a product *)
| product_application : preterm -> preterm -> preterm

(* The hierarchy of type universes *)
| type : nat -> preterm.

Module Aliases.

Definition fvar := free_variable.
Definition bvar := bound_variable.
Definition abs := abstraction.
Definition prod := product.
Definition app := application.
Definition papp := product_application.

End Aliases.

Module PretermExamples.

Include Aliases.

Example omega :=
  (app
    (abs (app (bvar 0) (bvar 0)))
    (abs (app (bvar 0) (bvar 0)))).

(* It looks strange without its typing annotations, but here it is *)
Example polymorphic_identity := (prod (abs (bvar 0))).

End PretermExamples.

Module LocalClosure.

(* Replace a bound variable i with replacement u in preterm p *)
Fixpoint substitute_bound (i : nat) (u p : preterm) : preterm :=
  match p with
  | free_variable _ => p
  | bound_variable b => if eq_nat_dec i b then u else p
  | abstraction b => (abstraction (substitute_bound (S i) u b))
  | product b => (product (substitute_bound (S i) u b))
  | application f a =>
      application (substitute_bound i u f) (substitute_bound i u a)
  | product_application f a =>
      product_application (substitute_bound i u f) (substitute_bound i u a)
  | type _ => p
  end.

Module SubstituteBoundExamples.

Include Aliases.

Example fvar_is_unchanged :
  forall (a b : atom), substitute_bound 0 (fvar a) (fvar b) = (fvar b).
Proof.
  infer.
Defined.

Example bvar_is_substituted :
  forall (a : atom), substitute_bound 0 (fvar a) (bvar 0) = (fvar a).
Proof.
  infer.
Defined.

Example wrong_bvar_is_unchanged :
  forall (a : atom), substitute_bound 0 (fvar a) (bvar 1) = (bvar 1).
Proof.
  infer.
Defined.

Example abs_substitutes_incremented_bvar :
  forall (a : atom), substitute_bound 0 (fvar a) (abs (bvar 1)) = (abs (fvar a)).
Proof.
  infer.
Defined.

Example prod_substitutes_incremented_bvar :
  forall (a : atom), substitute_bound 0 (fvar a) (prod (bvar 1)) = (prod (fvar a)).
Proof.
  infer.
Defined.

Example app_substitutes_into_subterms :
  forall (a : atom), substitute_bound 0 (fvar a)
    (app (bvar 0) (bvar 0)) = (app (fvar a) (fvar a)).
Proof.
  infer.
Defined.

Example papp_substitutes_into_subterms :
  forall (a : atom), substitute_bound 0 (fvar a)
    (papp (bvar 0) (bvar 0)) = (papp (fvar a) (fvar a)).
Proof.
  infer.
Defined.

Example type_is_unchanged :
  forall (a : atom) (n : nat), substitute_bound 0 (fvar a) (type n) = (type n).
Proof.
  infer.
Defined.

End SubstituteBoundExamples.

(*
A preterm is locally closed if every bound variable refers to some abstraction.

A proof of local closure reflects the shape of its preterm, with two key differences.

First, we transform abstraction bodies before demanding local closure of the result.  The
transformation is to substitute a "sufficiently fresh" free variable for the new bound
variable. This bound variable will therefore not appear in the preterm of the required
subproof.

Second, there is no local closure constructor for bound variables.

If all bound variables properly refer to some abstraction, then by the first point they
will all be replaced by free variables by the time we consider the proof of their local
closure.  Any bound variables that remain must be dangling.

By the second point, preterms with such bound variables will be unable to prove local
closure, due to the lack of a suitable constructor.  On the other hand, preterms without
dangling bound variables will have no need of one.

"Sufficiently fresh" means exclusion from an arbitrary list of free variables, but think
"free variables of the abstraction body".  Leaving it unspecified here makes proofs
somewhat easier later, per the "cofinite induction" pattern.
*)
Inductive locally_closed : preterm -> Type :=

| free_variable : forall (a : atom), locally_closed (free_variable a)

| abstraction : forall (stale : list atom) (b : preterm),
  (forall (a : atom), ~ has a stale ->
    locally_closed (substitute_bound 0 (free_variable a) b)) ->
  locally_closed (abstraction b)

| product : forall (stale : list atom) (b : preterm),
  (forall (a : atom), ~ has a stale ->
    locally_closed (substitute_bound 0 (free_variable a) b)) ->
  locally_closed (product b)

| application : forall (p q : preterm), locally_closed p -> locally_closed q ->
  locally_closed (application p q)

| product_application : forall (p q : preterm), locally_closed p -> locally_closed q ->
  locally_closed (product_application p q)

| type : forall (n : nat), locally_closed (type n).

Module Examples.

Include Aliases.

Example omega :
  locally_closed (app (abs (app (bvar 0) (bvar 0))) (abs (app (bvar 0) (bvar 0)))).
Proof.
  (* TODO(phs): infer search depth/order *)
  apply application;
  infer from application (abstraction []) free_variable.
Defined.

Example polymorphic_identity : locally_closed (prod (abs (bvar 0))).
Proof.
  (* TODO(phs): infer search depth/order *)
  apply (product []);
  intros; simpl; destruct (eq_nat_dec 1 0); try congruence;
  infer from (product []) (abstraction []) free_variable.
Defined.

Example fvar_is_locally_closed : forall (a : atom), locally_closed (fvar a).
Proof.
  apply free_variable.
Defined.

Example abs_can_be_locally_closed : locally_closed (abs (bvar 0)).
Proof.
  infer from (abstraction []) free_variable.
Defined.

Example abs_can_be_not_locally_closed : notT (locally_closed (abs (bvar 1))).
Proof.
  intro H;
  inversion H as [ | stale ? CFH | | | | ];
  subst;
  destruct (fresh_atom stale) as [a Hfresh];
  pose proof (CFH a Hfresh) as Himpossible;
  infer.
Defined.

Example prod_can_be_locally_closed : locally_closed (prod (bvar 0)).
Proof.
  infer from (product []) free_variable.
Defined.

Example prod_can_be_not_locally_closed : notT (locally_closed (prod (bvar 1))).
Proof.
  intro H;
  inversion H as [ | | stale ? CFH | | | ];
  subst;
  destruct (fresh_atom stale) as [a Hfresh];
  pose proof (CFH a Hfresh) as Himpossible;
  infer.
Defined.

Example app_can_be_locally_closed :
  forall (a : atom), locally_closed (app (fvar a) (fvar a)).
Proof.
  infer from application free_variable.
Defined.

Example app_can_be_not_locally_closed : notT (locally_closed (app (bvar 0) (bvar 0))).
Proof.
  (* TODO(phs): Explicit unfold should be unnecessary. *)
  unfold notT;
  infer from application.
Defined.

Example papp_can_be_locally_closed :
  forall (a : atom), locally_closed (papp (fvar a) (fvar a)).
Proof.
  infer from product_application free_variable.
Defined.

Example papp_can_be_not_locally_closed : notT (locally_closed (papp (bvar 0) (bvar 0))).
Proof.
  (* TODO(phs): Explicit unfold should be unnecessary. *)
  unfold notT;
  infer from product_application.
Defined.

Example type_is_locally_closed : locally_closed (Term.type 0).
Proof.
  infer from type.
Defined.

End Examples.

End LocalClosure.

Definition locally_closed := LocalClosure.locally_closed.

(* A term is a locally closed preterm. *)
Definition term := { p : preterm & locally_closed p }.

Module Examples.

Definition preterm_omega := PretermExamples.omega.
Definition omega_locally_closed := LocalClosure.Examples.omega.

Example omega : term := existT locally_closed preterm_omega omega_locally_closed.

End Examples.
