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
Require Import Way.Relation.
Require Import Way.Term.

(* Small-step beta reduction.

Beta reduction eliminates application-abstraction pairs, called beta redexes.  Beta
reduction is "full": to find redexes beta reduction looks within type annotations and
abstraction bodies, as well as applications.  In other words, beta redexes appearing in
either side of applications, abstractions and products may be reduced.

The possibility of computation within abstractions creates non-determinism, but see the
Church-Rosser property. It shows that no race conditions are present: all evaluation paths
eventually lead to the same term.
*)
Inductive beta : relation :=

(* Applications of abstractions beta reduce to opening the body with the argument.

The function must be a locally closed abstraction and the argument must be locally closed.
The equation involving open is required to allow proof search to match the head.
*)
| redex :
  forall (T u : preterm), term (Preterm.abstraction T u) ->
  forall (t : preterm), term t ->
  forall (v : preterm), v = open 0 t u ->
  beta (Preterm.application (Preterm.abstraction T u) t) v

(* Beta reduction descends into the function position of applications. *)
| application_function :
  forall (u : preterm), term u ->
  forall (t v : preterm), beta t v ->
  beta (Preterm.application t u) (Preterm.application v u)

(* Beta reduction descends into the argument position of applications. *)
| application_argument :
  forall (t : preterm), term t ->
  forall (u v : preterm), beta u v ->
  beta (Preterm.application t u) (Preterm.application t v)

(* Beta reduction descends into the annotation position of abstractions. *)
| abstraction_annotation :
  forall (l : list atom) (u : preterm), (fresh (a : l), term (open_free a u)) ->
  forall (t v : preterm), beta t v ->
  beta (Preterm.abstraction t u) (Preterm.abstraction v u)

(* Beta reduction descends into the body position of abstractions after opening. *)
| abstraction_body :
  forall (l : list atom) (t : preterm), term t ->
  forall (u v : preterm), (fresh (a : l), beta (open_free a u) (open_free a v)) ->
  beta (Preterm.abstraction t u) (Preterm.abstraction t v)

(* Beta reduction descends into the domain position of products. *)
| product_domain :
  forall (l : list atom) (u : preterm), (fresh (a : l), term (open_free a u)) ->
  forall (t v : preterm), beta t v ->
  beta (Preterm.product t u) (Preterm.product v u)

(* Beta reduction descends into the codomain position of products after opening. *)
| product_codomain :
  forall (l : list atom) (t : preterm), term t ->
  forall (u v : preterm), (fresh (a : l), beta (open_free a u) (open_free a v)) ->
  beta (Preterm.product t u) (Preterm.product t v).

Hint Resolve redex application_function application_argument : way.

Hint Extern 7 (beta (Preterm.abstraction _ _) (Preterm.abstraction _ _)) =>
  let stale := stale_atoms in
  match goal with
  | [ |- beta (Preterm.abstraction ?t ?u) (Preterm.abstraction ?v ?u) ] =>
    apply (Beta.abstraction_annotation stale)
  | [ |- beta (Preterm.abstraction ?t ?u) (Preterm.abstraction ?t ?v) ] =>
    apply (Beta.abstraction_body stale)
  end : way.

Hint Extern 7 (beta (Preterm.product _ _) (Preterm.product _ _)) =>
  let stale := stale_atoms in
  match goal with
  | [ |- beta (Preterm.product ?t ?u) (Preterm.product ?v ?u) ] =>
    apply (Beta.product_domain stale)
  | [ |- beta (Preterm.product ?t ?u) (Preterm.product ?t ?v) ] =>
    apply (Beta.product_codomain stale)
  end : way.

(* TODO(phs): Inversion showing beta implies term(?) *)
(* TODO(phs): Or just demand term from all relations *)

Module Examples.

Import Aliases.

Example omega : beta Preterm.Examples.omega Preterm.Examples.omega.
Proof.
  unfold Preterm.Examples.omega; infer.
Defined.

Example beta_reduction_eliminates_redex :
  beta
    (app (abs (type 1) (bvar 0)) (type 0))
    (type 0).
Proof.
  infer.
Defined.

Example beta_reduction_enters_application_function :
  beta
    (app
      (app (abs (type 2) (bvar 0)) (abs (type 1) (bvar 0)))
      (type 0))
    (app
      (abs (type 1) (bvar 0))
      (type 0)).
Proof.
  infer.
Defined.

Example beta_reduction_enters_application_argument :
  beta
    (app
      (abs (type 1) (bvar 0))
      (app (abs (type 1) (bvar 0)) (type 0)))
    (app
      (abs (type 1) (bvar 0))
      (type 0)).
Proof.
  infer.
Defined.

Example beta_reduction_enters_abstraction_annotation :
  beta
    (abs
      (app (abs (type 2) (bvar 0)) (type 1))
      (type 0))
    (abs
      (type 1)
      (type 0)).
Proof.
  infer.
Defined.

Example beta_reduction_enters_abstraction_body :
  beta
    (abs
      (type 1)
      (app (abs (type 1) (bvar 0)) (type 0)))
    (abs
      (type 1)
      (type 0)).
Proof.
  infer.
Defined.

Example beta_reduction_enters_product_domain :
  beta
    (prod
      (app (abs (type 1) (bvar 0)) (type 0))
      (type 0))
    (prod
      (type 0)
      (type 0)).
Proof.
  infer.
Defined.

Example beta_reduction_enters_product_codomain :
  beta
    (prod
      (type 0)
      (app (abs (type 1) (bvar 0)) (type 0)))
    (prod
      (type 0)
      (type 0)).
Proof.
  infer.
Defined.

End Examples.
