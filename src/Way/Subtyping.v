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

Require Import Way.Conversion.
Require Import Way.Open.
Require Import Way.Preterm.
Require Import Way.Relation.
Require Import Way.Term.

(* The subtyping relation.

Subtyping serves two roles in this logic.  First it includes conversion, and so the
conversion typing rule becomes the subtyping rule.  Second it brings transitivity to the
type hierarchy, allowing (type 0) to be considered a term of (type 2), for example.
*)
Inductive subtyping : relation :=

(* Convertible types are subtypes of each other. *)
| conversion : forall (T U : preterm), Conversion.conversion T U -> subtyping T U

(* Each sort is a subtype of the next in the hierarchy. *)
| type : forall (n : nat), subtyping (Preterm.type n) (Preterm.type (S n))

(* Subtyping descends into codomains of products with convertible domains. *)
| product : forall (l : list atom) (T V : preterm), Conversion.conversion T V ->
  forall (U W : preterm), (fresh (a : l), subtyping (open_free a U) (open_free a W)) ->
  subtyping (Preterm.product T U) (Preterm.product V W)

(* Terms are reflexivily subtypes of themselves. *)
(* TODO(phs): If we could move this guard then we could use star. *)
(* TODO(phs): Alternately, we could demand relations deal only in terms *)
| reflexivity : forall (T : preterm), term T -> subtyping T T

(* Subtyping is transitive. *)
| transitivity :
    forall (U T V : preterm), subtyping T U -> subtyping U V -> subtyping T V.

Hint Resolve conversion type reflexivity : way.

Module Examples.

Import Aliases.

Example convertible_terms_are_subtypes :
  subtyping
    (app (abs (type 1) (bvar 0)) (type 0))
    (type 0).
Proof.
  infer.
Defined.

Example sort_is_subtype_of_next : subtyping (type 2) (type 3).
Proof.
  infer.
Defined.

Example subtyping_descends_into_product_codomains :
  subtyping
    (prod (type 0) (app (abs (type 1) (bvar 0)) (type 0)))
    (prod (type 0) (type 0)).
Proof.
  infer.
Defined.

Example subtyping_is_reflexive_for_terms :
  subtyping
    (abs (type 0) (bvar 0))
    (abs (type 0) (bvar 0)).
Proof.
  infer.
Defined.

Example subtyping_is_transitive : subtyping (type 0) (type 2).
Proof.
  apply (Subtyping.transitivity (type 1));
  infer.
Defined.

End Examples.
