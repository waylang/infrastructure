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

Require Import Way.Beta.
Require Import Way.Open.
Require Import Way.Preterm.
Require Import Way.Relation.

(* The small-step conversion relation.

The calculus of constructions and related theories have a notion of type equivalence: if
two well-sorted types are "convertible" then the terms of one are the terms of the other.
Two terms (such as these types) are convertible if they are equal after applying some
sequence of reduction rules, such as those of beta reduction.

This is "small-step" since it has not yet been extended into an equivalence relation.
*)
Inductive step : relation :=

(* Terms are convertible if one beta reduces to the other. *)
| beta : forall (t u : preterm), Beta.beta t u -> step t u.

Hint Constructors step : way.

Definition conversion := equivalence step.

Hint Unfold conversion : way.

Module Examples.

Import Aliases.

Example conversion_relates_terms_with_common_beta_reducts :
  conversion
    (prod
      (app (abs (type 1) (bvar 0)) (type 0))
      (type 0))
    (prod
      (type 0)
      (app (abs (type 1) (bvar 0)) (type 0))).
Proof.
  apply (Equivalence.transitivity Conversion.step (prod (type 0) (type 0)));
  [ | apply Equivalence.symmetry ];
  infer.
Defined.

End Examples.
