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

Require Import Way.Preterm.

(* A binary relation over preterms. *)
Definition relation := preterm -> preterm -> Set.

Module Star.

(* The reflexive-transitive closure of a relation. *)
Inductive star (r : relation) : relation :=

(* Preterms relate to themselves. *)
| reflexivity : forall (t : preterm), star r t t

(* Preterms relate if related in the underlying relation *)
| include : forall (t u : preterm), r t u -> star r t u

(* Preterms relate if they relate to a third common preterm. *)
(* TODO(phs): Syntax-directed *)
| transitivity : forall (v t u : preterm), star r t v -> star r v u -> star r t u.

(* Don't need transitivity, which needs a parameter and so will never be inferred. *)
Hint Resolve reflexivity include : way.

End Star.

Export Star.

Module Equivalence.

(* The reflexive-symmetric-transitive closure of a relation. *)
Inductive equivalence (r : relation) : relation :=

(* Preterms relate to themselves. *)
| reflexivity : forall (t : preterm), equivalence r t t

(* Preterms relate if related in the underlying relation *)
| include : forall (t u : preterm), r t u -> equivalence r t u

(* Preterms relate if they relate to a third common preterm. *)
(* TODO(phs): Syntax-directed *)
| symmetry : forall (t u : preterm), equivalence r u t -> equivalence r t u

(* Preterms relate if they relate to a third common preterm. *)
(* TODO(phs): Syntax-directed *)
| transitivity :
  forall (v t u : preterm), equivalence r t v -> equivalence r v u -> equivalence r t u.

(* Don't add symmetry, search can spend its depth on useless pairs of applictions. *)
(* Don't need transitivity, which needs a parameter and so will never be inferred. *)
Hint Resolve reflexivity include : way.

End Equivalence.

Export Equivalence.

Module Examples.

Import Aliases.

Inductive example_relation : relation :=
| decrease : forall (n : nat), example_relation (type (S n)) (type n).

Example star_relations_are_reflexive : star example_relation (type 3) (type 3).
Proof.
  infer.
Defined.

Example star_relations_include_their_arguments : star example_relation (type 1) (type 0).
Proof.
  infer from decrease.
Defined.

Example star_relations_are_transitive : star example_relation (type 2) (type 0).
Proof.
  infer from (Star.transitivity example_relation (type 1)) decrease.
Defined.

Example equivalence_relations_are_reflexive :
  equivalence example_relation (type 2) (type 2).
Proof.
  infer.
Defined.

Example equivalence_relations_include_their_arguments :
  equivalence example_relation (type 1) (type 0).
Proof.
  infer from decrease.
Defined.

Example equivalence_relations_are_symmetric :
  equivalence example_relation (type 0) (type 1).
Proof.
  infer from Equivalence.symmetry decrease.
Defined.

Example equivalence_relations_are_transitive :
  equivalence example_relation (type 2) (type 0).
Proof.
  infer from
    (Equivalence.transitivity example_relation (type 1))
    decrease.
Defined.

End Examples.
