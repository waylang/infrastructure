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

Require Import Way.Beta.
Require Import Way.Context.
Require Import Way.Conversion.
Require Import Way.Open.
Require Import Way.Preterm.
Require Import Way.Relation.
Require Import Way.Subtyping.

(* Typings are proofs that under a given context, a given term has the given type.

Since types are terms, this emerges as a ternary relation between a context and two terms.

An interesting twist appears in the definition of contexts.  A context is a list that that
identifies the types of free variables in a term.  Since types are terms, the types
appearing in the context must themselves be well-typed, and can have free variables.  This
circular dependency is accounted for with a pair of mutually recursive definitions (or
"judgements").

The first kind of judgement is the typing of terms.
*)
Inductive typing : context -> preterm -> preterm -> Set :=

(* The type of a sort is the next sort in the hierarchy. *)
| type :
  forall (c : context), well_formed c -> forall (n : nat),
  typing c (Preterm.type n) (Preterm.type (S n))

(* The type of a free variable is that which it is bound to in a well-formed context. *)
| free_variable :
  forall (c : context), well_formed c -> forall (a : atom) (T : preterm), has (a, T) c ->
  typing c (Preterm.free_variable a) T

(* The type of a product is a sort, shared with its domain and codomain after opening.

Since the codomain can depend on the domain, we only require it to type after opening it
with the domain (using a sufficiently fresh free variable.)
*)
| product :
  forall (l : list atom) (c : context) (n : nat) (T U : preterm),
  typing c T (Preterm.type n) ->
  (fresh (a : l), typing ((a, T) :: c) (open_free a U) (Preterm.type n)) ->
  typing c (Preterm.product T U) (Preterm.type n)

(* The type of an abstraction is a well-typed product.

The abstraction body must have the product codomain as its type, after each has been
opened with the product's domain type (using a sufficiently fresh free variable.)
*)
| abstraction :
  forall (l : list atom) (n : nat) (c : context) (T U : preterm),
  typing c (Preterm.product T U) (Preterm.type n) ->
  forall (t : preterm),
  (fresh (a : l), typing ((a, T) :: c) (open_free a t) (open_free a U)) ->
  typing c (Preterm.abstraction T t) (Preterm.product T U)

(* The type of an application is its abstraction's codomain type opened with the argument.

The abstraction must have a product as its type, and the argument must be well-typed.
The equation involving open is required to allow proof search to match the head.
*)
| application :
  forall (T U : preterm) (c : context) (u : preterm),
  typing c u (Preterm.product T U) ->
  forall (t : preterm), typing c t T ->
  forall (v : preterm), v = open 0 t U ->
  typing c (Preterm.application u t) v

| subtyping :
  forall (T : preterm) (n : nat) (U : preterm), Subtyping.subtyping T U ->
  forall (c : context) (t : preterm), typing c t T ->
  typing c U (Preterm.type n) ->
  typing c t U

(* The second kind of judgement is the well-formation of contexts. *)
with well_formed : context -> Set :=

(* Empty contexts are well-formed. *)
| empty : well_formed []

(* A context that types a term as a type can be extended by it with a fresh variable. *)
| extend :
  forall (n : nat) (c : context) (T : preterm), typing c T (Preterm.type n) ->
  fresh (a : (domain c)), well_formed ((a, T) :: c).

Hint Resolve type free_variable empty : way.

Hint Extern 7 (typing _ (Preterm.product _ _) (Preterm.type _)) =>
  let stale := stale_atoms in apply (Typing.product stale) : way.

(* TODO(phs): hint extern for abstraction application subtyping extend *)

Module Examples.

Import Aliases.

(* TODO(phs): Use the type checker once it exists *)
Example polymorphic_identity :
  typing []
    Preterm.Examples.polymorphic_identity
    (prod (type 0) (prod (bvar 0) (bvar 1))).
Proof.
  unfold Preterm.Examples.polymorphic_identity;
  apply (Typing.abstraction [] 1);
  [ apply (Typing.product []);
    [ infer
    | intros a Ha; unfold open_free;
      apply (Typing.subtyping (type 1) 2);
      [ infer
      | apply (Typing.product [a]);
        [ apply (Typing.subtyping (type 0) 2);
          infer from (Typing.extend 1)
        | intros b Hb; unfold open_free;
          apply (Typing.subtyping (type 0) 2);
          [ infer
          | apply Typing.free_variable;
            [ apply (Typing.extend 0);
              [ apply Typing.free_variable;
                infer from (Typing.extend 1)
              | infer
              ]
            | infer
            ]
          | apply Typing.type;
            apply (Typing.extend 0);
            [ apply Typing.free_variable;
              infer from (Typing.extend 1)
            | infer
            ]
          ]
        ]
      | infer from (Typing.extend 1)
      ]
    ]
  | intros a Ha; unfold open_free;
    apply (Typing.abstraction [a] 0);
    [ apply (Typing.product [a]);
      [ infer from (Typing.extend 1)
      | intros b Hb; unfold open_free;
        apply Typing.free_variable;
        [ apply (Typing.extend 0);
          [ apply Typing.free_variable;
            infer from (Typing.extend 1)
          | infer
          ]
        | infer
        ]
      ]
    | intros b Hb; unfold open_free;
      apply Typing.free_variable;
      [ apply (Typing.extend 0);
        [ apply Typing.free_variable;
          infer from (Typing.extend 1)
        | infer
        ]
      | infer
      ]
    ]
  ].
Defined.

(* TODO(phs): Demonstrate polymorphic identity application *)
(* You chose type 0 in the definition of the identity.  This is tricky without base types
or the polymorphism allowing us to elide universe indices.
Example apply_polymorphic_identity :
  typing []
    (app Preterm.Examples.polymorphic_identity (abs (type 0) (bvar 0)))
    (prod (type 0) (type 0))
*)

Example type_of_sort_is_next_sort : typing [] (type 3) (type 4).
Proof.
  infer.
Defined.

Example type_of_free_variable_is_in_context :
  forall (a : atom), typing [(a, (type 7))] (fvar a) (type 7).
Proof.
  infer from (Typing.extend 8).
Defined.

Example type_of_product_is_sort : typing [] (prod (type 1) (type 1)) (type 2).
Proof.
  infer from (Typing.extend 2).
Defined.

Example type_of_abstraction_is_product :
  typing [] (abs (type 3) (bvar 0)) (prod (type 3) (type 3)).
Proof.
  infer from
    (Typing.abstraction [] 4)
    (Typing.extend 4).
Defined.

Example type_of_application_is_product_codomain :
  typing [] (app (abs (type 1) (bvar 0)) (type 0)) (type 1).
Proof.
  infer from
    (Typing.application (type 1) (type 1))
    (Typing.abstraction [] 2)
    (Typing.extend 2).
Defined.

Example terms_of_subtype_are_terms_of_supertype :
  typing []
    (type 0)
    (app (abs (type 2) (bvar 0)) (type 1)).
Proof.
  apply (Typing.subtyping (type 1) 2);
  [ apply Subtyping.conversion;
    apply Equivalence.symmetry
  | | ];
  infer from
    (Typing.application (type 2) (type 2))
    (Typing.abstraction [] 3)
    (Typing.extend 3).
Defined.

Example empty_context_is_well_formed : well_formed [].
Proof.
  infer.
Defined.

Example context_extended_with_fresh_name_is_well_formed :
  forall (a b : atom), a <> b -> well_formed [(a, (type 0)); (b, (type 0))].
Proof.
  infer from (Typing.extend 1).
Defined.

End Examples.
