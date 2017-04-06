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

Require Export Way.Atom.

(* Preterms are terms that may have dangling bound variables.

Variables are managed in the locally nameless style. This means that free and bound
variables are syntactically distinct.  Free variables are identified by names (atoms),
while bound variables are given de Bruijn indices.  This eliminates the need for alpha
conversion, but opens the possibility that bound variable indices may be invalid (that is,
may refer to abstractions which do not exist).  "Local closure" is the property that all
such indices are valid.
*)
Inductive preterm : Set :=

(* A named variable appearing in the term's context *)
| free_variable : atom -> preterm

(* A nameless variable (de Bruijn index)

de Bruijn indices appearing in binder annotations (the argument types of lambdas and
products) do not range over the binder they are included in.  Indices appearing in the
bodies of those terms do.

Thus the polymorphic identity, informally (forall (x : Set), (fun (y : x), y)) becomes
(prod (type 0) (abs (bvar 0) (bvar 0))).  Notice how the two occurrences of (bvar 0) refer
to different bound variables even though they appear within the same abs, due to their
placement.
*)
| bound_variable : nat -> preterm

(* Introduce a dependent product *)
| product : preterm -> preterm -> preterm

(* Introduce a lambda *)
| abstraction : preterm -> preterm -> preterm

(* Eliminate an abstraction *)
| application : preterm -> preterm -> preterm

(* Introduce a sort (type of types)

Non-type terms have types whose type is type 0. The type of type 0 is type 1, and so on.
This is the "stratified" presentation avoiding Girard's paradox.
*)
| type : nat -> preterm.

Module Aliases.

(* It seems these simple rewrites cannot be put into notation scopes. *)
Notation fvar := free_variable.
Notation bvar := bound_variable.
Notation prod := product.
Notation abs := abstraction.
Notation app := application.
Notation type := Preterm.type.

End Aliases.

Module Examples.

Import Aliases.

(* Fudge the annotations; omega isn't typable anyway *)
Example omega :=
  (app
    (abs (type 0) (app (bvar 0) (bvar 0)))
    (abs (type 0) (app (bvar 0) (bvar 0)))).

Example polymorphic_identity := (prod (type 0) (abs (bvar 0) (bvar 0))).

End Examples.
