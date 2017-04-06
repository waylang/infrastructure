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

(* Collect the names of the free variables in a preterm into a list. *)
Fixpoint free_variables (p : preterm) : list atom :=
  match p with

  | free_variable a => [a]

  | bound_variable _ => []

  | product a b => (free_variables a) ++ (free_variables b)

  | abstraction a b => (free_variables a) ++ (free_variables b)

  | application f a => (free_variables f) ++ (free_variables a)

  | type _ => []

  end.

Module Examples.

Import Aliases.

Example free_variables_of_fvar_is_singleton :
  forall (a : atom), free_variables (fvar a) = [a].
Proof.
  infer.
Defined.

Example free_variables_of_bvar_are_empty : free_variables (bvar 0) = [].
Proof.
  infer.
Defined.

Example free_variables_of_prod_are_those_of_domain_and_codomain :
  forall (a b : atom), free_variables (prod (fvar a) (fvar b)) = [a; b].
Proof.
  infer.
Defined.

Example free_variables_of_abs_are_those_of_annotation_and_body :
  forall (a b : atom), free_variables (abs (fvar a) (fvar b)) = [a; b].
Proof.
  infer.
Defined.

Example free_variables_of_app_are_those_of_function_and_argument :
  forall (a b : atom), free_variables (abs (fvar a) (fvar b)) = [a; b].
Proof.
  infer.
Defined.

Example free_variables_of_type_are_empty : free_variables (type 0) = [].
Proof.
  infer.
Defined.

End Examples.
