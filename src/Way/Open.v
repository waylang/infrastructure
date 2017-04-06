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

Require Import Way.Nat.
Require Import Way.Preterm.

(* Replace a bound variable i with replacement u in preterm p

No shifting, lifting or other house keeping is done on the remaining de Bruijn indices.
*)
Fixpoint open (i : nat) (u p : preterm) : preterm :=
  match p with

  | free_variable _ => p

  | bound_variable b => if eq_nat_dec i b then u else p

  | product a b => product (open i u a) (open (S i) u b)

  | abstraction a b => abstraction (open i u a) (open (S i) u b)

  | application f a => application (open i u f) (open i u a)

  | type _ => p

  end.

(* Open bound variable 0 in a term with a free variable. *)
Definition open_free (a : atom) (p : preterm) : preterm :=
  open 0 (Preterm.free_variable a) p.

Hint Unfold open_free : way.

Module Examples.

Import Aliases.

Example fvar_is_unchanged :
  forall (a b : atom), open_free a (fvar b) = (fvar b).
Proof.
  infer.
Defined.

Example same_bvar_is_opened :
  forall (a : atom), open_free a (bvar 0) = (fvar a).
Proof.
  infer.
Defined.

Example different_bvar_is_unchanged :
  forall (a : atom), open_free a (bvar 1) = (bvar 1).
Proof.
  infer.
Defined.

Example prod_opens_bvar_into_annotation :
  forall (a : atom), open_free a (prod (bvar 0) (bvar 0)) = (prod (fvar a) (bvar 0)).
Proof.
  infer.
Defined.

Example prod_opens_incremented_bvar_into_body :
  forall (a : atom), open_free a (prod (bvar 1) (bvar 1)) = (prod (bvar 1) (fvar a)).
Proof.
  infer.
Defined.

Example abs_opens_bvar_into_annotation :
  forall (a : atom), open_free a (abs (bvar 0) (bvar 0)) = (abs (fvar a) (bvar 0)).
Proof.
  infer.
Defined.

Example abs_opens_incremented_bvar_into_body :
  forall (a : atom), open_free a (abs (bvar 1) (bvar 1)) = (abs (bvar 1) (fvar a)).
Proof.
  infer.
Defined.

Example app_opens_into_subterms :
  forall (a : atom), open_free a (app (bvar 0) (bvar 0)) = (app (fvar a) (fvar a)).
Proof.
  infer.
Defined.

Example type_is_unchanged :
  forall (a : atom) (n : nat), open_free a (type n) = (type n).
Proof.
  infer.
Defined.

End Examples.
