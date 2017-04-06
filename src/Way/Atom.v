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

Require Import Way.ListNat.
Require Import Way.Nat.

(* Publish notation to clients. *)
Require Export Way.List.

Module Type AtomType.

  Parameter atom : Set.

  Parameter fresh_atom : forall (l : list atom), {a : atom | ~ has a l}.

  Parameter eq_atom_dec : forall (a b : atom), {a = b} + {a <> b}.

End AtomType.

Module AtomImpl : AtomType.

  Definition atom := nat.

  Definition fresh_atom := fresh_nat.

  Definition eq_atom_dec := eq_nat_dec.

End AtomImpl.

Export AtomImpl.

(* Syntactic sugar for cofinite quantification. *)
Notation "'fresh' ( a : l ) , P" :=
  (forall (a : atom), ~ has a l -> P) (at level 67, a at level 99) : way_scope.

Open Scope way_scope.
