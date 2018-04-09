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

Require Import Way.Atom.
Require Import Way.List.
Require Import Way.Preterm.

(* Contexts are lists of atom-preterm pairs. *)
Definition context := list (atom * preterm)%type.

(* The atoms defined by a context. *)
Function domain (c : context) : list atom := map (@fst atom preterm) c.

Module DomainExamples.

Example triple :
  forall (a b c : atom) (T U V : preterm), domain [(a, T); (b, U); (c, V)] = [a; b; c].
Proof.
  infer.
Defined.

End DomainExamples.
