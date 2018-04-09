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

Require Import Way.Context.
Require Import Way.FreeVariables.
Require Import Way.List.
Require Import Way.Preterm.

Ltac stale_atoms :=
  let rec find acc :=
    match goal with
    | l: list atom |- _ => collect acc l
    | a: atom |- _ => collect acc [a]
    | c: Context.context |- _ => collect acc (domain c)
    | p: preterm |- _ => collect acc (free_variables p)
    | _ => acc
    end
  with collect acc l :=
    match acc with
    | [] => find l
    | context [l] => fail 1
    | _ => find (l ++ acc)
    end in
  let rec prettify acc l :=
    match l with
    | ?l1 ++ ?l2 => let acc1 := prettify acc l2 in prettify acc1 l1
    | [] => acc
    | ?l1 =>
      match acc with
      | [] => l1
      | context [l1] => acc
      | _ => constr:(l1 ++ acc)
      end
    end in
  let stale := find (@nil atom) in
  prettify (@nil atom) stale.
