(*
  vim: set fenc=utf-8 ff=unix sts=2 sw=2 et ft=coq
*)
(*
Copyright (C) 2016-2018 Philip H. Smith

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

Require Import Way.List.
Require Import Way.Nat.

Lemma has_le_fold_max : forall (n : nat) (l : list nat), has n l -> n <= fold max 0 l.
Proof.
  intro n;
  induction l;
  [ infer
  | infer from eq_nat_dec le_max_l (le_trans n (fold max 0 l)) le_max_r ].
Defined.

Lemma fold_max_lt_not_has :
  forall (n : nat) (l : list nat), fold max 0 l < n -> ~ has n l.
Proof.
  intros n l;
  infer from has_le_fold_max (le_lt_trans n (fold max 0 l)) (lt_irrefl n).
Defined.

Lemma fresh_nat : forall (l : list nat), {n : nat | ~ has n l}.
Proof.
  intro l;
  exists (S (fold max 0 l));
  infer from fold_max_lt_not_has.
Defined.
