(*
vim: set fenc=utf-8 ff=unix sts=2 sw=2 et ft=coq :
*)
(*
Copyright (C) 2016-2019 Philip H. Smith

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

Lemma eq_nat_dec : forall (n m : nat), {n = m} + {n <> m}.
Proof.
  induction n as [ | ? IH ];
  induction m;
  [ | | | destruct (IH m) ];
  infer.
Defined.

Lemma le_trans : forall (n m p : nat), n <= m -> m <= p -> n <= p.
Proof.
  induction 2; infer.
Defined.

Lemma le_0_n : forall (n : nat), 0 <= n.
Proof.
  induction n; infer.
Defined.

Lemma le_n_S : forall (n m : nat), n <= m -> S n <= S m.
Proof.
  induction 1; infer.
Defined.

Lemma le_S_n : forall (n m : nat), S n <= S m -> n <= m.
Proof.
  intros n m H;
  inversion H;
  infer from (le_trans n (S n) m).
Defined.

Lemma le_Sn_n : forall n, ~ S n <= n.
Proof.
  intros n H;
  induction n;
  inversion H;
  infer from le_S_n.
Defined.

Lemma lt_irrefl : forall (n : nat), ~ n < n.
Proof.
  unfold lt;
  apply le_Sn_n.
Defined.

Lemma le_lt_trans : forall (n m p : nat), n <= m -> m < p -> n < p.
Proof.
  induction 2; infer from le_n_S.
Defined.

Lemma le_max_l : forall (n m : nat), n <= max n m.
Proof.
  induction n;
  induction m;
  infer from le_n_S.
Defined.

Lemma le_max_r : forall (n m : nat), m <= max n m.
Proof.
  induction n;
  induction m;
  infer from le_0_n le_n_S.
Defined.
