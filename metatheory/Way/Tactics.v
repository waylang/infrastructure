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

(* Make a private, static copy of the core hint database. *)
Create HintDb waycore discriminated.

Hint Unfold
  CompSpec
  CompSpecT
  ge
  gt
  lt
  not
: waycore.

Hint Resolve
  (f_equal (A:=nat))
  (f_equal2 (A1:=nat) (A2:=nat))
  (f_equal2 mult)
  BoolSpecF
  BoolSpecT
  CompEq
  CompEqT
  CompGt
  CompGtT
  CompLt
  CompLtT
  I
  O_S
  conj
  eq_refl
  ex_intro
  ex_intro2
  exist
  exist2
  existT
  existT2
  identity_refl
  inhabits
  inl
  inleft
  inr
  inright
  le_S
  le_n
  left
  mult_n_O
  mult_n_Sm
  n_Sn
  not_eq_S
  or_introl
  or_intror
  pair
  plus_n_O
  plus_n_Sm
  right
: waycore.

Hint Immediate
  eq_add_S
  eq_sym
  identity_sym
  not_eq_sym
  not_identity_sym
: waycore.

Hint Constructors
  le
: waycore.

(* A separate hint database for our own hints. *)
Create HintDb way discriminated.

Hint Unfold
  notT
: way.

(* Our central work-horse tactic, in the spirit of Prof. Chlipala's crush. *)
Hint Extern 5 => progress simpl in * : way.
Hint Extern 5 => match goal with
| [ |- context[match ?I with _ => _ end] ] => destruct I
end : way.

Hint Extern 6 => progress subst : way.
Hint Extern 6 => contradiction : way.
Hint Extern 6 => progress f_equal : way.
Hint Extern 6 => congruence : way.
Hint Extern 6 => progress intuition idtac : way.

(* Level 7 is reserved for application-specific tactics. *)

Hint Extern 8 => match goal with
| [ H : ex _ |- _ ] => destruct H
| [ _ : context[match ?I with _ => _ end] |- _ ] => destruct I

| [ H : _ _ |- _ ] => inversion_clear H
| [ H : _ _ _ |- _ ] => inversion_clear H
| [ H : _ _ _ _ |- _ ] => inversion_clear H
| [ H : _ _ _ _ _ |- _ ] => inversion_clear H
| [ H : _ _ _ _ _ _ |- _ ] => inversion_clear H
end : way.

Hint Extern 9 => symmetry : way.

Tactic Notation "infer" "from" constr_list(lemmas) :=
  auto 5 using lemmas with nocore waycore way;
  auto 20 using lemmas with nocore waycore way.

Tactic Notation "infer" := infer from.
