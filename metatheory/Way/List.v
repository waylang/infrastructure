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

Open Scope list_scope.

Notation " [ ] " := nil (format "[ ]") : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; y ; .. ; z ] " := (cons x (cons y .. (cons z nil) ..)) : list_scope.

(* Right fold *)
Fixpoint fold {A B : Type} (f : A -> B -> B) (b : B) (l : list A) {struct l} : B :=
  match l with
  | [] => b
  | a :: t => f a (fold f b t)
  end.

Module FoldExamples.

Example plus_over_triple : fold plus 0 [3; 1; 4] = 8.
Proof.
  infer.
Defined.

Example cons_over_triple : fold (@cons nat) nil [3; 1; 4] = [3; 1; 4].
Proof.
  infer.
Defined.

End FoldExamples.

Lemma unfold : forall {A B : Type} (f : A -> B -> B) (b : B) (a : A) (t : list A),
  fold f b (a :: t) = f a (fold f b t).
Proof.
  infer.
Defined.

Definition map {A B : Type} (f : A -> B) (l : list A) : list B :=
  fold (fun e t => (f e) :: t) [] l.

Module MapExamples.

Example successor_over_triple : map S [3; 1; 4] = [4; 2; 5].
Proof.
  infer.
Defined.

End MapExamples.

Definition has {A : Type} (a : A) (l : list A) : Prop :=
  fold (fun e acc => e = a \/ acc) False l.

Hint Unfold has : way.

Module HasExamples.

Example a_zero_in_pair : has 0 [2; 7] = (2 = 0 \/ 7 = 0 \/ False).
Proof.
  infer.
Defined.

End HasExamples.

Lemma intro_has_singleton :
  forall {A : Type} (a b : A), b = a -> has a [b].
Proof.
  infer.
Defined.

Hint Resolve intro_has_singleton : way.

Lemma elim_has_singleton :
  forall {A : Type} (a b : A), has a [b] -> b = a.
Proof.
  infer.
Defined.

Hint Extern 7 => match goal with
| [ H : has ?a [?b] |- _ ] => pose proof (elim_has_singleton a b H)
end : way.

Lemma intro_not_has_singleton :
  forall {A : Type} (a b : A), b <> a -> ~ has a [b].
Proof.
  infer.
Defined.

Hint Resolve intro_not_has_singleton : way.

Lemma elim_not_has_singleton :
  forall {A : Type} (a b : A), ~ has a [b] -> b <> a.
Proof.
  infer.
Defined.

Hint Extern 7 => match goal with
| [ H : ~ has ?a [?b] |- _ ] => pose proof (elim_not_has_singleton a b H)
end : way.

Lemma intro_has_cons :
  forall {A : Type} (a b : A) (l : list A), b = a \/ has a l -> has a (b :: l).
Proof.
  infer.
Defined.

Hint Resolve intro_has_cons : way.

Lemma elim_has_cons :
  forall {A : Type} (a b : A) (l : list A), has a (b :: l) -> b = a \/ has a l.
Proof.
  infer.
Defined.

Hint Extern 7 => match goal with
| [ H : has ?a (?b :: ?l) |- _ ] => pose proof (elim_has_cons a b l H)
end : way.

Lemma intro_not_has_cons :
  forall {A : Type} (a b : A) (l : list A), b <> a /\ ~ has a l -> ~ has a (b :: l).
Proof.
  infer.
Defined.

Hint Resolve intro_not_has_cons : way.

Lemma elim_not_has_cons :
  forall {A : Type} (a b : A) (l : list A), ~ has a (b :: l) -> b <> a /\ ~ has a l.
Proof.
  infer.
Defined.

Hint Extern 7 => match goal with
| [ H : ~ has ?a (?b :: ?l) |- _ ] => pose proof (elim_not_has_cons a b l H)
end : way.

Lemma intro_has_append :
  forall {A : Type} (a : A) (l m : list A), has a l \/ has a m -> has a (m ++ l).
Proof.
  induction m; infer.
Defined.

Hint Resolve intro_has_append : way.

Lemma elim_has_append :
  forall {A : Type} (a : A) (l m : list A), has a (m ++ l) -> has a l \/ has a m.
Proof.
  induction m; infer.
Defined.

Hint Extern 7 => match goal with
| [ H : has ?a (?m ++ ?l) |- _ ] => pose proof (elim_has_append a l m H)
end : way.

Lemma intro_not_has_append :
  forall {A : Type} (a : A) (l m : list A), ~ has a l /\ ~ has a m -> ~ has a (l ++ m).
Proof.
  infer.
Defined.

Hint Resolve intro_not_has_append : way.

Lemma elim_not_has_append :
  forall {A : Type} (a : A) (l m : list A), ~ has a (l ++ m) -> ~ has a l /\ ~ has a m.
Proof.
  infer.
Defined.

Hint Extern 7 => match goal with
| [ H : ~ has ?a (?l ++ ?m) |- _ ] => pose proof (elim_not_has_append a l m H)
end : way.

Lemma elim_not_has_append2 :
  forall {A : Type} (a : A) (l m n : list A),
  ~ has a (l ++ m ++ n) -> ~ has a l /\ ~ has a m /\ ~ has a n.
Proof.
  infer.
Defined.

Hint Extern 7 => match goal with
| [ H : ~ has ?a (?l ++ ?m ++ ?n) |- _ ] => pose proof (elim_not_has_append2 a l m n H)
end : way.
