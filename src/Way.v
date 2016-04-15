Require Import Arith.
Require Import Eqdep_dec.
Require Import List.
Require Import MSetInterface.
Require Import MSetList.
Require Import MSetProperties.

Lemma InA_iff_In :
  forall (A : Type) x xs, InA (@eq A) x xs <-> In x xs.
Proof.
  split.

  induction xs as [ | y ys IH ].
    intros H. inversion H.
    intros H. inversion H; subst; simpl.

    left. reflexivity.

    right. exact (IH H1).

  exact (@In_InA A eq (@eq_equivalence A) xs x).
Qed.
