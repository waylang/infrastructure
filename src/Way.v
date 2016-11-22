(*
Copyright (C) 2016-2016 Philip H. Smith

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
*)

Require Import Arith.
Require Import MSetInterface.
Require Import MSetList.
Require Import MSetFacts.
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

Section Equality_ext.

Variable A : Type.
Variable ltA : relation A.
Hypothesis ltA_trans : forall x y z, ltA x y -> ltA y z -> ltA x z.
Hypothesis ltA_not_eqA : forall x y, ltA x y -> x <> y.
Hypothesis ltA_eqA : forall x y z, ltA x y -> y = z -> ltA x z.
Hypothesis eqA_ltA : forall x y z, x = y -> ltA y z -> ltA x z.

Notation Inf := (lelistA ltA).
Notation Sort := (sort ltA).

Lemma StrictOrder_ltA :
  StrictOrder ltA.
Proof.
  assert (forall x : A, ~ ltA x x) as H_lta_irreflexive.
  intro x. unfold not. intro H_lta_x_x.
  contradiction (ltA_not_eqA x x H_lta_x_x).
  reflexivity.

  apply Build_StrictOrder.
  exact H_lta_irreflexive.
  exact ltA_trans.
Qed.

Lemma not_InA_if_Sort_Inf :
  forall xs a, Sort xs -> Inf a xs -> ~ InA (@eq A) a xs.
Proof.
  induction xs as [ | x xs IH ]; intros a Hsort Hinf H.
  inversion H.
  inversion H; subst.
    inversion Hinf; subst.
      assert (complement ltA x x) by
        exact ((@StrictOrder_Irreflexive A ltA StrictOrder_ltA) x).
      exact (H0 H1).
    inversion Hsort; inversion Hinf; subst.
      assert (Inf a xs) by exact (InfA_ltA StrictOrder_ltA H6 H4).
      assert (~ InA (@eq A) a xs) by exact (IH a H3 H0).
      intuition.
Qed.

Lemma Sort_eq_head :
  forall x xs y ys,
  Sort (x :: xs) ->
  Sort (y :: ys) ->
  (forall a, InA (@eq A) a (x :: xs) <-> InA (@eq A) a (y :: ys)) ->
  x = y.
Proof.
  intros x xs y ys SortXS SortYS H.
  inversion SortXS; inversion SortYS; subst.
  assert (Q3 : InA (@eq A) x (y :: ys)) by firstorder.
  assert (Q4 : InA (@eq A) y (x :: xs)) by firstorder.
  inversion Q3; subst. reflexivity.
  inversion Q4; subst. reflexivity.
  assert (Proper (eq ==> eq ==> iff) ltA) by intuition.
  assert (ltA y x) by (refine (SortA_InfA_InA _ _ _ H6 H7 H1); exact StrictOrder_ltA).
  assert (ltA x y) by (refine (SortA_InfA_InA _ _ _ H2 H3 H4); exact StrictOrder_ltA).
  assert (y <> y) by exact (ltA_not_eqA y y (ltA_trans y x y H5 H8)).
  intuition.
Qed.

Lemma Sort_InA_eq_ext :
  forall xs ys,
  Sort xs ->
  Sort ys ->
  (forall a, InA (@eq A) a xs <-> InA (@eq A) a ys) ->
  xs = ys.
Proof.
  induction xs as [ | x xs IH_xs ]; induction ys as [ | y ys IH_ys ];
    intros H_sorted_xs H_sorted_ys H_equal_as_sets.

    (* nil = nil *)
    reflexivity.

    (* nil = y :: ys *)
    assert (InA eq y nil) as H_y_in_nil.
      apply (proj2 (H_equal_as_sets y)).
      apply InA_cons_hd.
      reflexivity.
    inversion H_y_in_nil.

    (* x :: xs = nil *)
    assert (InA eq x nil) as H_x_in_nil.
      apply (proj1 (H_equal_as_sets x)).
      apply InA_cons_hd.
      reflexivity.
    inversion H_x_in_nil.

    (* x :: xs = y :: ys *)
    inversion H_sorted_xs as
      [
      | x' xs' H_sorted_tail_xs H_inf_x_tail_xs [ H_x_prime_eq_x H_xs_prime_eq_xs ] ].
    inversion H_sorted_ys as
      [
      | y' ys' H_sorted_tail_ys H_inf_y_tail_ys [ H_y_prime_eq_y H_ys_prime_eq_ys ] ].
    subst.
    assert (x = y) as H_x_eq_y by
      exact (Sort_eq_head x xs y ys H_sorted_xs H_sorted_ys H_equal_as_sets).
    assert (forall (a : A), InA (@eq A) a xs <-> InA (@eq A) a ys)
        as H_tails_equal_as_sets.
      intro a. split; intro H_a_in_left.

      (* InA eq a ys *)
      assert (InA (@eq A) a (y :: ys)) as H_a_in_ys.
        apply (proj1 (H_equal_as_sets a)).
        apply InA_cons_tl.
        exact H_a_in_left.
      inversion H_a_in_ys as
        [ y' ys' H_a_eq_y [ H_y_prime_eq_y H_ys_prime_eq_ys ]
        | y' ys' H_a_in_tail_ys [ H_y_prime_eq_y H_ys_prime_eq_ys ] ]; subst.

        (* InA eq y ys *)
        assert (Inf y xs) as H_inf_y_xs.
          exact H_inf_x_tail_xs.
        assert (~ InA eq y xs) as H_y_notin_xs by
          exact (not_InA_if_Sort_Inf xs y H_sorted_tail_xs H_inf_y_xs).
        intuition.

        (* InA eq a ys *)
        exact H_a_in_tail_ys.

      (* InA eq a xs *)
      assert (InA (@eq A) a (x :: xs)) as H_a_in_xs.
        apply (proj2 (H_equal_as_sets a)).
        apply InA_cons_tl.
        exact H_a_in_left.
      symmetry in H_x_eq_y.
      inversion H_a_in_xs as
        [ x' xs' H_a_eq_x [ H_x_prime_eq_x H_xs_prime_eq_xs ]
        | x' xs' H_a_in_tail_xs [ H_x_prime_eq_x H_xs_prime_eq_xs ] ]; subst.

        (* InA eq x xs *)
        assert (Inf x ys) as H_inf_x_ys by exact H_inf_y_tail_ys.
        assert (~ InA eq x ys) as H_x_notin_ys by
          exact (not_InA_if_Sort_Inf ys x H_sorted_tail_ys H_inf_x_ys).
        intuition.

        (* InA eq a xs *)
        exact H_a_in_tail_xs.

    assert (xs = ys) by
      exact (IH_xs ys H_sorted_tail_xs H_sorted_tail_ys H_tails_equal_as_sets).
    subst.
    reflexivity.
Qed.

End Equality_ext.

Module FiniteSets.

Module Type S.

  Declare Module E : UsualOrderedType.
  Declare Module F : MSetInterface.S with Module E := E.

  Parameter eq_if_Equal :
    forall s s' : F.t, F.Equal s s' -> s = s'.

End S.

Module Make (X : UsualOrderedType) <: S with Module E := X.

  Module E := X.
  Module F := MSetList.Make E.

  Axiom f_ok_proof_irrel : forall l (p q : F.Raw.Ok l), p = q.

  Lemma eq_if_Equal :
    forall s s' : F.t, F.Equal s s' -> s = s'.
  Proof.
    intros [l H_ok] [l' H_ok'] Eq.
    assert (Sorted F.E.lt l) as H_Sorted_l.
      rewrite F.Raw.isok_iff. exact H_ok.
    assert (Sorted F.E.lt l') as H_Sorted_l'.
      rewrite F.Raw.isok_iff. exact H_ok'.
    assert (forall x y : F.Raw.elt, F.E.lt x y -> x <> y) as H_lt_not_eq.
      intros x y H_lt_x_y. contradict H_lt_x_y. rewrite H_lt_x_y.
      apply (@StrictOrder_Irreflexive _ _ E.lt_strorder).
    assert (forall x y z : F.Raw.elt, x = y -> F.E.lt y z -> F.E.lt x z) as H_eq_lt.
      intros x y z H_eq H_lt. rewrite H_eq. exact H_lt.
    assert (l = l') as H_l_eq_l' by exact (Sort_InA_eq_ext
      F.Raw.elt F.E.lt
      (@StrictOrder_Transitive F.Raw.elt F.E.lt E.lt_strorder)
      H_lt_not_eq
      l l'
      H_Sorted_l
      H_Sorted_l'
      Eq).
    subst l'.
    assert (H_ok = H_ok') as H_ok_proof_irrel by exact (f_ok_proof_irrel l H_ok H_ok').
    subst H_ok'.
    reflexivity.
  Qed.

End Make.

End FiniteSets.

Module FSetNotin.

Module Notin (X : MSetInterface.S).

Import X.

Lemma elim_notin_union : forall x E F,
  ~ In x (union E F) -> (~ In x E) /\ (~ In x F).
Proof.
  intros x E F H_not_in_union.
  split; intros H_in; contradiction H_not_in_union;
    apply (proj2 (union_spec E F x)); [ left | right ]; exact H_in.
Qed.

Lemma elim_notin_singleton : forall x y,
  ~ In x (singleton y) -> ~ E.eq x y.
Proof.
  intros x y H_not_in H_eq. contradiction H_not_in.
  apply (proj2 (singleton_spec y x)). exact H_eq.
Qed.

End Notin.

End FSetNotin.

Module Type ATOM.

  Parameter atom : Set.

  Parameter atom_fresh_for_list :
    forall (xs : list atom), {x : atom | ~ List.In x xs}.

  Declare Module AtomAsOrderedType : UsualOrderedType with Definition t := atom.

  Parameter eq_atom_dec : forall x y : atom, {x = y} + {x <> y}.

End ATOM.

Module AtomImpl : ATOM.

  Definition atom := nat.

  (* NPeano.Nat works here, but its dependencies are expensive *)
  Module AtomAsOrderedType : UsualOrderedType with Definition t := nat.

    Definition t := nat.

    Definition eq := @Logic.eq t.
    Definition eq_equiv := @eq_equivalence t.
    Definition eq_dec := eq_nat_dec.

    Definition lt := lt.
    Definition lt_strorder := (Build_StrictOrder t lt lt_irrefl lt_trans).

    Lemma lt_compat :
      Proper (eq==>eq==>iff) lt.
    Proof.
      unfold Proper. unfold respectful. intros x y H_x_eq_y x' y' H_x'_eq_y'.
      rewrite H_x_eq_y. rewrite H_x'_eq_y'. split; intro H_lt_y_y'; exact H_lt_y_y'.
    Qed.

    Definition compare := nat_compare.
    Definition compare_spec := nat_compare_spec.

  End AtomAsOrderedType.

  Module AtomAsOrderedTypeFull := OT_to_Full AtomAsOrderedType.

  Lemma max_lt_r : forall x y z,
    x <= z -> x <= max y z.
  Proof.
    intros x y z H_x_le_z.
    assert (z <= max y z) as H_z_le_max_y_z by exact (Max.le_max_r y z).
    assert (x <= max y z) as H_x_le_max_y_z
      by exact (Le.le_trans x z (max y z) H_x_le_z H_z_le_max_y_z).
    exact H_x_le_max_y_z.
  Qed.

  Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, In x xs -> x <= n }.
  Proof.
    induction xs as [ | h xs [b H] ].

    (* case: nil *)
    exists 0. contradiction.

    (* case: cons x xs *)
    exists (max h b).
    intros x H_x_in. simpl in H_x_in.
    destruct H_x_in as [ H_x_eq_h | H_x_in_tail ].

      (* h = x *)
      subst.
      assert (x <= max x b) as H_x_le_max_x_b by exact (Max.le_max_l x b).
      exact H_x_le_max_x_b.

      (* In x xs *)
      assert (x <= b) as H_x_le_b by exact (H x H_x_in_tail).
      assert (x <= max h b) as H_x_le_max_h_b by exact (max_lt_r x h b H_x_le_b).
      exact H_x_le_max_h_b.
  Qed.

  Lemma atom_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ List.In n xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H]. exists (S x).
    intros J. lapply (H (S x)). exact (le_Sn_n x). exact J.
  Qed.

  Definition eq_atom_dec : forall x y : atom, {x = y} + {x <> y} :=
    AtomAsOrderedType.eq_dec.

End AtomImpl.

Export AtomImpl.

Module AtomSet : FiniteSets.S with Module E := AtomAsOrderedType :=
  FiniteSets.Make AtomAsOrderedType.

Notation atoms := AtomSet.F.t.

Import AtomSet.F.

Module AtomSetNotin   := FSetNotin.Notin            AtomSet.F.
Module AtomFacts      := MSetFacts.Facts            AtomSet.F.
Module AtomProperties := MSetProperties.Properties  AtomSet.F.

Notation elim_notin_singleton := AtomSetNotin.elim_notin_singleton.
Notation elim_notin_union     := AtomSetNotin.elim_notin_union.

Notation union_2              := AtomFacts.union_2.
Notation union_3              := AtomFacts.union_3.

Notation empty_union_1        := AtomProperties.empty_union_1.
Notation empty_union_2        := AtomProperties.empty_union_2.
Notation equal_sym            := AtomProperties.equal_sym.
Notation not_in_union         := AtomProperties.not_in_union.
Notation union_assoc          := AtomProperties.union_assoc.

Lemma atom_fresh_for_set : forall L : atoms, { x : atom | ~ In x L }.
Proof.
  intros L. destruct (atom_fresh_for_list (elements L)) as [a H].
  exists a. intros H_in. contradiction H.
  rewrite <- InA_iff_In. apply (proj2 (elements_spec1 L a)). exact H_in.
Qed.

Import AtomSet.F.

Notation Local "[ x ]" := (cons x nil).

Set Implicit Arguments.

Section Definitions.

Variables A B : Type.

Fixpoint dom (E : list (atom * A)) : atoms :=
  match E with
  | nil => empty
  | (x, _) :: E' => union (singleton x) (dom E')
  end.

Fixpoint map (f : A -> B) (E : list (atom * A)) : list (atom * B) :=
  match E with
  | nil => nil
  | (x, V) :: E' => (x, f V) :: map f E'
  end.

Fixpoint get (x : atom) (E : list (atom * A)) : option A :=
  match E with
  | nil => None
  | (y,a) :: E' => if eq_atom_dec x y then Some a else get x E'
  end.

End Definitions.

Unset Implicit Arguments.

Set Implicit Arguments.

Section Relations.

Variable A : Type.

Inductive ok : list (atom * A) -> Prop :=
  | ok_nil :
      ok nil
  | ok_cons : forall (E : list (atom * A)) (x : atom) (a : A),
      ok E -> ~ In x (dom E) -> ok ((x, a) :: E).

Definition binds x b (E : list (atom * A)) :=
  get x E = Some b.

End Relations.

Unset Implicit Arguments.

Section OpProperties.
Variable A B : Type.
Implicit Types E F : list (atom * A).
Implicit Types a b : A.

Lemma nil_concat : forall E,
  nil ++ E = E.
Proof.
  reflexivity.
Qed.

Lemma dom_nil :
  @dom A nil = empty.
Proof.
  reflexivity.
Qed.

Lemma dom_push : forall x a E,
  dom ([(x,a)] ++ E) = union (singleton x) (dom E).
Proof.
  simpl. intros. reflexivity.
Qed.

Lemma dom_concat : forall E F,
  dom (F ++ E) = union (dom F) (dom E).
Proof.
  induction F as [|(x,a) F IH]; simpl.

  apply AtomSet.eq_if_Equal.
  apply equal_sym.
  apply empty_union_1.
  exact empty_spec.

  rewrite IH.
  apply AtomSet.eq_if_Equal.
  apply equal_sym.
  exact (union_assoc (singleton x) (dom F) (dom E)).
Qed.

Lemma cons_concat_assoc : forall x a E F,
   ((x, a) :: E) ++ F = (x, a) :: (E ++ F).
Proof.
  reflexivity.
Qed.

End OpProperties.

Definition singleton_list (A : Type) (x : atom * A) := x :: nil.
Implicit Arguments singleton_list [A].

Lemma cons_concat : forall (A : Type) (E : list (atom * A)) x a,
  (x, a) :: E = singleton_list (x, a) ++ E.
Proof.
  reflexivity.
Qed.

Section OkProperties.
Variable A B : Type.
Implicit Types E F : list (atom * A).
Implicit Types a b : A.

Lemma ok_remove_mid : forall F E G,
  ok (G ++ F ++ E) -> ok (G ++ E).
Proof.
  intros F E G.
  induction G as [|(y,a)]; intros Ok.

    (* nil *)
    induction F as [|(y,a)].

      (* nil *)
      exact Ok.

      (* (y, a) *)
      inversion Ok.  apply IHF.  exact H1.

    (* (y, a) *)
    inversion Ok. simpl. apply ok_cons. apply IHG. exact H1.

    (* ~ In y (dom (G ++ E)) *)
    rewrite (dom_concat A (F ++ E) G) in H3.
    rewrite (dom_concat A E F) in H3.
    rewrite (dom_concat A E G).

    assert (~ In y (dom G) /\ ~ In y (union (dom F) (dom E)))
      as [ H_y_notin_dom_G H_y_notin_dom_F_union_dom_E ]
      by exact (elim_notin_union y (dom G) (union (dom F) (dom E)) H3).

    assert (~ In y (dom F) /\ ~ In y (dom E))
      as [ H_y_notin_dom_F H_y_notin_dom_E ]
      by exact (elim_notin_union y (dom F) (dom E) H_y_notin_dom_F_union_dom_E).

    exact (not_in_union H_y_notin_dom_G H_y_notin_dom_E).
Qed.

Lemma ok_remove_mid_cons : forall x a E G,
  ok (G ++ (x, a) :: E) ->
  ok (G ++ E).
Proof.
  intros x a E G H_ok.
  rewrite (cons_concat A E x a) in H_ok.
  unfold singleton_list in H_ok.
  exact (ok_remove_mid [(x, a)] E G H_ok).
Qed.

End OkProperties.

Section BindsProperties.
Variable A B : Type.
Implicit Types E F : list (atom * A).
Implicit Types a b : A.

Lemma binds_singleton : forall x a,
  binds x a [(x,a)].
Proof.
  intros x a. unfold binds. simpl. destruct (eq_atom_dec x x); intuition.
Qed.

Lemma binds_tail : forall x a E F,
  binds x a E -> ~ In x (dom F) -> binds x a (F ++ E).
Proof.
  unfold binds. induction F as [|(y,b)]; simpl; intro H_get_some_a.

    (* nil *)
    intro H_not_in. exact H_get_some_a.

    (* cons *)
    intro H_x_not_in_y_or_dom_f. destruct (eq_atom_dec x y) as [ H_x_eq_y | H_x_neq_y ].

      (* Equality*)
      rewrite H_x_eq_y in H_x_not_in_y_or_dom_f.
      assert (E.eq y y) as H_y_eq_y by reflexivity.
      assert (In y (singleton y))
        as H_y_in_singleton_y by exact ((proj2 (singleton_spec y y)) H_y_eq_y).
      assert (In y (union (singleton y) (dom F))) as H_y_in_y_union_dom_f
        by exact (@union_2 (singleton y) (dom F) y H_y_in_singleton_y).
      contradiction.

      (* Inequality *)
      assert (~ In x (dom F)) as H_x_notin_dom_f.

        (* ~ In x (dom F) *)
        contradict H_x_not_in_y_or_dom_f.
        apply union_3.
        exact H_x_not_in_y_or_dom_f.

      exact (IHF H_get_some_a H_x_notin_dom_f).
Qed.

Lemma binds_head : forall x a E F,
  binds x a F -> binds x a (F ++ E).
Proof.
  unfold binds. induction F as [|(y,b)]; simpl; intros H.
  discriminate.
  destruct (eq_atom_dec x y); intuition.
Qed.

Lemma binds_concat_inv : forall x a E F,
  binds x a (F ++ E) -> (~ In x (dom F) /\ binds x a E) \/ (binds x a F).
Proof.
  intros x a E F. unfold binds.
  induction F as [|(y,b)]; simpl; intros H.

    (* ~ In x empty /\ get x E = Some a \/ None = Some a *)
    left. apply conj. apply empty_spec. assumption.

    (* ~ In x (union (singleton y) (dom F)) /\ get x E = Some a \/
      (if eq_atom_dec x y then Some b else get x F) = Some a *)
    destruct (eq_atom_dec x y).

      (* ~ In x (union (singleton y) (dom F)) /\ get x E = Some a \/ Some b = Some a *)
      right. assumption.

      (* ~ In x (union (singleton y) (dom F)) /\ get x E = Some a \/ get x F = Some a *)
      destruct (IHF H) as [[? ?] | ?].

        (* get x E = Some a *)
        left. apply conj. apply not_in_union. intro H_x_in_y.
        assert (x = y) by exact ((proj1 (singleton_spec y x)) H_x_in_y).
        contradiction. assumption. assumption.

        (* get x F = Some a *)
        right. assumption.
Qed.

Lemma binds_singleton_inv : forall x y a b,
  binds x a [(y,b)] -> x = y /\ a = b.
Proof.
  unfold binds. simpl. intros. destruct (eq_atom_dec x y).
    split; congruence.
    discriminate.
Qed.

Lemma binds_mid_eq : forall z a b E F,
  binds z a (F ++ [(z,b)] ++ E) -> ok (F ++ [(z,b)] ++ E) -> a = b.
Proof.
  unfold binds. induction F as [|(x,c)]; simpl; intros H Ok.
  destruct (eq_atom_dec z z). congruence. intuition.
  inversion Ok; subst. destruct (eq_atom_dec z x).

  destruct H4. rewrite (cons_concat A E z b). unfold singleton_list.
  rewrite (dom_concat A ([(z, b)] ++ E) F).
  rewrite (dom_push A z b E).

  rewrite e.
  apply union_3.
  apply union_2.
  apply (proj2 (singleton_spec x x)).
  reflexivity.

  exact (IHF H H2).
Qed.

Lemma binds_mid_eq_cons : forall x a b E F,
  binds x a (F ++ (x,b) :: E) ->
  ok (F ++ (x,b) :: E) ->
  a = b.
Proof.
  intros. rewrite (cons_concat A E x b) in *. unfold singleton_list in *.
  apply (binds_mid_eq x a b E F). assumption. assumption.
Qed.

End BindsProperties.

Section AdditionalBindsProperties.
Variable A B : Type.
Implicit Types E F : list (atom * A).
Implicit Types a b : A.

Lemma binds_In : forall a x E,
  binds x a E -> In x (dom E).
Proof.
  induction E as [|(y,b)].
  rewrite dom_nil.
  2: rewrite (cons_concat A E y b); unfold singleton_list; rewrite (dom_push A y b E).
  intros H. 2: intros H.
  inversion H.

  destruct (@binds_concat_inv _ _ _ _ _ H) as [[H_x_notin_dom_y H_binds_E] | H_binds_y].

  assert (In x (dom E)) as H_x_in_dom_E by exact (IHE H_binds_E).
  exact (@union_3 (singleton y) (dom E) x H_x_in_dom_E).

  destruct (@binds_singleton_inv _ _ _ _ _ H_binds_y); subst.
  apply union_2.
  apply (proj2 (singleton_spec y y)).
  reflexivity.
Qed.

Lemma binds_concat_ok : forall x a E F,
  binds x a E -> ok (F ++ E) -> binds x a (F ++ E).
Proof.
  induction F as [|(y,b)]; intros H Ok.
  assumption.

  rewrite (cons_concat A F y b) in *.
  unfold singleton_list in *.
  rewrite <- (app_assoc [(y, b)] F E) in *.
  inversion Ok; subst. destruct (eq_atom_dec x y); subst.

  assert (In y (dom (F ++ E))) by exact (binds_In a y (F ++ E) (IHF H H2)).
  intuition.

  apply binds_tail. apply IHF. assumption. assumption.
  simpl. rewrite (empty_union_2 (singleton y) empty_spec).
  intro H_x_notin_y.
  assert (x = y) by exact ((proj1 (singleton_spec y x)) H_x_notin_y).
  intuition.
Qed.

Lemma binds_weaken : forall x a E F G,
  binds x a (G ++ E) ->
  ok (G ++ F ++ E) ->
  binds x a (G ++ F ++ E).
Proof.
  induction G as [|(y,b)]; intros H Ok.
  apply binds_concat_ok. apply binds_concat_ok. assumption. assumption. assumption.

  rewrite (cons_concat A G y b) in *.
  unfold singleton_list in *.
  rewrite <- (app_assoc [(y, b)] G E) in *.
  rewrite <- (app_assoc [(y, b)] G (F ++ E)) in *.

  inversion Ok; subst.
  destruct (@binds_concat_inv _ _ _ _ _ H)
    as [ [ H_x_notin_dom_y H_binds_G_E ] | H_binds_y ].
  destruct (@binds_concat_inv _ _ _ _ _ H_binds_G_E)
    as [ [ H_x_notin_G H_binds_E ] | H_binds_G ].

  apply binds_tail. apply IHG. apply binds_tail.
  assumption. assumption. assumption. assumption.

  apply binds_tail. apply IHG. apply binds_head. assumption. assumption. assumption.

  destruct (@binds_singleton_inv _ _ _ _ _ H_binds_y); subst.
  apply binds_head. apply binds_singleton.
Qed.

Lemma binds_remove_mid : forall x y a b F G,
  binds x a (F ++ [(y,b)] ++ G) ->
  x <> y ->
  binds x a (F ++ G).
Proof.
  intros x y a b F G H J.

  destruct (@binds_concat_inv _ _ _ _ _ H)
    as [ [ H_x_notin_dom_F H_binds_y_G ] | H_binds_F ].
  destruct (@binds_concat_inv _ _ _ _ _ H_binds_y_G)
    as [ [ H_x_notin_dom_y H_binds_G ] | H_binds_y ].

  apply binds_tail. assumption. assumption.

  destruct (@binds_singleton_inv _ _ _ _ _ H_binds_y). intuition.

  apply binds_head. assumption.
Qed.

Lemma binds_remove_mid_cons : forall x y a b E G,
  binds x a (G ++ (y, b) :: E) ->
  x <> y ->
  binds x a (G ++ E).
Proof.
  intros. exact (binds_remove_mid x y a b G E H H0).
Qed.

End AdditionalBindsProperties.

Notation "x == y" :=
  (eq_atom_dec x y) (at level 67) : metatheory_scope.
Notation "i === j" :=
  (Peano_dec.eq_nat_dec i j) (at level 67) : metatheory_scope.

Notation "E `union` F" :=
  (AtomSet.F.union E F)
  (at level 69, right associativity, format "E  `union`  '/' F")
  : set_scope.
Notation "x `in` E" :=
  (AtomSet.F.In x E) (at level 69) : set_scope.
Notation "x `notin` E" :=
  (~ AtomSet.F.In x E) (at level 69) : set_scope.

Notation "{}" :=
  (AtomSet.F.empty) : metatheory_scope.

Notation singleton := (AtomSet.F.singleton).

Open Scope metatheory_scope.
Open Scope set_scope.

(*
  Terms use the locally nameless representation, in which bound variables are identified
  by the number of abstractions separating them from their binder.

  While convenient, it allows for "unbound" bound variables such as
  `(term_bound_variable 1)`.  Terms that are "closed" have no such unbound variables.
*)
Inductive term : Set :=
  | term_bound_variable : nat -> term
  | term_free_variable : atom -> term
  | term_abstraction : term -> term
  | term_application : term -> term -> term.

(* nats can promote to term_bound_variable. *)
Coercion term_bound_variable : nat >-> term.

(* atoms can promote to term_free_variable. *)
Coercion term_free_variable : atom >-> term.

(*
  Replace a bound variable with a term.
*)
Fixpoint open
    (bound : nat)
    (replacement context : term)
    {struct context} : term :=
  match context with
    | term_bound_variable index => if bound === index then replacement else index

    | term_free_variable name => name

    | term_abstraction body => term_abstraction (open (S bound) replacement body)

    | term_application
      function
      argument =>
      term_application
        (open bound replacement function)
        (open bound replacement argument)
  end.

(* "replacement >> context" opens context at index 0. *)
Notation "replacement >> context" := (open 0 replacement context) (at level 67).

(*
  Closure is the absence of "unbound" bound variables.
*)
Inductive closed : term -> Prop :=
  | closed_free_variable : forall (name : atom), closed name

  | closed_abstraction :
    forall (stale : atoms)
    (body : term),
    (forall (name : atom), name `notin` stale -> closed (name >> body)) ->
    closed (term_abstraction body)

  | closed_application :
    forall (function argument : term),
    closed function ->
    closed argument ->
    closed (term_application function argument).

(*
  Replace a free variable with a term.
*)
Fixpoint substitute
    (free : atom)
    (replacement context : term)
    {struct context} : term :=
  match context with
    | term_bound_variable index => index

    | term_free_variable name => if free == name then replacement else name

    | term_abstraction body => term_abstraction (substitute free replacement body)

    | term_application
      function
      argument =>
      term_application
        (substitute free replacement function)
        (substitute free replacement argument)
  end.

(* "name ~> replacement" curries substitute. *)
Notation "name ~> replacement" := (substitute name replacement) (at level 68).

(*
  Identify the free variables in a term.
*)
Fixpoint free_variables (the_term : term) {struct the_term} : atoms :=
  match the_term with
    | term_bound_variable index => {}

    | term_free_variable name => singleton name

    | term_abstraction body => free_variables body

    | term_application
      function
      argument =>
      (free_variables function) `union` (free_variables argument)
  end.

(*
  If a variable does not appear free in a term, substituting for that variable does
  nothing.
*)
Lemma substituting_absent_variable_does_nothing :
  forall (absent : atom)
  (context : term),
  absent `notin` free_variables context ->
  forall (replacement : term),
  (absent ~> replacement) context = context.
Proof.
  intros absent context H_absent replacement.
  induction context as
    [ index
    | name
    | body IH_body
    | function IH_function argument IH_argument ].

    (* term_bound_variable *)
    simpl. reflexivity.

    (* term_free_variable *)
    simpl. destruct (absent == name) as [ H_eq | H_not_eq ].

      (* Equality *)
      subst name. simpl free_variables in H_absent.
      apply (elim_notin_singleton absent absent) in H_absent. intuition.

      (* Inequality *)
      reflexivity.

    (* term_abstraction *)
    simpl. simpl free_variables in H_absent. rewrite (IH_body H_absent). reflexivity.

    (* term_application *)
    simpl. simpl free_variables in H_absent.
    destruct (elim_notin_union absent
      (free_variables function) (free_variables argument) H_absent)
      as [ H_absent_function H_absent_argument ].
    rewrite (IH_function H_absent_function).
    rewrite (IH_argument H_absent_argument).
    reflexivity.
Qed.

(*
  Opening an absent index moves past other openings.
*)
Lemma opening_absence_moves_past_open :
  forall (unused replacement context : term)
  (absent bound : nat),
  absent <> bound ->
  open absent unused (open bound replacement context) = open bound replacement context ->
  open absent unused context = context.
Proof.
  intros unused replacement.
  induction context as
    [ index
    | name
    | body IH_body
    | function IH_function argument IH_argument ];
  intros absent bound H_neq H_absence; simpl; simpl in H_absence.

    (* term_bound_variable *)
    destruct (index === bound) as [ H_eq_index_bound | H_neq_index_bound ].

      (* Equality *)
      destruct (absent === index) as [ H_eq_absent_index | H_neq_absent_index ].

        (* Equality *)
        rewrite H_eq_index_bound in H_eq_absent_index. intuition.

        (* Inequality *)
        reflexivity.

      (* Inequality *)
      destruct (bound === index) as [ H_eq_bound_index | H_neq_bound_index ].

        (* Equality *)
        rewrite H_eq_bound_index in H_neq_index_bound. intuition.

        (* Inequality *)
        exact H_absence.

    (* term_free_variable *)
    reflexivity.

    (* term_abstraction *)
    inversion H_absence as [ H_absence_body ]. f_equal.
    apply (IH_body (S absent) (S bound)).

      (* S absent <> S bound *)
      injection.
      exact H_neq.

      (* open (S absent) unused (open (S bound) replacement body) =
        open (S bound) replacement body *)
      exact H_absence_body.

    (* term_application *)
    inversion H_absence as [ [ H_absence_function H_absence_argument ] ].
    rewrite (IH_function absent bound H_neq H_absence_function).
    rewrite (IH_argument absent bound H_neq H_absence_argument).
    reflexivity.
Qed.

(*
  If a term is closed, opening it at any index does nothing.
*)
Lemma opening_closed_term_does_nothing :
  forall (context : term),
  closed context ->
  forall (index : nat)
  (replacement : term),
  open index replacement context = context.
Proof.
  intros context H_closed index replacement.
  generalize dependent index.
  induction H_closed as
    [ name
    | stale body H_body_closed_except_stale IH_abstraction
    | function argument H_function_closed IH_function H_argument_closed IH_argument ];
  intro index; simpl.

    (* closed_free_variable *)
    reflexivity.

    (* closed_abstraction *)
    f_equal.
    destruct (atom_fresh_for_set stale) as [fresh H_fresh_not_in_stale].
    apply (opening_absence_moves_past_open replacement fresh body (S index) 0).

      (* S index <> 0 *)
      discriminate.

      (* open (S index) replacement (fresh >> body) = fresh >> body *)
      exact (IH_abstraction fresh H_fresh_not_in_stale (S index)).

    (* closed_application *)
    rewrite (IH_function index).
    rewrite (IH_argument index).
    reflexivity.
Qed.

(*
  Substitution distributes over opening.
*)
Lemma substitute_distributes_over_open :
  forall (context substituted opened : term)
  (free : atom)
  (bound : nat),
  closed substituted ->
  (free ~> substituted) (open bound opened context) =
    (open bound ((free ~> substituted) opened) ((free ~> substituted) context)).
Proof.
  induction context as
    [ index
    | name
    | body IH_body
    | function IH_function argument IH_argument ];
  intros substituted opened free bound H_closed;
  simpl.

    (* term_bound_variable *)
    destruct (bound === index) as [ H_eq_bound_index | H_neq_bound_index ];
    reflexivity.

    (* term_free_variable *)
    destruct (free == name) as [ H_eq_free_name | H_neq_free_name ].

      (* Equality *)
      symmetry.
      exact (opening_closed_term_does_nothing substituted H_closed
        bound ((free ~> substituted) opened)).

      (* Inequality *)
      reflexivity.

    (* term_abstraction *)
    f_equal.
    exact (IH_body substituted opened free (S bound) H_closed).

    (* term_application *)
    rewrite (IH_function substituted opened free bound H_closed).
    rewrite (IH_argument substituted opened free bound H_closed).
    reflexivity.
Qed.

(*
  Substituting a closed term commutes with opening a free variable.
*)
Lemma substituting_closed_term_commutes_with_opening_free_variable :
  forall (free opened : atom)
  (substituted context : term),
  free <> opened ->
  closed substituted ->
  opened >> ((free ~> substituted) context) = (free ~> substituted) (opened >> context).
Proof.
  intros free opened substituted context H_neq H_closed.
  symmetry.
  rewrite (substitute_distributes_over_open context substituted opened free 0 H_closed).
  simpl.
  destruct (free == opened) as [ H_eq_free_opened | H_neq_free_opened ].

    (* Equality *)
    intuition.

    (* Inequality *)
    reflexivity.
Qed.

(*
  The simply-typed lamba calculus has two kinds: base types and arrow types.
*)
Inductive type : Set :=
  | type_base : type
  | type_arrow : type -> type -> type.

(*
  Environments associate types with names.

  They allow for a name to be bound more than once, which is not allowed. Environments
  that are "ok" do not have multiple bindings.
*)
Notation environment := (list (atom * type)).

(*
  The typing relation.
*)
Inductive typing : environment -> term -> type -> Prop :=
  | typing_free_variable :
    forall (the_environment : environment)
    (free : atom)
    (the_type : type),
    ok the_environment ->
    binds free the_type the_environment ->
    typing the_environment free the_type

  | typing_abstraction :
    forall (stale : atoms)
    (the_environment : environment)
    (body : term)
    (argument_type application_type : type),
    (forall
      (fresh : atom),
      fresh `notin` stale ->
      typing ((fresh, argument_type) :: the_environment)
        (fresh >> body) application_type) ->
    typing the_environment (term_abstraction body)
      (type_arrow argument_type application_type)

  | typing_application :
    forall (the_environment : environment)
    (function argument : term)
    (argument_type application_type : type),
    typing the_environment function (type_arrow argument_type application_type) ->
    typing the_environment argument argument_type ->
    typing the_environment (term_application function argument) application_type.

(*
  If a term is typable then it is closed.
*)
Lemma typing_implies_closure :
  forall (the_environment : environment)
  (the_term : term)
  (the_type : type),
  typing the_environment the_term the_type ->
  closed the_term.
Proof.
  intros given_environment the_term the_type H_typing.
  induction H_typing as
    [ the_environment name the_type H_environment_ok H_binds

    | stale the_environment body argument_type application_type H_opened_typing
      IH_abstraction

    | the_environment function argument argument_type application_type
        H_function_typing IH_function_typing H_argument_typing IH_argument_typing ].

    (* typing_free_variable *)
    exact (closed_free_variable name).

    (* typing_abstraction *)
    exact (closed_abstraction stale body IH_abstraction).

    (* typing_application *)
    exact (closed_application function argument IH_function_typing IH_argument_typing).
Qed.

(*
  If a term has a type in an environment, then it has the same type in
  any environment that inserts new entries into the middle of the original.
*)
Lemma internally_expanding_environments_preserves_typing :
  forall (prefix expansion suffix : environment)
  (the_term : term)
  (the_type : type),
  typing (prefix ++ suffix) the_term the_type ->
  ok (prefix ++ expansion ++ suffix) ->
  typing (prefix ++ expansion ++ suffix) the_term the_type.
Proof.
  intros prefix expansion suffix the_term the_type.
  remember (prefix ++ suffix) as prefix_suffix_environment eqn:H_prefix_suffix.
  intro H_typing.
  generalize dependent prefix.
  induction H_typing as
    [ the_environment free the_type H_environment_ok H_binds

    | stale the_environment body argument_type application_type H_opened_typing
      IH_abstraction

    | the_environment function argument argument_type application_type
        H_function_typing IH_function_typing H_argument_typing IH_argument_typing ];
  intros prefix H_extended_environment H_extended_environment_ok.

    (* typing_free_variable *)
    apply (typing_free_variable (prefix ++ expansion ++ suffix)
      free the_type H_extended_environment_ok).
    rewrite H_extended_environment in H_binds.
    exact (binds_weaken type free the_type suffix expansion prefix H_binds
      H_extended_environment_ok).

    (* typing_abstraction *)
    apply (typing_abstraction
      (stale `union` dom (prefix ++ expansion ++ suffix))
      (prefix ++ expansion ++ suffix) body argument_type application_type).
    intros fresh H_fresh_not_in_stale_union_dom.
    destruct (elim_notin_union fresh stale (dom (prefix ++ expansion ++ suffix))
      H_fresh_not_in_stale_union_dom) as [ H_fresh_notin_stale H_fresh_notin_dom ].
    apply (IH_abstraction fresh H_fresh_notin_stale ((fresh, argument_type) :: prefix)).

      (* (fresh, argument_type) :: the_environment =
        ((fresh, argument_type) :: prefix) ++ suffix *)
      symmetry.
      rewrite H_extended_environment.
      exact (cons_concat_assoc type fresh argument_type prefix suffix).

      (* ok (((fresh, argument_type) :: prefix) ++ expansion ++ suffix) *)
      rewrite (cons_concat_assoc type fresh argument_type prefix (expansion ++ suffix)).
      exact (@ok_cons type (prefix ++ expansion ++ suffix) fresh argument_type
        H_extended_environment_ok H_fresh_notin_dom).

    (* typing_application *)
    exact (typing_application
      (prefix ++ expansion ++ suffix) function argument argument_type application_type
      (IH_function_typing prefix H_extended_environment H_extended_environment_ok)
      (IH_argument_typing prefix H_extended_environment H_extended_environment_ok)).
Qed.

(*
  If an expression is typable in some environment,
  then it is typable in any valid extension of that environment.
*)
Lemma extending_environments_preserves_typing :
  forall (extension the_environment : environment)
  (the_term : term)
  (the_type : type),
  typing the_environment the_term the_type ->
  ok (extension ++ the_environment) ->
  typing (extension ++ the_environment) the_term the_type.
Proof.
  intros extension the_environment the_term the_type H_typing H_ok.
  rewrite <- (nil_concat type (extension ++ the_environment)).
  rewrite <- (nil_concat type the_environment) in H_typing.
  rewrite <- (nil_concat type (extension ++ the_environment)) in H_ok.
  exact (internally_expanding_environments_preserves_typing nil extension
    the_environment the_term the_type H_typing H_ok).
Qed.

(*
  Substitution preserves typing for all bindings in the environment.
*)
Lemma substitution_preserves_typing_for_all_bindings :
  forall (prefix suffix : environment)
  (context replacement : term)
  (replacement_type result_type : type)
  (free : atom),
  typing (prefix ++ (free, replacement_type) :: suffix) context result_type ->
  typing suffix replacement replacement_type ->
  typing (prefix ++ suffix) ((free ~> replacement) context) result_type.
Proof.
  intros prefix suffix context replacement replacement_type result_type free.
  remember (prefix ++ (free, replacement_type) :: suffix)
    as prefix_suffix_environment eqn:H_prefix_suffix.
  intros H_result_typing H_replacement_typing.
  generalize dependent prefix.
  induction H_result_typing as
    [ the_environment name the_type H_environment_ok H_binds

    | stale the_environment body argument_type application_type H_opened_typing
      IH_abstraction

    | the_environment function argument argument_type application_type
        H_function_typing IH_function_typing H_argument_typing IH_argument_typing ];
  intros prefix H_extended_environment;
  simpl.

    (* typing_free_variable *)
    rewrite H_extended_environment in H_environment_ok.
    rewrite H_extended_environment in H_binds.
    assert (ok (prefix ++ suffix)) as H_ok_prefix_suffix by exact
      (ok_remove_mid_cons type free replacement_type suffix prefix H_environment_ok).
    destruct (free == name) as [ H_eq_free_name | H_neq_free_name ].

      (* Equality *)
      rewrite H_eq_free_name in H_environment_ok.
      rewrite H_eq_free_name in H_binds.
      assert (the_type = replacement_type) as H_type_eq_replacement_type by exact
        (binds_mid_eq_cons type name the_type replacement_type suffix prefix H_binds
        H_environment_ok).
      rewrite H_type_eq_replacement_type.
      exact (extending_environments_preserves_typing prefix suffix replacement
        replacement_type H_replacement_typing H_ok_prefix_suffix).

      (* Inequality *)
      assert (name <> free) as H_neq_name_free by exact (not_eq_sym H_neq_free_name).
      assert (binds name the_type (prefix ++ suffix)) as H_binds_prefix_suffix
        by exact (binds_remove_mid_cons type name free the_type replacement_type suffix
        prefix H_binds H_neq_name_free).
      exact (typing_free_variable (prefix ++ suffix) name the_type H_ok_prefix_suffix
        H_binds_prefix_suffix).

    (* typing_abstraction *)
    apply (typing_abstraction (stale `union` (singleton free)) (prefix ++ suffix)
      ((free ~> replacement) body) argument_type application_type).
    intros fresh H_fresh_notin_stale_or_free.
    destruct (elim_notin_union fresh stale (singleton free) H_fresh_notin_stale_or_free)
      as [ H_fresh_notin_stale H_fresh_notin_singleton_free ].
    assert (free <> fresh) as H_free_neq_fresh by
      exact (not_eq_sym (elim_notin_singleton fresh free H_fresh_notin_singleton_free)).
    assert (closed replacement) as H_closed_replacement by exact (typing_implies_closure
      suffix replacement replacement_type H_replacement_typing).
    rewrite (substituting_closed_term_commutes_with_opening_free_variable free fresh
      replacement body H_free_neq_fresh H_closed_replacement).
    rewrite <- (cons_concat_assoc type fresh argument_type prefix suffix).
    apply (IH_abstraction fresh H_fresh_notin_stale ((fresh, argument_type) :: prefix)).
    rewrite H_extended_environment.
    symmetry.
    exact (cons_concat_assoc type fresh argument_type prefix
      ((free, replacement_type) :: suffix)).

    (* typing_application *)
    exact (typing_application (prefix ++ suffix)
      ((free ~> replacement) function) ((free ~> replacement) argument)
      argument_type application_type
      (IH_function_typing prefix H_extended_environment)
      (IH_argument_typing prefix H_extended_environment)).
Qed.

(*
  Substitution preserves typing for the first binding in the environment.
*)
Lemma substitution_preserves_typing :
  forall (the_environment : environment)
  (context replacement : term)
  (replacement_type result_type : type)
  (free : atom),
  typing ((free, replacement_type) :: the_environment) context result_type ->
  typing the_environment replacement replacement_type ->
  typing the_environment ((free ~> replacement) context) result_type.
Proof.
  intros the_environment context replacement replacement_type result_type free
    H_result_typing H_replacement_typing.
  rewrite <- (nil_concat type the_environment).
  rewrite <- (nil_concat type ((free, replacement_type) :: the_environment))
    in H_result_typing.
  exact (substitution_preserves_typing_for_all_bindings nil the_environment context
    replacement replacement_type result_type free H_result_typing H_replacement_typing).
Qed.

(*
  Values are terms that cannot be evaluated further.
*)
Inductive value : term -> Prop :=
  | value_abstraction :
    forall (body : term),
    closed (term_abstraction body) ->
    value (term_abstraction body).

(*
  The small-step call-by-value evaluation relation.
*)
Inductive evaluation : term -> term -> Prop :=
  | evaluation_beta :
    forall (body argument : term),
    closed (term_abstraction body) ->
    value (argument) ->
    evaluation
      (term_application (term_abstraction body) argument)
      (argument >> body)

  | evaluation_function :
    forall (evaluable evaluated argument : term),
    closed argument ->
    evaluation evaluable evaluated ->
    evaluation
      (term_application evaluable argument)
      (term_application evaluated argument)

  | evaluation_argument :
    forall (function evaluable evaluated : term),
    value function ->
    evaluation evaluable evaluated ->
    evaluation
      (term_application function evaluable)
      (term_application function evaluated).

(*
  Opening a term is equivalent to opening a fresh variable and substituting it.
*)
Lemma opening_is_opening_fresh_then_substituting :
  forall (fresh : atom)
  (replacement context : term),
  fresh `notin` (free_variables context) ->
  closed replacement ->
  (replacement >> context) = (fresh ~> replacement) (fresh >> context).
Proof.
  intros fresh replacement context H_fresh_notin_free_variables H_closed_replacement.
  rewrite (substitute_distributes_over_open context replacement fresh fresh 0
    H_closed_replacement).
  simpl.
  destruct (fresh == fresh) as [ H_fresh_eq_fresh | H_fresh_neq_fresh ].

    (* Equality *)
    rewrite (substituting_absent_variable_does_nothing fresh context
      H_fresh_notin_free_variables replacement).
    reflexivity.

    (* Inequality *)
    intuition.
Qed.

(*
  Evaluation preserves typing.
*)
Lemma preservation :
  forall (the_environment : environment)
  (evaluable evaluated : term)
  (the_type : type),
  typing the_environment evaluable the_type ->
  evaluation evaluable evaluated ->
  typing the_environment evaluated the_type.
Proof.
  intros the_environment evaluable evaluated the_type H_typing.
  generalize dependent evaluated.
  induction H_typing as
    [ the_environment name the_type H_environment_ok H_binds

    | stale the_environment body argument_type application_type H_opened_typing
      IH_abstraction

    | the_environment function argument argument_type application_type
        H_function_typing IH_function_typing H_argument_typing IH_argument_typing ];
  intros evaluated H_evaluation.

    (* typing_free_variable *)
    inversion H_evaluation.

    (* typing_abstraction *)
    inversion H_evaluation.

    (* typing_application *)
    inversion H_evaluation as
      [ body passed_argument H_abstraction_closed H_argument_value
        [ H_abstraction_eq_function H_passed_argument_eq_argument ]
        H_opened_body_eq_evaluated

      | function_evaluable function_evaluated passed_argument H_argument_closed
        H_function_evaluation
        [ H_function_evaluable_eq_function H_passed_argument_eq_argument ]
        H_application_eq_evaluated

      | passed_function argument_evaluable argument_evaluated H_function_value
        H_argument_evaluation
        [ H_passed_function_eq_function H_argument_evaluable_eq_argument ]
        H_application_eq_evaluated ];
    subst.

      (* evaluation_beta *)
      inversion H_function_typing as
        [ function_environment name the_type H_environment_ok H_binds

        | stale function_environment function_body function_argument_type
          function_application_type H_opened_typing IH_abstraction

        | function_environment function function_argument function_argument_type
          function_application_type H_function_function_typing
          IH_function_function_typing H_function_argument_typing
          IH_function_argument_typing ];
      subst.
      destruct (atom_fresh_for_set (stale `union` free_variables body))
        as [fresh H_fresh_notin_stale_union_free_variables_body].
      destruct (elim_notin_union fresh stale (free_variables body)
        H_fresh_notin_stale_union_free_variables_body)
        as [ H_fresh_notin_stale H_fresh_notin_free_variables_body ].
      rewrite (opening_is_opening_fresh_then_substituting fresh argument body
        H_fresh_notin_free_variables_body (typing_implies_closure the_environment
        argument argument_type H_argument_typing)).
      exact (substitution_preserves_typing the_environment (fresh >> body) argument
        argument_type application_type fresh (H_opened_typing fresh H_fresh_notin_stale)
        H_argument_typing).

      (* evaluation_function *)
      exact (typing_application the_environment function_evaluated argument
        argument_type application_type
        (IH_function_typing function_evaluated H_function_evaluation)
        H_argument_typing).

      (* evaluation_argument *)
      exact (typing_application the_environment function argument_evaluated
        argument_type application_type
        H_function_typing
        (IH_argument_typing argument_evaluated H_argument_evaluation)).
Qed.

(*
  Typable terms are values or can be evaluated further.
*)
Lemma progress :
  forall (the_term : term)
  (the_type : type),
  typing nil the_term the_type ->
  value the_term \/ exists (evaluated : term), evaluation the_term evaluated.
Proof.
  intros the_term the_type.
  remember (nil : environment) as the_environment eqn:H_the_environment_nil.
  intro H_typing.
  assert (typing the_environment the_term the_type) as H_typing_copy by exact H_typing.
  induction H_typing_copy as
    [ the_environment name the_type H_environment_ok H_binds

    | stale the_environment body argument_type application_type H_opened_typing
      IH_abstraction

    | the_environment function argument argument_type application_type
        H_function_typing IH_function_typing H_argument_typing IH_argument_typing ];
  subst.

      (* typing_free_variable *)
      inversion H_binds.

      (* typing_abstraction *)
      left.
      apply (value_abstraction body).
      exact (typing_implies_closure nil (term_abstraction body)
        (type_arrow argument_type application_type) H_typing).

      (* typing_application *)
      right.
      assert ((nil : environment) = (nil : environment)) as H_nil_eq_nil by reflexivity.
      destruct (IH_function_typing H_nil_eq_nil H_function_typing) as
        [ H_function_value
        | [ function_evaluated H_function_evaluation ] ].

        (* value function *)
        destruct (IH_argument_typing H_nil_eq_nil H_argument_typing) as
          [ H_argument_value
          | [ argument_evaluated H_argument_evaluation ] ].

          (* value argument *)
          inversion H_function_value
            as [ body H_body_closed H_abstraction_body_eq_function ].
          exists (argument >> body).
          exact (evaluation_beta body argument H_body_closed H_argument_value).

          (* evaluation argument argument_evaluated *)
          exists (term_application function argument_evaluated).
          exact (evaluation_argument function argument argument_evaluated
            H_function_value H_argument_evaluation).

        (* evaluation function function_evaluated *)
        exists (term_application function_evaluated argument).
        assert (closed argument) as H_argument_closed by
          exact (typing_implies_closure nil argument argument_type H_argument_typing).
        exact (evaluation_function function function_evaluated argument
          H_argument_closed H_function_evaluation).
Qed.
