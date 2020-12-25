Require Export arithmetic.

Definition ℤ := (ambient_set _ 0).

Definition ℤ0 := {z in ℤ × ℤ | (proj2 ℤ ℤ z) ≠ value ℤ 0}.

Definition rational_relation :=
  {z in ℤ0 × ℤ0 | ∃ a b c d : Z,
     b ≠ 0 ∧ d ≠ 0 ∧ z = ((value ℤ a, value ℤ b), (value ℤ c, value ℤ d)) ∧ 
     a * d = b * c}.

Theorem rational_equivalence : is_equivalence ℤ0 rational_relation.
Proof.
  repeat split; unfold rational_relation in *.
  - intros a H.
    apply Specify_classification.
    split; try apply Product_classification; eauto.
    apply Specify_classification in H as [H H0].
    apply Product_classification in H as [x [y [H1 [H2 H3]]]].
    subst; simpl.
    unfold proj2 in H0.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description.
    + destruct a as [H3 [H4 H5]].
      apply Ordered_pair_iff in H5 as [H5 H6].
      subst.
      exists (mkSet ℤ x0 H1), (mkSet ℤ x1 H2), (mkSet ℤ x0 H1), (mkSet ℤ x1 H2).
      simpl.
      repeat split; try ring; contradict H0; now rewrite <-H0.
    + contradiction n.
      apply Product_classification; eauto.
  - intros x y H H0 H1.
    rewrite Specify_classification in *.
    destruct H1 as [H1 [a [b [c [d [H2 [H3 [H4 H5]]]]]]]].
    split; try apply Product_classification; eauto.
    exists c, d, a ,b.
    repeat split; auto; try ring [H5].
    repeat rewrite Ordered_pair_iff in *.
    intuition.
  - intros x y z H H0 H1 H2 H3.
    rewrite Specify_classification in *.
    destruct H2 as [H2 [a [b [c [d [H4 [H5 [H6 H7]]]]]]]],
                   H3 as [H3 [a' [b' [c' [d' [H8 [H9 [H10 H11]]]]]]]].
    split; try apply Product_classification; eauto.
    exists a, b, c', d'.
    repeat split; auto; repeat rewrite Ordered_pair_iff in *; intuition;
      subst; rewrite Ordered_pair_iff in *; intuition.
    apply set_proj_injective in H10.
    apply set_proj_injective in H12.
    subst.
    apply (cancellation_mul_l b'); auto.
    ring [H7 H11].
Qed.

Definition Q := elts (ℤ0 / rational_relation).

Delimit Scope Q_scope with Q.
Open Scope Q_scope.
Bind Scope Q_scope with Q.

Definition embed : Z → Z → Q.
Proof.
  intros a b.
  destruct (excluded_middle_informative (b = 0)).
  - assert (((value ℤ 0), (value ℤ 1)) ∈ ℤ0) as H.
    { apply Specify_classification.
      split.
      + apply Product_classification.
        eauto using in_set.
      + unfold proj2.
        destruct excluded_middle_informative.
        repeat destruct constructive_indefinite_description.
        * destruct a0 as [H [H0 H1]].
          apply Ordered_pair_iff in H1 as [H1 H2].
          subst.
          intros H1.
          assert (0 = 1) as H2 by eauto using set_proj_injective.
          contradiction (lt_irrefl 0).
          rewrite H2 at 2.
          apply zero_lt_1.
        * contradiction n.
          apply Product_classification.
          eauto using in_set. }
    exact (quotient_map ℤ0 rational_relation
                        (mkSet ℤ0 (value ℤ 0, value ℤ 1) H)).
  - destruct a as [_ a' A], b as [_ b' B].
    assert ((a', b') ∈ ℤ0) as H.
    { apply Specify_classification.
      split.
      + apply Product_classification; eauto.
      + contradict n.
        unfold proj2 in *.
        destruct excluded_middle_informative.
        * repeat destruct constructive_indefinite_description.
          destruct a as [H [H0 H1]].
          apply Ordered_pair_iff in H1 as [H1 H2].
          subst.
          now apply set_proj_injective.
        * contradict n0.
          apply Product_classification; eauto. }
    exact (quotient_map ℤ0 rational_relation (mkSet ℤ0 (a', b') H)).
Defined.

Infix "/" := embed : Q_scope.

Theorem Qlift : ∀ q, ∃ a b, b ≠ 0 ∧ a / b = q.
Proof.
  intros q.
  destruct (quotient_lift _ _ q) as [y H].
  destruct (unique_set_element _ y) as [x [[H0 H1] H2]].
  apply Specify_classification in H0 as [H0 H3].
  apply Product_classification in H0 as [a [b [H0 [H4 H5]]]].
  subst.
  exists (mkSet _ _ H0), (mkSet _ _ H4).
  set (a' := {| value := a; in_set := H0 |}).
  set (b' := {| value := b; in_set := H4 |}).
  assert (b' ≠ 0) as H5.
  { contradict H3.
    unfold proj2.
    destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description.
    - destruct a0 as [H5 [H6 H7]].
      apply Ordered_pair_iff in H7 as [H7 H8].
      subst.
      unfold b' in H3.
      now rewrite <-H3.
    - contradict n.
      apply Product_classification; eauto. }
  split; auto.
  apply set_proj_injective.
  rewrite quotient_image, H1.
  unfold embed; destruct excluded_middle_informative; simpl; intuition.
Qed.

Theorem Qequiv : ∀ a b c d, b ≠ 0 → d ≠ 0 → a / b = c / d ↔ a * d = b * c.
Proof.
  intros [_ a A] [_ b B] [_ c C] [_ d D] H H0.
  split; intros H1.
  - unfold embed in H1.
    destruct excluded_middle_informative; try now contradiction.
    symmetry in H1.
    destruct excluded_middle_informative; try now contradiction.
    apply quotient_wf in H1; auto using rational_equivalence.
    simpl in *.
    apply Specify_classification in H1
      as [H1 [c' [d' [a' [b' [H2 [H3 [H4 H5]]]]]]]].
    repeat rewrite Ordered_pair_iff in *.
    intuition.
    subst.
    replace {| in_set := A |} with a'; replace {| in_set := B |} with b';
      replace {| in_set := C |} with c'; replace {| in_set := D |} with d';
        try (now apply set_proj_injective); ring [H5].
  - unfold embed.
    destruct excluded_middle_informative; try now contradiction.
    symmetry.
    destruct excluded_middle_informative; try now contradiction.
    apply quotient_wf; auto using rational_equivalence.
    simpl.
    apply Specify_classification.
    split.
    + apply Product_classification.
      exists (c, d), (a, b).
      repeat split.
      * apply Specify_classification.
        split; try apply Product_classification; eauto.
        unfold proj2.
        destruct excluded_middle_informative;
          try (contradict n1; apply Product_classification; eauto).
        repeat destruct constructive_indefinite_description.
        destruct a0 as [H2 [H3 H4]].
        apply Ordered_pair_iff in H4 as [H4 H5].
        contradict n0.
        subst.
        now apply set_proj_injective.
      * apply Specify_classification.
        split; try apply Product_classification; eauto.
        unfold proj2.
        destruct excluded_middle_informative;
          try (contradict n1; apply Product_classification; eauto).
        repeat destruct constructive_indefinite_description.
        destruct a0 as [H2 [H3 H4]].
        apply Ordered_pair_iff in H4 as [H4 H5].
        contradict n.
        subst.
        now apply set_proj_injective.
    + exists {| in_set := C |}, {| in_set := D |},
      {| in_set := A |}, {| in_set := B |}.
      repeat split; auto.
      ring [H1].
Qed.

Definition IZQ a := a / 1.
Definition zero := 0 / 1.
Definition one := 1 / 1.

Notation "0" := zero : Q_scope.
Notation "1" := zero : Q_scope.
