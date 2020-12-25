Require Export arithmetic Field.

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
          contradiction zero_ne_1.
          now apply set_proj_injective.
        * contradiction n.
          apply Product_classification; eauto using in_set. }
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
      assert (∀ e f (F : f ∈ ℤ), e ∈ ℤ → {| in_set := F |} ≠ 0 → (e, f) ∈ ℤ0);
        eauto.
      intros e f F E H2.
      apply Specify_classification.
      split; try apply Product_classification; eauto.
      unfold proj2.
      destruct excluded_middle_informative;
        try (contradict n1; apply Product_classification; eauto).
      repeat destruct constructive_indefinite_description.
      destruct a0 as [H3 [H4 H5]].
      apply Ordered_pair_iff in H5 as [H6 H7].
      contradict H2.
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
Notation "1" := one : Q_scope.

Definition add : Q → Q → Q.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (Qlift x)) as [a e].
  destruct (constructive_indefinite_description _ e) as [b [e0 e1]].
  destruct (constructive_indefinite_description _ (Qlift y)) as [c e2].
  destruct (constructive_indefinite_description _ e2) as [d [e3 e4]].
  exact ((a * d + c * b) / (b * d)).
Defined.

Definition mul : Q → Q → Q.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (Qlift x)) as [a e].
  destruct (constructive_indefinite_description _ e) as [b [e0 e1]].
  destruct (constructive_indefinite_description _ (Qlift y)) as [c e2].
  destruct (constructive_indefinite_description _ e2) as [d [e3 e4]].
  exact ((a * c) / (b * d)).
Defined.

Definition neg : Q → Q.
Proof.
  intros x.
  destruct (constructive_indefinite_description _ (Qlift x)) as [a e].
  destruct (constructive_indefinite_description _ e) as [b [e0 e1]].
  exact (-a / b).
Defined.

Definition inv : Q → Q.
Proof.
  intros x.
  destruct (constructive_indefinite_description _ (Qlift x)) as [a e].
  destruct (constructive_indefinite_description _ e) as [b [e0 e1]].
  exact (b / a).
Defined.

Infix "+" := add : Q_scope.
Infix "*" := mul : Q_scope.
Notation "- a" := (neg a) : Q_scope.
Notation "/ a" := (inv a) : Q_scope.

Definition sub a b := a + -b.

Check mk_rt 0 1 add mul sub neg eq.

Theorem add_wf : ∀ a b c d : Z,
    b ≠ 0%Z → d ≠ 0%Z → (a / b) + (c / d) = (a * d + c * b) / (b * d).
Proof.
  intros a b c d H H0.
  unfold add.
  repeat destruct constructive_indefinite_description.
  destruct a0 as [H1 H2].
  destruct a1 as [H3 H4].
  rewrite Qequiv in *; auto; try ring [H2 H4];
    intros H5; apply cancellation_0_mul in H5; tauto.
Qed.

Theorem mul_wf : ∀ a b c d : Z,
    b ≠ 0%Z → d ≠ 0%Z → (a / b) * (c / d) = (a * c) / (b * d).
Proof.
  intros a b c d H H0.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  destruct a0 as [H1 H2].
  destruct a1 as [H3 H4].
  rewrite Qequiv in *; auto; try ring [H2 H4];
    intros H5; apply cancellation_0_mul in H5; tauto.
Qed.

Theorem neg_wf : ∀ a b : Z, b ≠ 0%Z → -(a / b) = (-a) / b.
Proof.
  intros a b H.
  unfold neg.
  repeat destruct constructive_indefinite_description.
  destruct a0 as [H1 H2].
  rewrite Qequiv in *; auto.
  ring [H2].
Qed.

Theorem inv_wf : ∀ a b : Z, a ≠ 0%Z → b ≠ 0%Z → / (a / b) = b / a.
Proof.
  intros a b H H0.
  unfold inv.
  repeat destruct constructive_indefinite_description.
  destruct a0 as [H1 H2].
  rewrite Qequiv in H2; auto.
  rewrite Qequiv; auto.
  intros H3.
  subst.
  replace (0*b)%Z with (0%Z) in * by ring.
  symmetry in H2.
  apply cancellation_0_mul in H2.
  tauto.
Qed.

Theorem A3 : ∀ x, 0 + x = x.
Proof.
  intros [_ x H].
  unfold add in *.
  repeat destruct constructive_indefinite_description.
  destruct a, a0.
  rewrite <-add_wf, e1, <-e2; auto.
  unfold zero.
  rewrite add_wf, Qequiv; auto.
  - ring.
  - contradict n0.
    ring [n0].
  - apply zero_ne_1.
Qed.

Theorem A1 : ∀ a b, a + b = b + a.
Proof.
  intros [_ a A] [_ b B].
  unfold add in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  rewrite Qequiv in *; auto;
    try (intros Z; apply cancellation_0_mul in Z; tauto).
  ring.
Qed.

Theorem A2 : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  intros [_ a A] [_ b B] [_ c C].
  unfold add in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4.
  rewrite Qequiv in *; auto;
    try (intros Z; apply cancellation_0_mul in Z; tauto).
  apply (cancellation_mul_r x3); auto.
  ring [e7 e8].
Qed.

Theorem M3 : ∀ x, 1 * x = x.
Proof.
  intros [_ x H].
  unfold mul in *.
  repeat destruct constructive_indefinite_description.
  destruct a, a0.
  rewrite <-mul_wf, e1, <-e2; auto.
  unfold one.
  rewrite mul_wf, Qequiv; auto.
  - ring.
  - contradict n0.
    ring [n0].
  - apply zero_ne_1.
Qed.

Theorem M1 : ∀ a b, a * b = b * a.
Proof.  
  intros [_ a A] [_ b B].
  unfold mul in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  rewrite Qequiv in *; auto;
    try (intros Z; apply cancellation_0_mul in Z; tauto).
  ring.
Qed.

Theorem M2 : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  intros [_ a A] [_ b B] [_ c C].
  unfold mul in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4.
  rewrite Qequiv in *; auto;
    try (intros Z; apply cancellation_0_mul in Z; tauto).
  apply (cancellation_mul_r x3); auto.
  ring [e7 e8].
Qed.

Theorem D1 : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  intros [_ a A] [_ b B] [_ c C].
  unfold mul, add in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4, a5.
  rewrite Qequiv in *; auto;
    try (intros Z; apply cancellation_0_mul in Z; tauto).
  apply (cancellation_mul_r x3); auto.
  apply (cancellation_mul_r x1); auto.
  ring_simplify.
  replace (x*x5*x8*x10*x3*x1)%Z with (x*(x1*x3)*x5*x8*x10)%Z by ring.
  replace (x8*x3*x1*x4*x6*x9)%Z with ((x9*(x3*x6)*x1*x4*x8))%Z by ring.
  replace (x10*x3*x1*x4*x6*x7)%Z with (x7*(x1*x6)*x3*x4*x10)%Z by ring.
  rewrite e7, e9, e10.
  ring.
Qed.

Check mk_rt.

Check mk_field.
