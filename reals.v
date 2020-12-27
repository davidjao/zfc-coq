Require Export rationals.

Definition ℝ := {α in P ℚ |
                  α ≠ ∅ ∧
                  (∀ p q : Q, value ℚ p ∈ α → q < p → value ℚ q ∈ α) ∧
                  (∀ p : Q, value ℚ p ∈ α → ∃ r : Q, p < r ∧ value ℚ r ∈ α)}.

Theorem Dedekind_cut_1 : ∀ α, α ∈ ℝ → α ≠ ∅.
Proof.
  intros α H.
  now apply Specify_classification in H as [H [H0 [H1 H2]]].
Qed.

Theorem Dedekind_cut_2 : ∀ α,
    α ∈ ℝ → ∀ p q : Q, value ℚ p ∈ α → value ℚ q ∉ α → p < q.
Proof.
  intros α H p q H0 H1.
  apply Specify_classification in H as [H [H2 [H3 H4]]].
  destruct (T p q) as [[H5 [H6 H7]] | [[H5 [H6 H7]] | [H5 [H6 H7]]]]; subst;
    try tauto.
  exfalso; eauto.
Qed.

Theorem Dedekind_cut_3 : ∀ α,
    α ∈ ℝ → ∀ r s : Q, value ℚ r ∉ α → r < s → value ℚ s ∉ α.
Proof.
  intros α H r s H0 H1 H2.
  apply Specify_classification in H as [H [H3 [H4 H5]]].
  eauto.
Qed.

Definition R := elts ℝ.

Delimit Scope R_scope with R.
Open Scope R_scope.
Bind Scope R_scope with R.

Definition lt : R → R → Prop.
Proof.
  intros a b.
  exact (value ℝ a ⊊ value ℝ b).
Defined.

Infix "<" := lt : R_scope.
Notation "a > b" := (b < a) (only parsing) : R_scope.

Theorem lt_trans : ∀ a b c : R, a < b → b < c → a < c.
Proof.
  intros a b c [H H0] [H1 H2].
  split.
  - intros z H3.
    eauto.
  - contradict H0.
    destruct H0.
    now apply Subset_equality_iff.
Qed.

Theorem lt_trichotomy : ∀ a b : R, a < b ∨ a = b ∨ b < a.
Proof.
  intros a b.
  destruct (classic (a < b)), (classic (a = b)); try tauto.
  right; right.
  assert (∃ p, p ∈ value ℝ a ∧ p ∉ value ℝ b) as [p [H1 H2]].
  { apply NNPP.
    contradict H.
    split.
    - intros z H1.
      apply NNPP.
      contradict H.
      now (exists z).
    - contradict H0.
      now apply set_proj_injective. }
  pose proof in_set ℝ a as H3.
  apply Specify_classification in H3 as [H3 [H4 [H5 H6]]].
  pose proof in_set ℝ b as H7.
  apply Specify_classification in H7 as [H7 [H8 [H9 H10]]].
  assert (p ∈ ℚ) as H11 by (apply Powerset_classification in H3; eauto).
  split.
  - intros q H12.
    assert (q ∈ ℚ) as H13 by (apply Powerset_classification in H7; eauto).
    assert (mkSet _ _ H13 < mkSet _ _ H11)%Q as H14
        by eauto using Dedekind_cut_2, in_set.
    apply H5 in H14; auto.
  - contradict H0.
    now apply set_proj_injective.
Qed.

Theorem T : ∀ a b : R, a < b ∧ a ≠ b ∧ ¬ b < a
                       ∨ ¬ a < b ∧ a = b ∧ ¬ b < a
                       ∨ ¬ a < b ∧ a ≠ b ∧ b < a.
Proof.
  intros a b.
  destruct (lt_trichotomy a b) as [H | [H | H]].
  - left.
    destruct H as [H H0].
    repeat split; auto; contradict H0; try congruence.
    destruct H0 as [H0 H1].
    now apply Subset_equality_iff.
  - right; left.
    repeat split; auto; intros [H0 H1]; congruence.
  - right; right.
    destruct H as [H H0].
    repeat split; auto; contradict H0; try congruence.
    destruct H0 as [H0 H1].
    now apply Subset_equality_iff.
Qed.
