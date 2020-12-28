Require Export rationals.

Definition ℝ := {α in P ℚ |
                  α ≠ ∅ ∧
                  (∀ p q : Q, value _ p ∈ α → q < p → value _ q ∈ α) ∧
                  (∀ p : Q, value _ p ∈ α → ∃ r : Q, p < r ∧ value _ r ∈ α)}.

Theorem Dedekind_cut_1 : ∀ α, α ∈ ℝ → α ≠ ∅.
Proof.
  intros α H.
  now apply Specify_classification in H as [H [H0 [H1 H2]]].
Qed.

Theorem Dedekind_cut_2 : ∀ α,
    α ∈ ℝ → ∀ p q : Q, value _ p ∈ α → value _ q ∉ α → p < q.
Proof.
  intros α H p q H0 H1.
  apply Specify_classification in H as [H [H2 [H3 H4]]].
  destruct (T p q) as [[H5 [H6 H7]] | [[H5 [H6 H7]] | [H5 [H6 H7]]]]; subst;
    try tauto.
  exfalso; eauto.
Qed.

Theorem Dedekind_cut_3 : ∀ α,
    α ∈ ℝ → ∀ r s : Q, value _ r ∉ α → r < s → value _ s ∉ α.
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

Definition le a b := a < b ∨ a = b.
Infix "≤" := le : R_scope.
Notation "a ≥ b" := (b ≤ a) (only parsing) : R_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level): R_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level): R_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level): R_scope.

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
  assert (∃ p, p ∈ value ℝ a ∧ p ∉ value ℝ b) as [p [H1 H2]]
      by eauto using proper_subset_inhab, set_proj_injective.
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

Theorem lub : ∀ A,
    A ⊂ ℝ → A ≠ ∅ →
    (∃ β : R, ∀ α : R, value _ α ∈ A → α ≤ β) →
    ∃ γ : R, (∀ α : R, value _ α ∈ A → α ≤ γ) ∧
             (∀ δ : R, (∀ α : R, value _ α ∈ A → α ≤ δ) → γ ≤ δ).
Proof.
  intros A H H0 [β H1].
  set (g := ⋃ A).
  assert (g ∈ ℝ).
  { apply Specify_classification.
    repeat split.
    - apply Powerset_classification.
      intros z H2.
      apply Union_classification in H2 as [a [H2 H3]].
      apply H in H2.
      apply Specify_classification in H2 as [H2 [H4 [H5 H6]]].
      apply Powerset_classification in H2.
      now apply H2.
    - apply Nonempty_classification.
      apply Nonempty_classification in H0 as [z H0].
      pose proof H0 as H2.
      apply H, Specify_classification in H2 as [H2 [H3 [H4 H5]]].
      apply Nonempty_classification in H3 as [y H3].
      exists y.
      apply Union_classification.
      exists z.
      split; auto.
    - intros p q H2 H3.
      apply Union_classification in H2 as [x [H2 H4]].
      apply H in H2 as H5.
      apply Specify_classification in H5 as [H5 [H6 [H7 H8]]].
      apply H7 in H3; auto.
      apply Union_classification.
      now (exists x).
    - intros p H2.
      apply Union_classification in H2 as [x [H2 H3]].
      apply H in H2 as H4.
      apply Specify_classification in H4 as [H4 [H5 [H6 H7]]].
      apply H7 in H3 as [r [H3 H8]].
      exists r.
      split; auto.
      apply Union_classification.
      now (exists x). }
  set (γ := (mkSet _ _ H2)).
  exists γ.
  split.
  - intros α H3.
    unfold le.
    destruct (classic (α = γ)); auto.
    left.
    split.
    + intros z H5.
      simpl.
      apply Union_classification.
      now (exists (value _ α)).
    + contradict H4.
      now apply set_proj_injective.
  - intros δ H3.
    unfold le.
    destruct (T γ δ) as [H4 | [H4 | [H4 [H5 H6]]]]; try tauto.
    assert (∃ s, s ∈ value ℝ γ ∧ s ∉ value ℝ δ) as [s [H7 H8]]
        by eauto using proper_subset_inhab, set_proj_injective.
    simpl in *.
    apply Union_classification in H7 as [a [H7 H9]].
    apply H in H7 as H10.
    set (α := mkSet _ _ H10).
    pose proof H7 as H11.
    apply (H3 α) in H7.
    unfold le in H7.
    assert (¬ δ < α) as H12 by (pose proof (T α δ); tauto).
    contradict H12.
    split.
    + intros z H12.
      simpl.
      apply H, Specify_classification in H11 as [H11 [H13 [H14 H15]]].
      apply Powerset_classification in H11.
      apply H11 in H9 as H16.
      set (σ := mkSet _ _ H16).
      pose proof in_set _ δ as H17.
      apply Specify_classification in H17 as [H17 [H18 [H19 H20]]].
      apply Powerset_classification in H17.
      apply H17 in H12 as H21.
      set (ζ := mkSet _ _ H21).
      replace z with (value _ ζ); auto.
      apply (H14 σ); eauto using Dedekind_cut_2, in_set.
    + intros H12.
      rewrite H12 in H8.
      contradiction.
Qed.

Definition inz (q : Q) := {x in ℚ | ∃ ξ : Q, value _ ξ = x ∧ (ξ < q)%Q}.

Theorem inz_in : ∀ q, inz q ∈ ℝ.
Proof.
  intros q.
  apply Specify_classification.
  repeat split.
  - apply Powerset_classification.
    intros z H.
    now apply Specify_classification in H as [H H0].
  - apply Nonempty_classification.
    exists (value _ (q-1)).
    apply Specify_classification.
    split; auto using in_set.
    exists (q-1).
    split; auto.
    unfold rationals.lt.
    replace (q-(q-1)) with 1 by field.
    unfold one.
    rewrite pos_wf, integers.M3; auto using zero_ne_1, zero_lt_1.
  - intros p x H H0.
    apply Specify_classification in H as [H [ξ [H1 H2]]].
    apply Specify_classification.
    split; auto using in_set.
    exists x.
    replace ξ with p in *; eauto using set_proj_injective, rationals.lt_trans.
  - intros p H.
    apply Specify_classification in H as [H [ξ [H0 H1]]].
    replace ξ with p in *; eauto using set_proj_injective.
    destruct (lt_dense p q) as [r H2]; auto.
    exists r.
    split; try tauto.
    apply Specify_classification.
    split; eauto using in_set.
    now exists r.
Qed.

Definition IQR (q : Q) := (mkSet _ _ (inz_in q)) : R.

Coercion IQR : Q >-> R.
