Require Export rationals.

Definition ℝ := {α in P ℚ | α ≠ ∅ ∧ α ≠ ℚ ∧
                            (∀ p q : Q, p ∈ α → q < p → q ∈ α) ∧
                            (∀ p : Q, p ∈ α → ∃ r : Q, p < r ∧ r ∈ α)}.

Definition R := elts ℝ.

Definition IRS (a : R) := value ℝ a : set.
Coercion IRS : R >-> set.

Lemma Dedekind_cut_0 : ∀ (α : R) (p : set), p ∈ α → p ∈ ℚ.
Proof.
  intros α p H.
  pose proof in_set _ α as H0.
  apply Specify_classification in H0 as [H0 [H1 [H2 [H3 H4]]]].
  apply Powerset_classification in H0.
  eauto.
Qed.

Lemma Dedekind_cut_1 : ∀ α : R, ∅ ≠ α.
Proof.
  intros α H.
  pose proof in_set _ α as H0.
  apply Specify_classification in H0 as [H0 [H1 [H2 [H3 H4]]]].
  now contradict H1.
Qed.

Lemma Dedekind_cut_2 : ∀ (α : R) (p q : Q), p ∈ α → q < p → q ∈ α.
Proof.
  intros α p q H H0.
  pose proof in_set _ α as H1.
  apply Specify_classification in H1 as [H1 [H2 [H3 [H4 H5]]]].
  eauto.
Qed.

Lemma Dedekind_cut_3 : ∀ (α : R) (p : Q), p ∈ α → ∃ r : Q, p < r ∧ r ∈ α.
Proof.
  intros α p H.
  pose proof (in_set _ α).
  apply Specify_classification in H0 as [H0 [H1 [H2 [H3 H4]]]].
  eauto.
Qed.

Lemma Dedekind_cut_4 : ∀ α : R, ∀ p q : Q, p ∈ α → q ∉ α → p < q.
Proof.
  intros α p q H H0.
  pose proof in_set _ α as H1.
  apply Specify_classification in H1 as [H1 [H2 [H3 [H4 H5]]]].
  destruct (T p q) as [[H6 [H7 H8]] | [[H6 [H7 H8]] | [H6 [H7 H8]]]]; subst;
    try tauto.
  exfalso; eauto.
Qed.

Lemma Dedekind_cut_5 : ∀ α : R, ∀ r s : Q, r ∉ α → r < s → s ∉ α.
Proof.
  intros α r s H H0 H1.
  pose proof in_set _ α as H2.
  apply Specify_classification in H2 as [H2 [H3 [H4 [H5 H6]]]].
  eauto.
Qed.

Lemma Dedekind_cut_6 : ∀ a : R, ∃ q : Q, q ∉ a.
Proof.
  intros a.
  pose proof (in_set _ a) as H.
  apply Specify_classification in H as [H [H0 [H1 [H2 H3]]]].
  apply Powerset_classification in H.
  assert (ℚ ≠ a) as H4 by (now contradict H1).
  apply not_proper_subset_inhab in H4 as [z [H4 H5]].
  - exists (mkSet _ _ H4); auto.
  - contradict H4.
    destruct H4 as [H4 H5].
    now apply Subset_equality_iff.
Qed.

Delimit Scope R_scope with R.
Open Scope R_scope.
Bind Scope R_scope with R.

Definition lt (a b : R) := a ⊊ b.

Infix "<" := lt : R_scope.
Notation "a > b" := (b < a) (only parsing) : R_scope.

Definition le a b := a < b ∨ a = b.
Infix "≤" := le : R_scope.
Notation "a ≥ b" := (b ≤ a) (only parsing) : R_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level): R_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level): R_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level): R_scope.

Theorem le_is_subset : ∀ a b, a ≤ b ↔ a ⊂ b.
Proof.
  intros a b.
  split; unfold le, lt, proper_subset; intros H.
  - destruct H as [[H H0] | H]; subst; auto using Set_is_subset.
  - destruct (classic (a = b)); auto.
    left; split; eauto using set_proj_injective.
Qed.

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
  assert (∃ p, p ∈ a ∧ p ∉ b) as [p [H1 H2]]
      by eauto using not_proper_subset_inhab, set_proj_injective.
  pose proof in_set ℝ a as H3.
  apply Specify_classification in H3 as [H3 [H4 [H5 [H6 H7]]]].
  pose proof in_set ℝ b as H8.
  apply Specify_classification in H8 as [H8 [H9 [H10 [H11 H12]]]].
  assert (p ∈ ℚ) as H13 by (apply Powerset_classification in H3; eauto).
  split.
  - intros q H14.
    assert (q ∈ ℚ) as H15 by (apply Powerset_classification in H8; eauto).
    assert (mkSet _ _ H15 < mkSet _ _ H13)%Q as H16
        by eauto using Dedekind_cut_4, in_set.
    apply H6 in H16; auto.
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

Theorem lub : ∀ A, A ⊂ ℝ → A ≠ ∅ → (∃ β : R, ∀ α : R, α ∈ A → α ≤ β) →
                   ∃ γ : R, (∀ α : R, α ∈ A → α ≤ γ) ∧
                            (∀ δ : R, (∀ α : R, α ∈ A → α ≤ δ) → γ ≤ δ).
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
      apply Specify_classification in H2 as [H2 [H4 [H5 [H6 H7]]]].
      apply Powerset_classification in H2.
      now apply H2.
    - apply Nonempty_classification.
      apply Nonempty_classification in H0 as [z H0].
      pose proof H0 as H2.
      apply H, Specify_classification in H2 as [H2 [H3 [H4 [H5 H6]]]].
      apply Nonempty_classification in H3 as [y H3].
      exists y.
      apply Union_classification.
      exists z.
      split; auto.
    - intros H2.
      pose proof in_set _ β as H3.
      apply Specify_classification in H3 as [H3 [H4 [H5 [H6 H7]]]].
      contradict H5.
      apply Subset_equality_iff.
      split.
      + now rewrite Powerset_classification in H3.
      + rewrite <-H2.
        intros z H8.
        apply Union_classification in H8 as [x [H8 H9]].
        assert (x ∈ ℝ) as H10 by eauto.
        pose proof H1 (mkSet _ _ H10) H8 as H11.
        destruct H11 as [H11 | H11].
        * now apply H11.
        * now subst.
    - intros p q H2 H3.
      apply Union_classification in H2 as [x [H2 H4]].
      apply H in H2 as H5.
      apply Specify_classification in H5 as [H5 [H6 [H7 [H8 H9]]]].
      apply H8 in H3; auto.
      apply Union_classification.
      now (exists x).
    - intros p H2.
      apply Union_classification in H2 as [x [H2 H3]].
      apply H in H2 as H4.
      apply Specify_classification in H4 as [H4 [H5 [H6 [H7 H8]]]].
      apply H8 in H3 as [r [H3 H9]].
      exists r.
      split; auto.
      apply Union_classification.
      now (exists x). }
  set (γ := mkSet _ _ H2 : R).
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
      now (exists α).
    + contradict H4.
      now apply set_proj_injective.
  - intros δ H3.
    unfold le.
    destruct (T γ δ) as [H4 | [H4 | [H4 [H5 H6]]]]; try tauto.
    assert (∃ s, s ∈ γ ∧ s ∉ δ) as [s [H7 H8]]
        by eauto using not_proper_subset_inhab, set_proj_injective.
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
      apply H, Specify_classification in H11 as [H11 [H13 [H14 [H15 H16]]]].
      apply Powerset_classification in H11.
      apply H11 in H9 as H17.
      set (σ := mkSet _ _ H17).
      pose proof in_set _ δ as H18.
      apply Specify_classification in H18 as [H18 [H19 [H20 [H21 H22]]]].
      apply Powerset_classification in H18.
      apply H18 in H12 as H23.
      set (ζ := mkSet _ _ H23).
      replace z with (value _ ζ); auto.
      apply (H15 σ); eauto using Dedekind_cut_4, in_set.
    + intros H12.
      rewrite H12 in H8.
      contradiction.
Qed.

Definition iqr_set (q : Q) := {x in ℚ | ∃ ξ : Q, x = ξ ∧ (ξ < q)%Q}.

Theorem iqr_in : ∀ q, iqr_set q ∈ ℝ.
Proof.
  intros q.
  apply Specify_classification.
  repeat split.
  - apply Powerset_classification.
    intros z H.
    now apply Specify_classification in H as [H H0].
  - apply Nonempty_classification.
    exists (q-1).
    apply Specify_classification.
    split; eauto using in_set.
    exists (q-1).
    split; auto.
    unfold rationals.lt.
    replace (q-(q-1)) with (1-0) by field.
    apply zero_lt_1.
  - intros H.
    apply Subset_equality_iff in H as [H H0].
    pose proof (H0 (q+1) (in_set _ _)) as H1.
    apply Specify_classification in H1 as [H1 [ξ [H2 H3]]].
    replace ξ with (q+1) in * by eauto using set_proj_injective.
    contradiction (lt_antisym q (q+1)).
    rewrite <-(rationals.A3 q), rationals.A1 at 1.
    auto using O1, zero_lt_1.
  - intros p x H H0.
    apply Specify_classification in H as [H [ξ [H1 H2]]].
    apply Specify_classification.
    split; eauto using in_set.
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

Definition IQR (q : Q) := (mkSet _ _ (iqr_in q)) : R.
Definition zero := IQR 0.

Coercion IQR : Q >-> R.

Notation "0" := zero : R_scope.

Definition add_set (α β : R) := {x in ℚ | ∃ r s, x = r + s ∧ r ∈ α ∧ s ∈ β}.

Lemma not_Q_subset : ∀ α : R, ¬ ℚ ⊊ α.
Proof.
  intros α [H H0].
  contradict H0.
  apply Subset_equality_iff; split; auto.
  intros z H0.
  pose proof (in_set _ α) as H2.
  apply Specify_classification in H2 as [H2 H3].
  apply Powerset_classification in H2.
  auto.
Qed.

Lemma not_Q_eq : ∀ α : R, ℚ ≠ α.
Proof.
  intros α H.
  pose proof (in_set _ α) as H0.
  apply Specify_classification in H0.
  symmetry in H.
  tauto.
Qed.

Theorem add_in : ∀ α β, add_set α β ∈ ℝ.
Proof.
  intros α β.
  apply Specify_classification.
  repeat split; unfold add_set.
  - apply Powerset_classification.
    intros z H.
    now apply Specify_classification in H as [H H0].
  - apply Nonempty_classification.
    pose proof (in_set _ α) as H.
    apply Specify_classification in H as [H [H0 [H1 [H2 H3]]]].
    pose proof (in_set _ β) as H4.
    apply Specify_classification in H4 as [H4 [H5 [H6 [H7 H8]]]].
    rewrite Nonempty_classification in H0, H5.
    rewrite Powerset_classification in H, H4.
    destruct H0 as [x H0], H5 as [y H5].
    assert (x ∈ ℚ) as H9 by eauto.
    assert (y ∈ ℚ) as H10 by eauto.
    exists (mkSet _ _ H9 + mkSet _ _ H10).
    apply Specify_classification.
    split; eauto using in_set.
  - destruct (not_proper_subset_inhab ℚ α)
      as [r' [H H0]], (not_proper_subset_inhab ℚ β) as [s' [H1 H2]];
    auto using not_Q_subset, not_Q_eq.
    intros H3.
    apply Subset_equality_iff in H3 as [H3 H4].
    set (ρ := mkSet _ _ H).
    set (σ := mkSet _ _ H1).
    pose proof (in_set _ (ρ + σ)) as H5.
    apply H4, Specify_classification in H5 as [H5 [r [s [H6 [H7 H8]]]]].
    assert (r < ρ)%Q as H9 by eauto using Dedekind_cut_4, in_set.
    assert (s < σ)%Q as H10 by eauto using Dedekind_cut_4, in_set.
    assert (r + s < ρ + σ)%Q.
    { eapply rationals.lt_trans.
      eapply O1 in H10; eauto.
      eapply O1 in H9.
      rewrite rationals.A1, (rationals.A1 ρ); eauto. }
    replace (ρ+σ)%Q with (r+s)%Q in *; eauto using set_proj_injective.
    contradiction (rationals.lt_irrefl (r+s)).
  - intros p q H H0.
    apply Specify_classification in H as [H [r [s [H1 [H2 H3]]]]].
    assert (p = r+s) as H4 by eauto using set_proj_injective.
    subst.
    apply Specify_classification.
    split; eauto using in_set.
    exists (q+-s), s.
    repeat split; auto.
    + now replace (q+-s+s) with q by ring.
    + pose proof in_set _ α as H4.
      apply Specify_classification in H4 as [H4 [H5 [H6 [H7 H8]]]].
      eapply H7; eauto.
      apply (O1 (-s)) in H0.
      ring_simplify in H0.
      now rewrite rationals.A1.
  - intros p H.
    apply Specify_classification in H as [H [r [s [H0 [H1 H2]]]]].
    assert (p = r+s) as H3 by eauto using set_proj_injective.
    subst.
    pose proof in_set _ α as H3.
    apply Specify_classification in H3 as [H3 [H4 [H5 [H6 H7]]]].
    apply H7 in H1 as [t [H1 H8]].
    exists (t+s).
    split.
    + rewrite ? (rationals.A1 _ s).
      now apply O1.
    + apply Specify_classification.
      split; eauto using in_set.
Qed.

Definition add : R → R → R.
Proof.
  intros a b.
  exact (mkSet _ _ (add_in a b)).
Defined.

Infix "+" := add : R_scope.

Theorem A1 : ∀ a b, a + b = b + a.
Proof.
  intros a b.
  unfold add.
  apply set_proj_injective.
  simpl.
  unfold add_set.
  apply Extensionality.
  split; intros H; rewrite Specify_classification in *;
    destruct H as [H [r [s [H0 [H1 H2]]]]]; split; auto; exists s, r;
      repeat split; auto; now rewrite rationals.A1.
Qed.

Theorem A2 : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  intros a b c.
  unfold add.
  apply set_proj_injective.
  simpl.
  unfold add_set.
  apply Extensionality.
  split; intros H; rewrite Specify_classification in *; simpl in *;
    destruct H as [H [r [s [H0 [H1 H2]]]]].
  - apply Specify_classification in H2 as [H2 [t [u [H3 [H4 H5]]]]].
    apply set_proj_injective in H3.
    rewrite H3 in *.
    split; auto.
    exists (r+t)%Q, u.
    repeat split; auto.
    + now rewrite <-rationals.A2.
    + apply Specify_classification; split; eauto using in_set.
  - apply Specify_classification in H1 as [H1 [t [u [H3 [H4 H5]]]]].
    apply set_proj_injective in H3.
    rewrite H3 in *.
    split; auto.
    exists t, (u+s)%Q.
    repeat split; auto.
    + now rewrite rationals.A2.
    + apply Specify_classification; split; eauto using in_set.
Qed.

Theorem A3 : ∀ a, a + 0 = a.
Proof.
  intros α.
  unfold add, zero.
  apply set_proj_injective.
  simpl.
  unfold add_set, IQR in *.
  apply Extensionality; split; intros H.
  - apply Specify_classification in H as [H [r [s [H0 [H1 H2]]]]].
    apply Specify_classification in H2 as [H2 [ξ [H3 H4]]].
    pose proof (in_set _ α) as H5.
    apply Specify_classification in H5 as [H6 [H7 [H8 [H9 H10]]]].
    set (ζ := mkSet _ _ H).
    replace z with (value _ ζ) in * by auto.
    apply set_proj_injective in H0.
    apply set_proj_injective in H3.
    eapply H9; eauto.
    rewrite H0, H3, <-(A3 r), (rationals.A1 0), <-rationals.A2.
    apply O1.
    now rewrite (rationals.A3).
  - apply Specify_classification.
    pose proof (in_set _ α) as H0.
    apply Specify_classification in H0 as [H0 [H1 [H2 [H3 H4]]]].
    apply Powerset_classification in H0.
    split; auto.
    apply H0 in H as H5.
    set (ζ := (mkSet _ _ H5) : Q).
    replace z with (value _ ζ) in * by auto.
    apply H4 in H as [r [H H6]].
    exists r, (ζ+-r)%Q.
    repeat split; auto.
    + now replace (r+(ζ+-r))%Q with ζ by ring.
    + simpl.
      apply Specify_classification; split; eauto using in_set.
      exists (ζ+-r)%Q.
      split; auto.
      rewrite <-(A4 r), ? (rationals.A1 _ (-r)).
      now apply O1.
Qed.

Definition neg_set (α : R) :=
  {p in ℚ | ∃ ρ r : Q, p = ρ ∧ (0 < r)%Q ∧ (- ρ - r)%Q ∉ α}.

Theorem neg_in : ∀ a, neg_set a ∈ ℝ.
Proof.
  intros α.
  apply Specify_classification.
  repeat split.
  - apply Powerset_classification.
    intros z H.
    now apply Specify_classification in H.
  - apply Nonempty_classification.
    pose proof in_set _ α as H.
    apply Specify_classification in H as [H [H0 [H1 [H2 H3]]]].
    apply Powerset_classification in H.
    destruct (not_proper_subset_inhab ℚ α) as [s [H4 H5]]; auto.
    { intros [H4 H5].
      contradict H1.
      now apply Subset_equality_iff. }
    set (σ := mkSet _ _ H4 : Q).
    exists (-σ-1).
    apply Specify_classification.
    split; eauto using in_set.
    exists (-σ-1), 1.
    repeat split; auto using zero_lt_1.
    now replace (-(-σ-1)-1)%Q with σ by ring.
  - pose proof in_set _ α as H.
    apply Specify_classification in H as [H [H0 [H1 [H2 H3]]]].
    apply Powerset_classification in H.
    apply Nonempty_classification in H0 as [s H0].
    assert (s ∈ ℚ) as H4 by auto.
    set (q := (mkSet _ _ H4) : Q).
    intros H5.
    pose proof (in_set _ (-q)) as H6.
    rewrite <-H5 in H6.
    pose proof H6 as H7.
    apply Specify_classification in H7 as [H7 [p [r [H8 [H9 H10]]]]].
    apply set_proj_injective in H8.
    contradict H10.
    apply (H2 q); auto.
    subst.
    apply (O1 (q-r)) in H9.
    ring_simplify in H9.
    now ring_simplify.
  - intros p q H H0.
    apply Specify_classification in H as [H [ρ [r [H1 [H2 H3]]]]].
    apply set_proj_injective in H1.
    subst.
    apply Specify_classification.
    split; eauto using in_set.
    exists q, r.
    repeat split; auto.
    contradict H3.
    pose proof in_set _ α as H4.
    apply Specify_classification in H4 as [H4 [H5 [H6 [H7 H8]]]].
    eapply H7; eauto.
    apply (rationals.O1 (-ρ-q-r)%Q) in H0.
    now ring_simplify in H0.
  - intros p H.
    apply Specify_classification in H as [H [ρ [r [H1 [H2 H3]]]]].
    apply set_proj_injective in H1.
    subst.
    assert (ρ+0 < ρ+r)%Q as H0 by now apply O1.
    ring_simplify in H0.
    apply lt_dense in H0 as [t [H0 H1]].
    exists t.
    split; auto.
    apply Specify_classification.
    split; eauto using in_set.
    exists t, (ρ+r-t).
    repeat split; auto.
    + apply (O1 (-t)) in H1.
      now rewrite ? (rationals.A1 (-t)), rationals.A4 in H1.
    + now replace (-t-(ρ+r-t)) with (-ρ-r) by ring.
Qed.

Definition neg : R → R.
Proof.
  intros a.
  exact (mkSet _ _ (neg_in a)).
Defined.

Notation "- a" := (neg a) : R_scope.

Theorem cut_archimedean : ∀ (α : R) (b : Q),
    (0 < b)%Q → ∃ n : Z, n * b ∈ α ∧ (n + 1) * b ∉ α.
Proof.
  intros α b H.
  pose proof (in_set _ α) as H0.
  apply Specify_classification in H0 as [H0 [H1 [H2 [H3 H4]]]].
  apply Nonempty_classification in H1 as [x H1].
  apply Powerset_classification in H0.
  assert (x ∈ ℚ) as H5 by eauto.
  set (ξ := mkSet _ _ H5 : Q).
  destruct (Q_archimedean ξ b) as [k [H6 H7]]; auto.
  destruct (WOP (λ m, (k + m)%Z * b ∉ α)) as [n [H8 H9]].
  - intros m H8.
    apply NNPP.
    contradict H8.
    assert (m ≤ 0)%Z as [H9 | H9] by
          (unfold integers.le; pose proof (integers.T m 0); tauto).
    + apply (H3 ξ); auto.
      destruct H6 as [H6 | H6]; rewrite <-IZQ_add; ring_simplify.
      * apply (rationals.lt_trans _ (k*b)); auto.
        rewrite <-(rationals.A3 (k*b)) at 2.
        rewrite (rationals.A1 0).
        apply rationals.O1.
        replace 0%Q with (0*b)%Q by ring.
        rewrite ? (rationals.M1 _ b).
        now apply O3, IZQ_lt.
      * rewrite <-(rationals.A3 ξ), <-H6, (rationals.A1 0).
        apply O1.
        replace 0%Q with (0*b)%Q by ring.
        rewrite ? (rationals.M1 _ b).
        now apply O3, IZQ_lt.
    + subst.
      rewrite integers.A3_r.
      destruct H6 as [H6 | H6].
      * apply (H3 ξ); auto.
      * rewrite H6; auto.
  - destruct (not_proper_subset_inhab ℚ α) as [z [H8 H9]]; auto.
    { intros [H8 H9].
      contradict H9.
      now apply Subset_equality_iff. }
    set (ζ := mkSet _ _ H8 : Q).
    destruct (Q_archimedean ζ b) as [m [H10 H11]]; auto.
    exists (m - k + 1)%Z.
    split.
    + unfold integers.sub.
      rewrite  <-(integers.A4 k), (integers.A1 m), (integers.A1 k),
      <-integers.A2.
      apply integers.O1.
      destruct (integers.T k (m+1)) as [H12 | [H12 | H12]]; intuition;
        contradict H9; replace z with (value _ ζ); try apply (H3 ξ); auto.
      * rewrite H12, <-IZQ_add in H6.
        destruct H6 as [H6 | H6]; eauto using rationals.lt_trans.
        now rewrite <-H6.
      * apply IZQ_lt, (O3 b) in H15; auto.
        rewrite ? (M1 b) in H15.
        rewrite <-IZQ_add in H15.
        assert (ζ < k * b)%Q as H9 by eauto using rationals.lt_trans.
        destruct H6 as [H6 | H6]; eauto using rationals.lt_trans.
        now rewrite <-H6.
    + unfold integers.sub.
      rewrite ? IZQ_add.
      replace (k + (m + - k + 1))%Z with (m+1)%Z by ring.
      eapply Dedekind_cut_5; eauto using in_set.
      * replace z with (value _ ζ) in * by auto.
        exact H9.
      * now rewrite <-IZQ_add.
  - exists (k+(n+-(1)))%Z.
    rewrite ? IZQ_add.
    split.
    + apply NNPP.
      intros H10.
      assert (n + (-(1)) < n)%Z.
      { rewrite <-(integers.A3_r n), <-integers.A2.
        apply integers.O1.
        rewrite integers.A3, <-integers.neg_lt_0.
        exact integers.zero_lt_1. }
      pose proof (integers.T (n+(-(1))) n).
      eapply H9 in H10 as [H10 | H10]; try tauto.
      symmetry in H10.
      tauto.
    + replace (1) with (IZQ 1) by auto.
      now rewrite IZQ_add, <-? integers.A2, (integers.A1 _ 1), integers.A4,
      integers.A3_r.
Qed.
      
Theorem A4 : ∀ a, a + -a = 0.
Proof.
  intros α.
  unfold neg, add, zero, add_set.
  apply set_proj_injective.
  simpl.
  unfold iqr_set.
  apply Extensionality.
  split; intros H; apply Specify_classification in H as [H H0].
  - destruct H0 as [r [p [H0 [H1 H2]]]].
    apply Specify_classification in H2 as [H2 [s [q [H3 [H4 H5]]]]].
    apply set_proj_injective in H3.
    subst.
    assert (-s ∉ α)%Q as H0.
    { eapply Dedekind_cut_5; eauto using in_set.
      unfold sub in *.
      rewrite <-(rationals.A3 (-s)) at 2.
      rewrite <-(rationals.A4 q), <-rationals.A2, <-(rationals.A1 (-q)),
      <-(rationals.A3 (-q+-s)), ? (rationals.A1 _ (-q+-s)) at 1.
      now apply rationals.O1. }
    eapply Dedekind_cut_4 in H0; eauto using in_set.
    apply Specify_classification.
    split; eauto using in_set.
    exists (r+s)%Q.
    split; auto.
    rewrite <-(rationals.A4 s), (rationals.A1 _ s).
    now apply O1.
  - destruct H0 as [v [H0 H1]].
    subst.
    set (w := (-v * 2^-1)%Q).
    assert (0 < 2)%Z as H0.
    apply IZQ_lt.
    eauto using zero_lt_1, one_lt_2, rationals.lt_trans.
    assert (0 < w)%Q as H2.
    { unfold w.
      apply rationals.O2; try now apply lt_neg_0.
      now apply O4, IZQ_lt. }
    destruct (cut_archimedean α w) as [n [H3 H4]]; auto.
    apply Specify_classification.
    split; auto.
    exists (n*w)%Q, (-(n+2)*w)%Q.
    repeat split; auto.
    + apply f_equal.
      unfold w.
      ring_simplify.
      rewrite <-M2, inv_l; try ring.
      intros H5.
      apply IZQ_eq in H5.
      subst.
      rewrite H5 in H0.
      contradiction (integers.lt_irrefl 0).
    + apply Specify_classification.
      split; eauto using in_set.
      exists (-(n+2)*w), w.
      repeat split; auto.
      replace ((-(-(n+2)*w)-w))%Q with ((n+2)*w+-w)%Q by ring.
      rewrite ? D1.
      replace (IZQ 2) with (1/1+1/1)%Q.
      * rewrite D1, M3, <-? rationals.A2, A4, (rationals.A1 w), rationals.A3.
        rewrite <-(M3 w) at 2.
        now rewrite <-D1.
      * unfold IZQ; rewrite add_wf, Qequiv; try rewrite integers.M3;
          auto using integers.zero_ne_1; try ring.
Qed.

Theorem O1 : ∀ a b c, b < c → a + b < a + c.
Proof.
  intros a b c H.
  unfold lt in *.
  destruct H as [H H0].
  split.
  - intros z H1.
    unfold add in *.
    apply Specify_classification in H1 as [H1 [r [s [H2 [H3 H4]]]]].
    apply Specify_classification.
    split; auto.
    exists r, s.
    split; auto.
  - contradict H0.
    apply f_equal.
    apply set_proj_injective in H0.
    assert (-a+(a+b) = -a+(a+c)) by congruence.
    now rewrite ? A2, ? (A1 (-a)), ? A4, ? (A1 0), ? A3 in H1.
Qed.

Definition mul_pos_set (a b : R) :=
  {x in ℚ | (∃ r s ξ : Q, x = ξ ∧ r ∈ a ∧ s ∈ b ∧ 0 < r ∧ 0 < s ∧ ξ ≤ r * s)%Q}.

Definition one : R := IQR 1.
Notation "1" := one : R_scope.

Theorem pos_nonempty : ∀ a, 0 < a → ∃ c : Q, (0 < c)%Q ∧ c ∈ a.
Proof.
  intros a H.
  apply proper_subset_inhab in H as [c [H H0]].
  assert (c ∈ ℚ) as H1.
  { pose proof (in_set _ a) as H1.
    apply Specify_classification in H1 as [H1 [H2 [H3 [H4 H5]]]].
    apply Powerset_classification in H1.
    now apply H1. }
  set (γ := mkSet _ _ H1 : Q).
  assert (¬ γ < 0)%Q as H2.
  { contradict H0.
    unfold zero, IQR, iqr_set.
    apply Specify_classification.
    split; auto.
    now exists γ. }
  destruct (rationals.T γ 0) as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]];
    try tauto; try now (exists γ).
  pose proof in_set _ a as H6.
  apply Specify_classification in H6 as [H6 [H7 [H8 [H9 H10]]]].
  destruct (H10 γ H) as [x [H11 H12]].
  exists x.
  split; auto; congruence.
Qed.

Theorem mul_pos_in : ∀ a b, 0 < a → 0 < b → mul_pos_set a b ∈ ℝ.
Proof.
  intros a b H H0.
  apply Specify_classification.
  repeat split.
  - apply Powerset_classification.
    intros x H1.
    apply Specify_classification in H1
      as [H1 [r [s [ξ [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]].
    subst.
    apply in_set.
  - apply Nonempty_classification.
    apply pos_nonempty in H as [c [H H1]].
    apply pos_nonempty in H0 as [d [H0 H2]].
    exists (c*d - 1).
    apply Specify_classification.
    simpl.
    split; unfold IQS; auto using in_set.
    exists c, d, (c*d - 1).
    repeat split; auto.
    left.
    apply lt_sub_pos, zero_lt_1.
  - destruct (Dedekind_cut_6 a) as [c H1], (Dedekind_cut_6 b) as [d H2].
    intros H3.
    apply Subset_equality_iff in H3 as [H3 H4].
    assert (c*d ∈ mul_pos_set a b) as H5 by eauto using in_set.
    apply Specify_classification in H5
      as [H5 [r [s [ξ [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]].
    assert (r < c)%Q as H12 by eauto using Dedekind_cut_4, in_set.
    assert (s < d)%Q as H13 by eauto using Dedekind_cut_4, in_set.
    assert (0 < c)%Q as H14 by eauto using rationals.lt_trans.
    apply set_proj_injective in H6.
    subst.
    assert (r*s < c*d)%Q by auto using lt_cross_mul.
    unfold rationals.le in H11.
    pose proof (rationals.T (c*d) (r*s)).
    tauto.
  - intros p q H1 H2.
    apply Specify_classification in H1
      as [H1 [r [s [ξ [H3 [H4 [H5 [H6 [H7 H8]]]]]]]]].
    apply Specify_classification.
    split; unfold IQS; auto using in_set.
    exists r, s, q.
    apply set_proj_injective in H3.
    subst.
    repeat split; auto.
    destruct H8 as [H8 | H8]; left; eauto using rationals.lt_trans.
    congruence.      
  - intros p H1.
    apply Specify_classification in H1
      as [H1 [r [s [ξ [H3 [H4 [H5 [H6 [H7 H8]]]]]]]]].
    apply Dedekind_cut_3 in H4 as [ρ [H4 H9]].
    apply Dedekind_cut_3 in H5 as [σ [H5 H10]].
    exists (ρ * σ)%Q.
    apply set_proj_injective in H3.
    assert (r*s < ρ*σ)%Q as H2 by auto using lt_cross_mul.
    split.
    + rewrite H3.
      destruct H8 as [H8 | H8]; eauto using rationals.lt_trans.
      congruence.
    + apply Specify_classification.
      split; eauto using in_set.
      exists ρ, σ, (ρ * σ).
      repeat split; eauto using rationals.lt_trans.
      now right.
Qed.

Definition mul_pos : R → R → R.
Proof.
  intros a b.
  destruct (excluded_middle_informative (0 < a)),
  (excluded_middle_informative (0 < b)).
  - exact (mkSet _ _ (mul_pos_in a b l l0)).
  - exact 0.
  - exact 0.
  - exact 0.
Defined.

Infix "*" := mul_pos : R_scope.

Theorem M1_pos : ∀ a b, 0 < a → 0 < b → a * b = b * a.
Proof.
  intros a b H H0.
  unfold mul_pos, mul_pos_set.
  repeat destruct excluded_middle_informative; auto.
  apply set_proj_injective.
  simpl.
  apply Extensionality.
  split; intros H1; apply Specify_classification in H1
    as [H1 [r [s [ξ [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]];
  apply Specify_classification; split; auto; exists s, r, ξ;
    rewrite M1; split; auto.
Qed.

Theorem O2_pos : ∀ a b, 0 < a → 0 < b → 0 < a * b.
Proof.
  intros a b H H0.
  unfold mul_pos.
  repeat destruct excluded_middle_informative; try tauto.
  split.
  - intros z H1.
    unfold zero, IQR in H1.
    apply Specify_classification in H1 as [H1 [ξ [H2 H3]]].
    subst.
    apply Specify_classification.
    split; auto.
    apply pos_nonempty in H as [c [H H2]].
    apply pos_nonempty in H0 as [d [H0 H4]].
    exists c, d, ξ.
    repeat split; auto.
    left.
    eauto using O2, rationals.lt_trans.
  - intros H1.
    apply pos_nonempty in H as [c [H H2]].
    apply pos_nonempty in H0 as [d [H0 H3]].
    apply lt_dense in H as [e [H H4]].
    apply lt_dense in H0 as [f [H0 H5]].
    assert ((e * f)%Q ∈ 0).
    { rewrite H1.
      apply Specify_classification.
      split; eauto using in_set.
      exists c, d, (e*f)%Q.
      repeat split; eauto using rationals.lt_trans.
      left.
      auto using lt_cross_mul. }
    unfold IRS, zero, IQR in H6.
    apply Specify_classification in H6 as [H6 [ξ [H7 H8]]].
    apply set_proj_injective in H7.
    rewrite <-H7 in H8.
    assert (0 < e*f)%Q by eauto using O2.
    pose proof (rationals.T (e*f) 0).
    tauto.
Qed.

Theorem M2_pos : ∀ a b c, 0 < a → 0 < b → 0 < c → a * (b * c) = (a * b) * c.
Proof.
  intros a b c H H0 H1.
  assert (0 < a * b) as H2 by auto using O2_pos.
  assert (0 < b * c) as H3 by auto using O2_pos.
  unfold mul_pos.
  repeat destruct excluded_middle_informative; try tauto;
    try (contradict n; unfold mul_pos in *;
         repeat destruct excluded_middle_informative; tauto).
  apply set_proj_injective.
  simpl.
  apply Extensionality.
  split; intros H4; apply Specify_classification in H4
    as [H4 [ρ [τ [ξ [H5 [H6 [H7 [H8 [H9 H10]]]]]]]]];
  apply Specify_classification; split; auto.
  - apply Specify_classification in H7
      as [H7 [s [t [ζ [H11 [H12 [H13 [H14 [H15 H16]]]]]]]]].
    apply set_proj_injective in H11.
    subst.
    exists (ρ*s)%Q, t, ξ.
    repeat split; auto using O2.
    + apply Specify_classification.
      split; eauto using in_set.
      exists ρ, s, (ρ*s)%Q.
      repeat split; auto.
      now right.
    + destruct H16 as [H16 | H16], H10 as [H10 | H10].
      * apply (O3 ρ) in H16; auto.
        rewrite M2 in H16.
        left.
        eauto using rationals.lt_trans.
      * subst.
        left.
        apply (O3 ρ) in H16; auto.
        now rewrite M2 in H16.
      * left.
        subst.
        now rewrite M2 in H10.
      * right.
        subst.
        now rewrite M2.
  - apply Specify_classification in H6
      as [H6 [r [s [ζ [H11 [H12 [H13 [H14 [H15 H16]]]]]]]]].
    apply set_proj_injective in H11.
    subst.
    exists r, (s*τ)%Q, ξ.
    repeat split; auto using O2.
    + apply Specify_classification.
      split; eauto using in_set.
      exists s, τ, (s*τ)%Q.
      repeat split; auto.
      now right.
    + destruct H16 as [H16 | H16], H10 as [H10 | H10].
      * apply (O3 τ) in H16; auto.
        rewrite ? (M1 τ), <-M2 in H16.
        left.
        eauto using rationals.lt_trans.
      * subst.
        left.
        apply (O3 τ) in H16; auto.
        now rewrite ? (M1 τ), <-M2 in H16.
      * left.
        subst.
        now rewrite <-M2 in H10.
      * right.
        subst.
        now rewrite M2.
Qed.

Theorem M5 : 1 ≠ 0.
Proof.
  intros H.
  unfold zero, one, IQR, iqr_set in H.
  inversion H as [H0].
  apply Subset_equality_iff in H0 as [H0 H1].
  pose proof zero_lt_1 as H2.    
  apply lt_dense in H2 as [c [H2 H3]].
  contradiction (lt_antisym c 0).
  pose proof (H0 c) as H4.
  rewrite ? Specify_classification in H4.
  destruct H4 as [H4 [ξ [H5 H6]]]; try split; eauto using in_set.
  apply set_proj_injective in H5.
  now subst.
Qed.

Theorem zero_lt_1 : 0 < 1.
Proof.
  unfold lt.
  split.
  - intros z H.
    unfold zero, one, IQR, iqr_set in *.
    apply Specify_classification in H as [H [ξ [H0 H1]]].
    apply Specify_classification.
    split; eauto using rationals.lt_trans, zero_lt_1.
  - intros H.
    apply set_proj_injective in H.
    now contradiction M5.
Qed.

Theorem M3_pos : ∀ a, 0 < a → 1 * a = a.
Proof.
  intros a H.
  unfold mul_pos.
  repeat destruct excluded_middle_informative; try tauto.
  - apply set_proj_injective.
    simpl.
    apply Extensionality.
    split; intros H0.
    + apply Specify_classification in H0
        as [H0 [r [s [ξ [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]].
      subst.
      eapply Dedekind_cut_2; eauto.
      unfold one, IQR, iqr_set in H2.
      apply Specify_classification in H2 as [H2 [ρ [H7 H8]]].
      apply set_proj_injective in H7.
      subst.
      apply (O3 s) in H8; auto.
      rewrite ? (M1 s), M3 in H8.
      destruct H6 as [H6 | H6]; eauto using rationals.lt_trans.
      now subst.
    + apply Specify_classification.
      split; eauto using Dedekind_cut_0.
      apply Dedekind_cut_0 in H0 as H1.
      set (ζ := mkSet _ _ H1 : Q).
      replace z with (value _ ζ) in * by auto.
      destruct (classic (0 < ζ)%Q) as [H2 | H2].
      * apply Dedekind_cut_3 in H0 as [t [H0 H3]].
        exists (ζ * t^-1)%Q, t, ζ.
        assert (t ≠ 0)%Q as H4.
           { intros H4.
             subst.
             contradiction (lt_antisym 0 ζ). }
        repeat split; eauto using O2, inv_lt, rationals.lt_trans.
        -- unfold one, IQR, iqr_set.
           apply Specify_classification.
           split; eauto using in_set.
           exists (ζ * t^-1)%Q.
           split; auto.
           rewrite <-(inv_l t), (M1 ζ); auto.
           eauto using O3, inv_lt, rationals.lt_trans.
        -- rewrite <-M2, inv_l, M1, M3; auto.
           now right.
      * apply pos_nonempty in l as [c [H3 H4]].
        apply pos_nonempty in l0 as [d [H5 H6]].
        exists c, d, ζ.
        repeat split; auto.
        left.
        destruct (rationals.T 0 ζ)
          as [[H7 [H8 H9]] | [[H7 [H8 H9]] | [H7 [H8 H9]]]]; try tauto;
          eauto using rationals.lt_trans, O2.
        rewrite <-H8.
        now apply O2.
  - contradiction n.
    now apply zero_lt_1.
Qed.

Definition inv_pos_set (α : R) :=
  {p in ℚ | ∃ ρ r : Q,
     p = ρ ∧ (1 < r)%Q ∧ ((ρ ≤ 0)%Q ∨ ((0 < ρ)%Q ∧ (ρ*r)^-1 ∉ α))}.

Theorem inv_pos_in : ∀ a, 0 < a → inv_pos_set a ∈ ℝ.
Proof.
  intros a H.
  apply Specify_classification.
  repeat split.
  - apply Powerset_classification.
    intros x H0.
    apply Specify_classification in H0.
    tauto.
  - apply Nonempty_classification.
    exists 0%Q.
    apply Specify_classification.
    split; eauto using in_set.
    exists 0%Q, 2.
    repeat split; eauto using zero_lt_1, one_lt_2, rationals.lt_trans.
    now left; right.
  - pose proof H as H0.
    apply pos_nonempty in H0 as [c [H0 H1]].
    intros H2.
    assert (c^-1 ∈ ℚ) by eauto using in_set.
    rewrite <-H2 in H3.
    apply Specify_classification in H3
      as [H3 [p [r [H4 [H5 [[H6 | H6] | [H6 H7]]]]]]];
      apply set_proj_injective in H4; subst.
    + apply inv_lt in H0.
      pose proof (rationals.T (c^-1) 0).
      tauto.
    + unfold inv in H6.
      repeat destruct constructive_indefinite_description.
      destruct a0.
      unfold rationals.zero, IZQ in H6.
      apply Qequiv in H6; eauto using integers.zero_ne_1.
      * replace (x*0)%Z with 0%Z in * by ring.
        rewrite integers.M3_r in H6.
        contradiction.
      * intros H7.
        subst.
        unfold rationals.zero, IZQ in H0.
        unfold rationals.lt, rationals.sub in H0.
        rewrite neg_wf, add_wf, pos_wf in H0; auto using integers.zero_ne_1.
        -- replace ((0 * 1 + - 0 * x0) * (x0 * 1))%Z with 0%Z in H0 by ring.
           contradiction (integers.lt_irrefl 0).
        -- now rewrite integers.M3_r.
    + contradict H7.
      eapply Dedekind_cut_2; eauto.
      rename H6 into H4.
      assert (0 < r)%Q as H6.
      { eapply (rationals.lt_trans _ 1); auto.
        apply IZQ_lt, integers.zero_lt_1. }
      rewrite <-(rationals.M3 c) at 2.
      rewrite <-(inv_l (c^-1 * r)), <-rationals.M2.
      * rewrite <-(rationals.M3 ((c^-1 * r)^-1)), (rationals.M1 1) at 1.
        apply rationals.O3; eauto using inv_lt, O2.
        rewrite M1, M2, (M1 c), inv_l, M3; auto.
        intros H7.
        subst.
        contradiction (lt_irrefl 0).
      * intros H7.
        symmetry in H7.
        assert (0 < c^-1 * r)%Q by eauto using O2.
        pose proof (rationals.T 0 (c^-1*r)).
        tauto.
  - intros p q H0 H1.
    apply Specify_classification in H0 as [H0 [ρ [r [H2 [H3 [H4 | [H4 H5]]]]]]];
      apply set_proj_injective in H2; subst; apply Specify_classification;
        split; eauto using in_set; exists q, r; repeat split; auto.
    + left.
      destruct H4 as [H4 | H4]; left; eauto using rationals.lt_trans.
      congruence.
    + destruct (classic (q ≤ 0)%Q) as [H2 | H2]; try tauto; right.
      assert (0 < q)%Q as H6.
      { pose proof (rationals.T q 0).
        unfold rationals.le in H2.
        tauto. }
      assert (0 < r)%Q as H7.
      { eapply (rationals.lt_trans _ 1); eauto.
        apply IZQ_lt, integers.zero_lt_1. }
      split; auto.
      eapply Dedekind_cut_5; eauto.
      rewrite <-lt_cross_inv; eauto using O2, rationals.lt_trans.
      rewrite ? (M1 _ r).
      eauto using O3.
  - intros p H0.
    apply Specify_classification in H0
      as [H0 [ρ [r [H1 [H2 [[H3 | H3] | [H3 H4]]]]]]];
      apply set_proj_injective in H1; subst.
    + exists 0%Q.
      split; auto.
      apply Specify_classification.
      split; eauto using in_set.
      exists 0%Q, 2%Q.
      repeat split; auto using one_lt_2.
      now left; right.
    + destruct (Dedekind_cut_6 a) as [c H1].
      exists (c^-1 * r^-1 * r^-1)%Q.
      assert (0 < r)%Q as H4.
      { eapply (rationals.lt_trans _ 1); eauto.
        apply IZQ_lt, integers.zero_lt_1. }
      assert (0 < c)%Q as H3.
      { eapply Dedekind_cut_4; eauto.
        apply pos_nonempty in H as [d [H H3]].
        eauto using Dedekind_cut_2. }
      assert (c ≠ 0%Q) as H5 by eauto using lt_neq.
      assert (r ≠ 0%Q) as H6 by eauto using lt_neq.
      split; eauto 6 using O2, inv_lt.
      apply Specify_classification.
      split; eauto using in_set.
      exists (c^-1 * r^-1 * r^-1)%Q, r.
      repeat split; auto.
      right.
      split; eauto 6 using O2, inv_lt.
      eapply Dedekind_cut_5; eauto.
      rewrite <-M2, inv_l, (M1 _ 1), M3, inv_mul, inv_inv; auto.
      rewrite <-(M3 c), ? (M1 _ c) at 1.
      now apply O3.
    + apply lt_dense in H2 as [c [H2 H5]].
      exists (ρ * r * c^-1)%Q.
      assert (0 < c)%Q as H6.
      { apply (rationals.lt_trans _ 1); auto.
        apply IZQ_lt, integers.zero_lt_1. }
      split.
      * apply lt_div in H5; auto.
        apply (O3 ρ) in H5; auto.
        now rewrite M1, M3, M2 in H5.
      * apply Specify_classification.
        split; eauto using in_set.
        exists (ρ * r * c^-1)%Q, c.
        repeat split; auto.
        right.
        rewrite <-? M2, inv_l, (M1 _ 1), M3; auto using lt_neq.
        split; auto.
        assert (0 < r)%Q.
        { apply (rationals.lt_trans _ 1); eauto.
          apply IZQ_lt, integers.zero_lt_1.
          eauto using rationals.lt_trans. }
        eauto using O2, inv_lt.
Qed.

Definition inv_pos : R → R.
Proof.
  intros a.
  destruct (excluded_middle_informative (0 < a)).
  - exact (mkSet _ _ (inv_pos_in _ l)).
  - exact 0.
Defined.

Notation "a '^-1' " := (inv_pos a) (at level 30, format "a '^-1'") : R_scope.

Lemma pos_not_in_0 : ∀ x : Q, (0 < x)%Q → x ∉ 0.
Proof.
  intros x H H0.
  unfold zero, IQR, iqr_set in H0.
  apply Specify_classification in H0 as [H0 [ξ [H1 H2]]].
  apply set_proj_injective in H1.
  subst.
  contradiction (lt_antisym 0 ξ).
Qed.

Theorem inv_lt : ∀ a, 0 < a → 0 < a^-1.
Proof.
  intros a H.
  unfold lt.
  split.
  - intros z H0.
    unfold zero, IQR in H0.
    apply Specify_classification in H0 as [H0 [ξ [H1 H2]]].
    unfold inv_pos.
    repeat destruct excluded_middle_informative; try tauto.
    apply Specify_classification.
    split; auto.
    exists ξ, 2%Q.
    repeat split; auto using one_lt_2.
    now left; left.
  - pose proof H as H0.
    apply pos_nonempty in H0 as [c [H0 H1]].
    intros H2.
    destruct (Dedekind_cut_6 a).
    assert (0 < x)%Q as H4.
    { destruct (rationals.T 0 x)
        as [[H4 [H5 H6]] | [[H4 [H5 H6]] | [H4 [H5 H6]]]]; try tauto; subst;
        contradiction H3; eauto using Dedekind_cut_2, rationals.lt_trans. }
    apply inv_lt in H4 as H5.
    assert (0 < 2)%Q as H6 by
          eauto using rationals.zero_lt_1, one_lt_2, rationals.lt_trans.
    apply inv_lt in H6 as H7.
    assert ((x^-1 * 2^-1)%Q ∉ 0) as H8 by auto using pos_not_in_0, O2.
    contradiction H8.
    rewrite H2.
    unfold inv_pos, inv_pos_set.
    destruct excluded_middle_informative; try tauto.
    apply Specify_classification.
    split; eauto using in_set.
    exists (x^-1 * 2^-1)%Q, 2%Q.
    repeat split; auto using one_lt_2.
    right.
    split; auto using O2.
    rewrite <-M2, inv_l, M1, M3, inv_inv; auto using lt_neq.
Qed.

Theorem lt_is_in : ∀ (a : R) (b : Q), b < a ↔ b ∈ a.
Proof.
Admitted.

Theorem pow_archimedean : ∀ (a : R) (r : Q),
    0 < a → (1 < r)%Q → ∃ n : Z, (r^n)%Q ∈ a ∧ (r^(n+1))%Q ∉ a.
Proof.
  intros a r H H0.
  apply pos_nonempty in H as [c [H H1]].
  pose proof Dedekind_cut_6 a as [q H2].
  apply (neg_pow_archimedean c r) in H0 as H3; auto.
  apply (pos_pow_archimedean q r) in H0 as H5.
  destruct H3 as [m [H3 H4]], H5 as [n [H5 H6]], (WOP (λ x, (r^(m+x))%Q ∉ a))
        as [x [H7 H8]]; auto.
  assert (0 < r)%Q as H7 by eauto using rationals.lt_trans, rationals.zero_lt_1.
  - intros x H8.
    destruct (integers.T 0 x) as [[H9 _] | [[_ [H9 _]] | [_ [_ H9]]]]; auto.
    + subst.
      contradict H8.
      rewrite integers.A1, integers.A3.
      eauto using Dedekind_cut_2.
    + rewrite pow_add_r in H8; auto using lt_neq.
      contradict H8.
      eapply Dedekind_cut_2; eauto.
      rewrite <-(M3 c), (M1 1).
      apply lt_cross_mul; auto using pow_pos.
      now apply pow_lt_1.
  - exists (n+-m)%Z.
    split.
    + rewrite <-integers.lt_shift.
      eauto using integers.lt_trans.
    + replace (m+(n+-m))%Z with n%Z by ring.
      eauto using Dedekind_cut_5.
  - exists (m+(x+-(1)))%Z.
    split.
    + apply NNPP.
      intros H9.
      pose proof lt_succ (x+-(1)) as H10.
      replace (x+-(1)+1)%Z with x in H10 by ring.
      apply H8 in H9 as [H9 | H9].
      * contradiction (integers.lt_antisym x (x+-(1))).
      * contradiction (integers.lt_irrefl x).
        now rewrite H9 at 1.
    + now replace (m + (x + - (1)) + 1)%Z with (m+x)%Z by ring.
Qed.

Theorem M4_pos : ∀ a, 0 < a → a^-1 * a = 1.
Proof.
  intros a H.
  apply set_proj_injective, Extensionality.
  split; intros H0; unfold mul_pos in H0;
    repeat destruct excluded_middle_informative;
    try tauto; try now apply inv_lt in l.
  - apply Specify_classification in H0
      as [H0 [r [s [ξ [H1 [H2 [H3 [H4 [H5 H6]]]]]]]]].
    subst.
    unfold inv_pos, inv_pos_set, IQR in H2 |- *.
    repeat destruct excluded_middle_informative; try tauto.
    simpl in *.
    apply Specify_classification in H2 as [H2 [p [q [H7 [H8 [H9 | [H9 H10]]]]]]];
      apply set_proj_injective in H7; subst.
    + destruct H9 as [H9 | H9].
      * contradiction (rationals.lt_antisym 0 p).
      * subst.
        contradiction (rationals.lt_irrefl 0).
    + assert (0 < q)%Q as H1 by
            eauto using rationals.lt_trans, rationals.zero_lt_1.
      apply inv_lt_1 in H8; auto.
      eapply Dedekind_cut_4 in H10; eauto.
      rewrite <-inv_mul in H10.
      apply (O3 (p^-1)) in H8; auto using rationals.inv_lt.
      rewrite (rationals.M1 _ 1), rationals.M3 in H8.
      assert (s < p^-1)%Q as H11 by eauto using rationals.lt_trans.
      apply (O3 p) in H11; auto.
      rewrite (M1 _ (p^-1)), inv_l in H11; auto using lt_neq.
      apply Specify_classification.
      split; auto.
      exists ξ.
      split; auto.
      destruct H6 as [H6 | H6]; eauto using rationals.lt_trans.
      congruence.
  - unfold IQR, one in H0.
    simpl in H0.
    unfold iqr_set in H0.
    apply Specify_classification in H0 as [H0 [ξ [H1 H2]]].
    subst.
    set (w := (ξ^-1)%Q).
    apply NNPP; intros H1.
    assert (0 < ξ)%Q as H3.
    { destruct (rationals.T 0 ξ) as [[H4 _] | [[_ [H4 _]] | [_ [_ H4]]]];
        try tauto; contradict H1.
      + unfold mul_pos, mul_pos_set.
        repeat destruct excluded_middle_informative; try contradiction.
        * simpl.
          apply Specify_classification.
          split; auto.
          apply pos_nonempty in l as [c [H1 H5]].
          apply pos_nonempty in l0 as [d [H6 H7]].
          exists c, d, ξ.
          repeat split; auto; subst; left; eauto using O2.
        * now apply inv_lt in l.
      + unfold mul_pos, mul_pos_set.
        repeat destruct excluded_middle_informative; try contradiction.
        * simpl.
          apply Specify_classification.
          split; auto.
          apply pos_nonempty in l as [c [H1 H5]].
          apply pos_nonempty in l0 as [d [H6 H7]].
          exists c, d, ξ.
          repeat split; auto; left; eauto using rationals.lt_trans, O2.
        * now apply inv_lt in l. }
    assert (1 < w)%Q as H4.
    { rewrite inv_lt_1; unfold w; auto using rationals.inv_lt.
      now rewrite inv_inv. }
    contradict H1.
    pose proof H4 as H1.
    apply square_in_interval in H4 as [r [H4 [H5 H6]]].
    assert (1 < r)%Q as H7 by auto using square_ge_1.
    pose proof H7 as H8.
    eapply pow_archimedean in H8 as [n [H9 H10]]; eauto.
    unfold mul_pos.
    repeat destruct excluded_middle_informative; try tauto;
      try now (exfalso; auto using inv_lt).
    apply Specify_classification.
    split; auto.
    exists (r^(-(n+2))), (r^n), ξ.
    repeat split; auto using pow_pos.
    + unfold inv_pos.
      destruct excluded_middle_informative; try tauto.
      apply Specify_classification.
      split; eauto using in_set.
      exists (r^(-(n+2))), r.
      repeat split; auto.
      right.
      split.
      * now apply pow_pos.
      * rewrite <-inv_mul, <-? inv_pow, <-pow_mul_r, <-pow_add_r;
          auto using lt_neq.
        replace (-(n+2)*-(1)+-(1))%Z with (n+1)%Z by ring; auto.
    + unfold w in *.
      rewrite <-pow_add_r; auto using lt_neq.
      left.
      replace (-(n+2)+n)%Z with (-(2))%Z by ring.
      apply (O3 (ξ * r^(-(2)))) in H6; auto using O2, pow_pos.
      rewrite <-M2, (M1 _ (ξ^-1)), ? M2, inv_l, M3 in H6; auto using lt_neq.
      rewrite <-(pow_1_r r) in H6 at 2 3.
      rewrite <-(M2 ξ), <-pow_add_r, <-M2, <-pow_add_r in H6; auto using lt_neq.
      replace (-(2)+1+1)%Z with 0%Z in H6 by ring.
      now rewrite pow_0_r, M1, M3 in H6.
Qed.

Theorem D1_pos : ∀ a b c, 0 < a → 0 < b → 0 < c → (a + b) * c = a * c + b * c.
Proof.
Admitted.
