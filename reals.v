Require Export rationals.

Definition ℝ := {α in P ℚ | α ≠ ∅ ∧ α ≠ ℚ ∧
                            (∀ p q : Q, p ∈ α → q < p → q ∈ α) ∧
                            (∀ p : Q, p ∈ α → ∃ r : Q, p < r ∧ r ∈ α)}.

Theorem Dedekind_cut_1 : ∀ α, α ∈ ℝ → α ≠ ∅.
Proof.
  intros α H.
  now apply Specify_classification in H as [H [H0 [H1 [H2 H3]]]].
Qed.

Theorem Dedekind_cut_2 : ∀ α, α ∈ ℝ → ∀ p q : Q, p ∈ α → q ∉ α → p < q.
Proof.
  intros α H p q H0 H1.
  apply Specify_classification in H as [H [H2 [H3 [H4 H5]]]].
  destruct (T p q) as [[H6 [H7 H8]] | [[H6 [H7 H8]] | [H6 [H7 H8]]]]; subst;
    try tauto.
  exfalso; eauto.
Qed.

Theorem Dedekind_cut_3 : ∀ α, α ∈ ℝ → ∀ r s : Q, r ∉ α → r < s → s ∉ α.
Proof.
  intros α H r s H0 H1 H2.
  apply Specify_classification in H as [H [H3 [H4 [H5 H6]]]].
  eauto.
Qed.

Definition R := elts ℝ.

Definition IRS (a : R) := value ℝ a : set.
Coercion IRS : R >-> set.

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
        by eauto using Dedekind_cut_2, in_set.
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
      apply (H15 σ); eauto using Dedekind_cut_2, in_set.
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
    replace (q-(q-1)) with 1 by field.
    unfold one.
    rewrite pos_wf, integers.M3; auto using zero_ne_1, zero_lt_1.
  - intros H.
    apply Subset_equality_iff in H as [H H0].
    pose proof (H0 (q+1) (in_set _ _)) as H1.
    apply Specify_classification in H1 as [H1 [ξ [H2 H3]]].
    replace ξ with (q+1) in * by eauto using set_proj_injective.
    contradiction (lt_antisym q (q+1)).
    rewrite <-(rationals.A3 q), rationals.A1 at 1.
    apply O1, IZQ_lt, zero_lt_1.
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
    assert (r < ρ)%Q as H9 by eauto using Dedekind_cut_2, in_set.
    assert (s < σ)%Q as H10 by eauto using Dedekind_cut_2, in_set.
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
    repeat split; try apply IZQ_lt; auto using zero_lt_1.
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
      eapply Dedekind_cut_3; eauto using in_set.
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
        exact zero_lt_1. }
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
    { eapply Dedekind_cut_3; eauto using in_set.
      unfold sub in *.
      rewrite <-(rationals.A3 (-s)) at 2.
      rewrite <-(rationals.A4 q), <-rationals.A2, <-(rationals.A1 (-q)),
      <-(rationals.A3 (-q+-s)), ? (rationals.A1 _ (-q+-s)) at 1.
      now apply rationals.O1. }
    eapply Dedekind_cut_2 in H0; eauto using in_set.
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
    { eapply integers.lt_trans; try now apply zero_lt_1.
      rewrite <-(integers.A3_r 1) at 1.
      apply integers.O1, zero_lt_1. }
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
          auto using zero_ne_1; ring.
Qed.

Definition mul_pos_set (a b : R) :=
  {x in ℚ | (∃ r s ξ : Q, x = ξ ∧ r ∈ a ∧ s ∈ b ∧ 0 < r ∧ 0 < s ∧ ξ < r * s)%Q}.

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

Lemma Dedekind_cut_4 : ∀ a : R, ∃ q : Q, q ∉ a.
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
    apply lt_sub_pos, IZQ_lt, zero_lt_1.
  - destruct (Dedekind_cut_4 a) as [c H1], (Dedekind_cut_4 b) as [d H2].
    intros H3.
    apply Subset_equality_iff in H3 as [H3 H4].
    assert (c*d ∈ mul_pos_set a b) as H5 by eauto using in_set.
    apply Specify_classification in H5
      as [H5 [r [s [ξ [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]].
    assert (r < c)%Q as H12 by eauto using Dedekind_cut_2, in_set.
    assert (s < d)%Q as H13 by eauto using Dedekind_cut_2, in_set.
    assert (0 < c)%Q as H14 by eauto using rationals.lt_trans.
    apply set_proj_injective in H6.
    subst.
    contradiction (lt_antisym (c*d) (r*s)).
    apply (O3 s) in H12; auto.
    apply (O3 c) in H13; auto.
    rewrite ? (M1 s) in H12.
    eauto using rationals.lt_trans.
  - intros p q H1 H2.
    apply Specify_classification in H1
      as [H1 [r [s [ξ [H3 [H4 [H5 [H6 [H7 H8]]]]]]]]].
    apply Specify_classification.
    split; unfold IQS; auto using in_set.
    exists r, s, q.
    apply set_proj_injective in H3.
    subst.
    repeat split; eauto using rationals.lt_trans.
  - intros p H1.
    apply Specify_classification in H1
      as [H1 [r [s [ξ [H3 [H4 [H5 [H6 [H7 H8]]]]]]]]].
    apply lt_dense in H8 as [c [H8 H9]].
    exists c.
    apply set_proj_injective in H3.
    subst.
    split; auto.
    apply Specify_classification.
    split; unfold IQS; auto using in_set.
    now exists r, s, c.
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
Admitted.

Theorem M2_pos : ∀ a b c, 0 < a → 0 < b → 0 < c → a * (b * c) = (a * b) * c.
Proof.
Admitted.

Theorem M3_pos : ∀ a, 0 < a → 1 * a = a.
Proof.
Admitted.

Definition inv_pos_set (a : R) :=
  {x in ℚ | (∃ r ξ : Q, x = ξ ∧ r ∈ a ∧ 0 < r ∧ ξ < r^-1)%Q}.

Theorem inv_pos_in : ∀ a, 0 < a → inv_pos_set a ∈ ℝ.
Proof.
Admitted.

Definition inv_pos : R → R.
Proof.
  intros a.
  destruct (excluded_middle_informative (0 < a)).
  - exact (mkSet _ _ (inv_pos_in _ l)).
  - exact 0.
Defined.

Notation "a '^-1' " := (inv_pos a) (at level 35, format "a '^-1'") : R_scope.

Theorem M4_pos : ∀ a, 0 < a → a^-1 * a = 1.
Proof.
Admitted.

Theorem M5 : 1 ≠ 0.
Proof.
Admitted.

Theorem D1 : ∀ a b c, 0 < a → 0 < b → 0 < c → (a + b) * c = a * c + b * c.
Proof.
Admitted.
