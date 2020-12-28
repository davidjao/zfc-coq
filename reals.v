Require Export rationals.

Definition ℝ := {α in P ℚ |
                  α ≠ ∅ ∧ α ≠ ℚ ∧
                  (∀ p q : Q, value _ p ∈ α → q < p → value _ q ∈ α) ∧
                  (∀ p : Q, value _ p ∈ α → ∃ r : Q, p < r ∧ value _ r ∈ α)}.

Theorem Dedekind_cut_1 : ∀ α, α ∈ ℝ → α ≠ ∅.
Proof.
  intros α H.
  now apply Specify_classification in H as [H [H0 [H1 [H2 H3]]]].
Qed.

Theorem Dedekind_cut_2 : ∀ α,
    α ∈ ℝ → ∀ p q : Q, value _ p ∈ α → value _ q ∉ α → p < q.
Proof.
  intros α H p q H0 H1.
  apply Specify_classification in H as [H [H2 [H3 [H4 H5]]]].
  destruct (T p q) as [[H6 [H7 H8]] | [[H6 [H7 H8]] | [H6 [H7 H8]]]]; subst;
    try tauto.
  exfalso; eauto.
Qed.

Theorem Dedekind_cut_3 : ∀ α,
    α ∈ ℝ → ∀ r s : Q, value _ r ∉ α → r < s → value _ s ∉ α.
Proof.
  intros α H r s H0 H1 H2.
  apply Specify_classification in H as [H [H3 [H4 [H5 H6]]]].
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

Definition inz_set (q : Q) := {x in ℚ | ∃ ξ : Q, value _ ξ = x ∧ (ξ < q)%Q}.

Theorem inz_in : ∀ q, inz_set q ∈ ℝ.
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
  - intros H.
    apply Subset_equality_iff in H as [H H0].
    pose proof (H0 (value _ (q+1)) (in_set _ _)) as H1.
    apply Specify_classification in H1 as [H1 [ξ [H2 H3]]].
    replace ξ with (q+1) in * by eauto using set_proj_injective.
    contradiction (lt_antisym q (q+1)).
    rewrite <-(rationals.A3 q), rationals.A1 at 1.
    apply O1, IZQ_lt, zero_lt_1.
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
Definition zero := IQR 0.

Coercion IQR : Q >-> R.

Notation "0" := zero : R_scope.

Definition add_set : R → R → set.
Proof.
  intros α β.
  exact {x in ℚ |
          ∃ r s,
           value _ (r+s) = x ∧ value _ r ∈ value _ α ∧ value _ s ∈ value _ β}.
Defined.


Lemma not_Q_subset : ∀ α, ¬ ℚ ⊊ value ℝ α.
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

Lemma not_Q_eq : ∀ α, ℚ ≠ value ℝ α.
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
    exists (value _ (mkSet _ _ H9 + mkSet _ _ H10)).
    apply Specify_classification.
    split; auto using in_set.
    exists (mkSet _ _ H9), (mkSet _ _ H10).
    split; simpl; auto.
  - destruct (proper_subset_inhab ℚ (value _ α))
      as [r' [H H0]], (proper_subset_inhab ℚ (value _ β)) as [s' [H1 H2]];
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
    split; auto using in_set.
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
    rewrite <-H3 in *.
    split; auto.
    exists (r+t)%Q, u.
    repeat split; auto.
    + now rewrite <-rationals.A2.
    + apply Specify_classification; split; auto using in_set.
      now exists r, t.
  - apply Specify_classification in H1 as [H1 [t [u [H3 [H4 H5]]]]].
    apply set_proj_injective in H3.
    rewrite <-H3 in *.
    split; auto.
    exists t, (u+s)%Q.
    repeat split; auto.
    + now rewrite rationals.A2.
    + apply Specify_classification; split; auto using in_set.
      now exists u, s.
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
    rewrite <-H0, <-H3, <-(A3 r), (rationals.A1 0), <-rationals.A2.
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
      apply Specify_classification; split; auto using in_set.
      exists (ζ+-r)%Q.
      split; auto.
      rewrite <-(A4 r), ? (rationals.A1 _ (-r)).
      now apply O1.
Qed.

Definition neg_set : R → set.
Proof.
  intros α.
  exact {p in ℚ |
          ∃ ρ r : Q,
           value ℚ ρ = p ∧ (0 < r)%Q ∧ value ℚ (-ρ-r)%Q ∉ value ℝ α}.
Defined.

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
    destruct (proper_subset_inhab ℚ (value ℝ α)) as [s [H4 H5]]; auto.
    { intros [H4 H5].
      contradict H1.
      now apply Subset_equality_iff. }
    set (σ := mkSet _ _ H4 : Q).
    exists (value _ (-σ-1)).
    apply Specify_classification.
    split; auto using in_set.
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
    split; auto using in_set.
    exists q, r.
    repeat split; auto.
    contradict H3.
    pose proof in_set _ α as H4.
    apply Specify_classification in H4 as [H4 [H5 [H6 [H7 H8]]]].
    eapply H7; eauto.
    apply (rationals.O1 (-p-q-r)%Q) in H0.
    now ring_simplify in H0.
  - intros p H.
    apply Specify_classification in H as [H [ρ [r [H1 [H2 H3]]]]].
    apply set_proj_injective in H1.
    subst.
    assert (p+0 < p+r)%Q as H0 by now apply O1.
    ring_simplify in H0.
    apply lt_dense in H0 as [t [H0 H1]].
    exists t.
    split; auto.
    apply Specify_classification.
    split; auto using in_set.
    exists t, (p+r-t).
    repeat split; auto.
    + apply (O1 (-t)) in H1.
      now rewrite ? (rationals.A1 (-t)), rationals.A4 in H1.
    + now replace (-t-(p+r-t)) with (-p-r) by ring.
Qed.

Definition neg : R → R.
Proof.
  intros a.
  exact (mkSet _ _ (neg_in a)).
Defined.

