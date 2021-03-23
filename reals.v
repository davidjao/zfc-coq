Set Warnings "-notation-overridden,-ambiguous-paths".
Require Export rationals.

Definition 𝐑 := {α in P 𝐐 | α ≠ ∅ ∧ α ≠ 𝐐 ∧
                            (∀ p q : Q, p ∈ α → q < p → q ∈ α) ∧
                            ∀ p : Q, p ∈ α → ∃ r : Q, p < r ∧ r ∈ α}.

Definition R := elts 𝐑.

Definition IRS (a : R) := elt_to_set a : set.
Coercion IRS : R >-> set.

Lemma Dedekind_cut_0 : ∀ (α : R) (p : set), p ∈ α → p ∈ 𝐐.
Proof.
  intros α p H.
  pose proof elts_in_set α as H0.
  apply Specify_classification in H0 as [H0 [H1 [H2 [H3 H4]]]].
  apply Powerset_classification in H0.
  eauto.
Qed.

Lemma Dedekind_cut_1 : ∀ α : R, ∅ ≠ α.
Proof.
  intros α H.
  pose proof elts_in_set α as H0.
  apply Specify_classification in H0 as [H0 [H1 [H2 [H3 H4]]]].
  now contradict H1.
Qed.

Lemma Dedekind_cut_2 : ∀ (α : R) (p q : Q), p ∈ α → q < p → q ∈ α.
Proof.
  intros α.
  pose proof elts_in_set α as H1.
  now apply Specify_classification in H1 as [H1 [H2 [H3 [H4 H5]]]].
Qed.

Lemma Dedekind_cut_3 : ∀ (α : R) (p : Q), p ∈ α → ∃ r : Q, p < r ∧ r ∈ α.
Proof.
  intros α.
  pose proof elts_in_set α as H0.
  now apply Specify_classification in H0 as [H0 [H1 [H2 [H3 H4]]]].
Qed.

Lemma Dedekind_cut_4 : ∀ α : R, ∀ p q : Q, p ∈ α → q ∉ α → p < q.
Proof.
  intros α p q H H0.
  pose proof elts_in_set α as H1.
  apply Specify_classification in H1 as [H1 [H2 [H3 [H4 H5]]]].
  destruct (T p q) as [[H6 _] | [[_ [H6 _]] | [_ [_ H6]]]]; subst; try tauto.
  exfalso; eauto.
Qed.

Lemma Dedekind_cut_5 : ∀ α : R, ∀ r s : Q, r ∉ α → r < s → s ∉ α.
Proof.
  intros α r s H H0 H1.
  pose proof elts_in_set α as H2.
  apply Specify_classification in H2 as [H2 [H3 [H4 [H5 H6]]]].
  eauto.
Qed.

Lemma Dedekind_cut_6 : ∀ a : R, ∃ q : Q, q ∉ a.
Proof.
  intros α.
  pose proof elts_in_set α as H.
  apply Specify_classification in H as [H [H0 [H1 [H2 H3]]]].
  apply Powerset_classification in H.
  assert (𝐐 ≠ α) as H4 by (now contradict H1).
  apply not_proper_subset_inhab in H4 as [z [H4 H5]].
  - exists (exist H4 : Q); auto.
  - contradict H4.
    destruct H4 as [H4 H5].
    now apply Subset_equality_iff.
Qed.

Declare Scope R_scope.
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
  apply Dedekind_cut_0 in H1 as H3.
  split.
  - intros q H4.
    apply Dedekind_cut_0 in H4 as H5.
    replace q with ((exist H5 : Q) : set) in * by auto.
    replace p with ((exist H3 : Q) : set) in * by auto.
    eauto using Dedekind_cut_2, Dedekind_cut_4.
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

Theorem lub : ∀ A, A ⊂ 𝐑 → A ≠ ∅ → (∃ β : R, ∀ α : R, α ∈ A → α ≤ β) →
                   ∃ γ : R, (∀ α : R, α ∈ A → α ≤ γ) ∧
                            ∀ δ : R, (∀ α : R, α ∈ A → α ≤ δ) → γ ≤ δ.
Proof.
  intros A H H0 [β H1].
  set (g := ⋃ A).
  assert (g ∈ 𝐑) as H2.
  { apply Specify_classification.
    repeat split.
    - apply Powerset_classification.
      intros z H2.
      apply Union_classification in H2 as [a [H2 H3]].
      now apply (Dedekind_cut_0 (exist (H _ H2))).
    - apply Nonempty_classification in H0 as [z H0].
      set (ζ := (exist (H _ H0)) : R).
      pose proof Dedekind_cut_1 ζ as H2.
      rewrite neq_sym in H2.
      apply Nonempty_classification in H2 as [x H2].
      apply Nonempty_classification.
      exists x.
      apply Union_classification; eauto.
    - intros H2.
      destruct β as [b B].
      pose proof B as H3.
      apply Specify_classification in H3 as [H3 [H4 [H5 [H6 H7]]]].
      contradict H5.
      apply Subset_equality_iff.
      split.
      + now rewrite Powerset_classification in H3.
      + rewrite <-H2.
        intros z H8.
        apply Union_classification in H8 as [x [H8 H9]].
        destruct (H1 (exist (H _ H8)) H8) as [H10 | H10].
        * now apply H10.
        * inversion H10.
          congruence.
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
  set (γ := exist H2 : R).
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
    set (α := exist (H _ H7) : R).
    apply (H3 α) in H7 as H10.
    unfold le in H10.
    assert (¬ δ < α) as H12 by (pose proof (T α δ); tauto).
    contradict H12.
    split.
    + intros z H12.
      apply (Dedekind_cut_0 α) in H9 as H13.
      apply Dedekind_cut_0 in H12 as H17.
      replace s with ((exist H13 : Q) : set) in * by auto.
      replace z with ((exist H17 : Q) : set) in * by auto.
      eapply Dedekind_cut_2; eauto using Dedekind_cut_4.
    + intros H12.
      rewrite H12 in H8.
      contradiction.
Qed.

Definition iqr_set (q : Q) := {x of type 𝐐 | (x < q)%Q}.

Theorem iqr_in : ∀ q, iqr_set q ∈ 𝐑.
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
    rewrite despecify, (ordered_rings.lt_shift ℚ_ring_order); simpl.
    split; unfold IQS; auto using elts_in_set.
    replace (q+-(q-1)) with 1 by field.
    apply (ordered_rings.zero_lt_1 ℚ_ring_order).
  - intros H.
    assert (q+1 ∈ 𝐐) as H1 by (unfold IQS; auto using elts_in_set).
    rewrite <-H in H1.
    unfold iqr_set in *.
    apply Specify_classification in H1 as [H1 H2].
    rewrite despecify in H2.
    contradiction (lt_antisym ℚ_ring_order q (q+1)).
    apply (lt_succ ℚ_ring_order).
  - intros p x H H0.
    apply Specify_classification in H as [H H1].
    rewrite despecify in *.
    apply Specify_classification.
    split; unfold IQS; auto using elts_in_set.
    rewrite despecify.
    eauto using rationals.lt_trans.
  - intros p H.
    apply Specify_classification in H as [H H0].
    rewrite despecify in *.
    destruct (lt_dense p q) as [r H2]; auto.
    exists r.
    split; try tauto.
    apply Specify_classification.
    split; unfold IQS; auto using elts_in_set.
    now rewrite despecify in *.
Qed.

Definition IQR (q : Q) := (exist (iqr_in q)) : R.
Definition zero := IQR 0.

Coercion IQR : Q >-> R.

Notation "0" := zero : R_scope.

Definition add_set (α β : R) := {x in 𝐐 | ∃ r s, x = r + s ∧ r ∈ α ∧ s ∈ β}.

Lemma not_Q_subset : ∀ α : R, ¬ 𝐐 ⊊ α.
Proof.
  intros α [H H0].
  contradict H0.
  apply Subset_equality_iff; split; auto.
  intros z H0.
  eauto using Dedekind_cut_0.
Qed.

Lemma not_Q_eq : ∀ α : R, 𝐐 ≠ α.
Proof.
  intros α H.
  pose proof elts_in_set α as H0.
  apply Specify_classification in H0 as [H0 [H1 [H2 H3]]].
  now contradict H2.
Qed.

Theorem add_in : ∀ α β, add_set α β ∈ 𝐑.
Proof.
  intros α β.
  apply Specify_classification.
  repeat split; unfold add_set.
  - apply Powerset_classification.
    intros z H.
    now apply Specify_classification in H as [H H0].
  - apply Nonempty_classification.
    pose proof (Dedekind_cut_1 α) as H.
    pose proof (Dedekind_cut_1 β) as H0.
    apply neq_sym, Nonempty_classification in H as [x H].
    apply neq_sym, Nonempty_classification in H0 as [y H0].
    apply Dedekind_cut_0 in H as H1.
    apply Dedekind_cut_0 in H0 as H2.
    exists (exist H1 + exist H2).
    apply Specify_classification.
    split; eauto using elts_in_set.
  - destruct (not_proper_subset_inhab 𝐐 α)
      as [r' [H H0]], (not_proper_subset_inhab 𝐐 β) as [s' [H1 H2]];
    auto using not_Q_subset, not_Q_eq.
    intros H3.
    apply Subset_equality_iff in H3 as [H3 H4].
    set (ρ := exist H : Q).
    set (σ := exist H1 : Q).
    pose proof (elts_in_set (ρ + σ)) as H5.
    apply H4, Specify_classification in H5 as [H5 [r [s [H6 [H7 H8]]]]].
    assert (r + s < ρ + σ)%Q.
    { apply (lt_cross_add ℚ_ring_order); simpl;
        eauto using Dedekind_cut_4. }
    replace (ρ+σ)%Q with (r+s)%Q in *; eauto using set_proj_injective.
    contradiction (lt_irrefl ℚ_ring_order (r+s)).
  - intros p q H H0.
    apply Specify_classification in H as [H [r [s [H1 [H2 H3]]]]].
    apply set_proj_injective in H1.
    subst.
    apply Specify_classification.
    split; unfold IQS; auto using elts_in_set.
    exists (q+-s), s.
    repeat split; auto.
    + f_equal.
      ring.
    + eapply Dedekind_cut_2; eauto.
      rewrite (ordered_rings.lt_shift ℚ_ring_order) in *; simpl in *.
      now replace (r+-(q+-s)) with (r+s+-q) by ring.
  - intros p H.
    apply Specify_classification in H as [H [r [s [H0 [H1 H2]]]]].
    apply set_proj_injective in H0.
    subst.
    apply Dedekind_cut_3 in H1 as [t [H1 H3]].
    exists (t+s).
    split.
    + rewrite ? (rationals.A1 _ s).
      now apply O1.
    + apply Specify_classification.
      split; eauto using elts_in_set.
Qed.

Definition add : R → R → R.
Proof.
  intros a b.
  exact (exist (add_in a b)).
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
    subst.
    split; auto.
    exists (r+t)%Q, u.
    repeat split; auto.
    + now rewrite <-rationals.A2.
    + apply Specify_classification; split; eauto using elts_in_set.
  - apply Specify_classification in H1 as [H1 [t [u [H3 [H4 H5]]]]].
    apply set_proj_injective in H3.
    subst.
    split; auto.
    exists t, (u+s)%Q.
    repeat split; auto.
    + now rewrite rationals.A2.
    + apply Specify_classification; split; eauto using elts_in_set.
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
    apply Specify_classification in H2 as [H2 H3].
    rewrite despecify in H3.
    subst.
    eapply Dedekind_cut_2; eauto.
    rewrite <-(A3 r), (rationals.A1 0), <-rationals.A2, rationals.A3.
    now apply O1.
  - apply Specify_classification.
    apply Dedekind_cut_0 in H as H0.
    split; auto.
    set (ζ := (exist H0) : Q).
    replace z with (ζ : set) in * by auto.
    apply Dedekind_cut_3 in H as [r [H H1]].
    exists r, (ζ+-r)%Q.
    repeat split; auto.
    + apply f_equal.
      now ring_simplify.
    + simpl.
      apply Specify_classification; split; eauto using elts_in_set.
      rewrite despecify.
      rewrite <-(A4 r), ? (rationals.A1 _ (-r)).
      now apply O1.
Qed.

Definition neg_set (α : R) :=
  {p in 𝐐 | ∃ ρ r : Q, p = ρ ∧ (0 < r)%Q ∧ (- ρ - r)%Q ∉ α}.

Theorem neg_in : ∀ a, neg_set a ∈ 𝐑.
Proof.
  intros α.
  apply Specify_classification.
  repeat split.
  - apply Powerset_classification.
    intros z H.
    now apply Specify_classification in H.
  - apply Nonempty_classification.
    pose proof elts_in_set α as H; simpl in *.
    apply Specify_classification in H as [H [H0 [H1 [H2 H3]]]].
    apply Powerset_classification in H.
    destruct (not_proper_subset_inhab 𝐐 α) as [s [H4 H5]]; auto.
    { intros [H4 H5].
      contradict H1.
      now apply Subset_equality_iff. }
    set (σ := exist H4 : Q).
    exists (-σ-1).
    apply Specify_classification.
    split; unfold IQS; auto using elts_in_set.
    exists (-σ-1), 1.
    repeat split; try apply (ordered_rings.zero_lt_1 ℚ_ring_order).
    now replace (-(-σ-1)-1)%Q with σ by ring.
  - pose proof Dedekind_cut_1 α as H.
    apply neq_sym in H.
    apply Nonempty_classification in H as [s H].
    apply Dedekind_cut_0 in H as H0.
    set (σ := (exist H0) : Q).
    intros H1.
    pose proof (elts_in_set (-σ)) as H2; simpl in *.
    rewrite <-H1 in H2.
    pose proof H2 as H3.
    apply Specify_classification in H3 as [H3 [p [r [H4 [H5 H6]]]]].
    contradict H6.
    apply (Dedekind_cut_2 _ σ); auto.
    apply set_proj_injective in H4.
    rewrite <-H4, (ordered_rings.lt_shift ℚ_ring_order); simpl.
    now replace (σ+-(--σ-r))%Q with r by ring.
  - intros p q H H0.
    apply Specify_classification in H as [H [ρ [r [H1 [H2 H3]]]]].
    apply set_proj_injective in H1.
    subst.
    apply Specify_classification.
    split; unfold IQS; auto using elts_in_set.
    exists q, r.
    repeat split; auto.
    contradict H3.
    apply (Dedekind_cut_2 _ (-q-r)); auto.
    rewrite (ordered_rings.lt_shift ℚ_ring_order) in *; simpl in *.
    now replace (-q-r+-(-ρ-r))%Q with (ρ+-q)%Q by ring.
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
    split; unfold IQS; auto using elts_in_set.
    exists t, (ρ+r-t).
    repeat split; auto.
    + apply (O1 (-t)) in H1.
      now rewrite ? (rationals.A1 (-t)), rationals.A4 in H1.
    + now replace (-t-(ρ+r-t)) with (-ρ-r) by ring.
Qed.

Definition neg : R → R.
Proof.
  intros a.
  exact (exist (neg_in a)).
Defined.

Notation "- a" := (neg a) : R_scope.

Theorem cut_archimedean : ∀ (α : R) (b : Q),
    (0 < b)%Q → ∃ n : Z, n * b ∈ α ∧ (n + 1) * b ∉ α.
Proof.
  intros α b H.
  pose proof (elts_in_set α) as H0; simpl in *.
  apply Specify_classification in H0 as [H0 [H1 [H2 [H3 H4]]]].
  apply Nonempty_classification in H1 as [x H1].
  apply Powerset_classification in H0.
  assert (x ∈ 𝐐) as H5 by eauto.
  set (ξ := exist H5 : Q).
  destruct (Q_archimedean ξ b) as [k [H6 H7]]; auto.
  destruct (WOP (λ m, (k + m)%Z * b ∉ α)) as [n [H8 H9]].
  - intros m H8.
    apply NNPP.
    contradict H8.
    apply (le_not_gt ℤ_order) in H8 as [H8 | H8]; simpl in *.
    + apply (H3 ξ); auto.
      destruct H6 as [H6 | H6]; rewrite <-IZQ_add; ring_simplify.
      * apply (rationals.lt_trans _ (k*b)); auto.
        rewrite (ordered_rings.lt_shift ℚ_ring_order); simpl.
        replace (k*b+-(k*b+m*b))%Q with (-m*b)%Q by field.
        apply O2; auto.
        now rewrite IZQ_lt, (lt_neg_0 ℚ_ring_order) in H8.
      * rewrite <-H6, (ordered_rings.lt_shift ℚ_ring_order); simpl.
        replace (k*b+-(k*b+m*b))%Q with (-m*b)%Q by field.
        apply O2; auto.
        now rewrite IZQ_lt, (lt_neg_0 ℚ_ring_order) in H8.
    + subst.
      rewrite (A3_r ℤ).
      destruct H6 as [H6 | H6].
      * apply (H3 ξ); auto.
      * rewrite H6; auto.
  - destruct (not_proper_subset_inhab 𝐐 α) as [z [H8 H9]]; auto.
    { intros [H8 H9].
      contradict H9.
      now apply Subset_equality_iff. }
    set (ζ := exist H8 : Q).
    destruct (Q_archimedean ζ b) as [m [H10 H11]]; auto.
    exists (m - k + 1)%Z.
    split.
    + replace (m-k+1)%Z with (m+1+-k)%Z by ring.
      rewrite <-(ordered_rings.lt_shift ℤ_order); simpl.
      destruct (integers.T k (m+1)) as [H12 | [H12 | H12]]; intuition;
        contradict H9; replace z with (ζ : set); try apply (H3 ξ); auto.
      * rewrite H12, <-IZQ_add in H6.
        destruct H6 as [H6 | H6]; eauto using rationals.lt_trans.
        now rewrite <-H6.
      * apply IZQ_lt, (O3 ℚ_ring_order b) in H15; auto.
        rewrite ? (M1 b), <-IZQ_add in H15.
        assert (ζ < k * b)%Q as H9 by eauto using rationals.lt_trans.
        destruct H6 as [H6 | H6]; eauto using rationals.lt_trans.
        now rewrite <-H6.
    + replace (k+(m-k+1))%Z with (m+1)%Z by ring.
      eapply Dedekind_cut_5.
      * replace z with (ζ : set) in *; eauto.
      * now rewrite <-IZQ_add.
  - exists (k+(n+-1))%Z.
    rewrite ? IZQ_add.
    split.
    + apply NNPP.
      intros H10.
      pose proof (H9 _ H10) as H11.
      rewrite (le_not_gt ℤ_order) in H11; simpl in *.
      contradict H11.
      rewrite (ordered_rings.lt_shift ℤ_order); simpl.
      replace (n+-(n+-1))%Z with 1%Z by ring.
      apply integers.zero_lt_1.
    + replace 1 with (IZQ 1) by auto.
      now rewrite IZQ_add, <-? integers.A2, (integers.A1 _ 1), integers.A4,
      (A3_r ℤ).
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
    { eapply Dedekind_cut_5; eauto.
      rewrite (ordered_rings.lt_shift ℚ_ring_order) in *; simpl in *.
      now replace (-s+-(-s-q))%Q with (q+-0)%Q by ring. }
    eapply Dedekind_cut_4 in H0; eauto.
    apply Specify_classification.
    rewrite despecify.
    split; eauto.
    rewrite (ordered_rings.lt_shift ℚ_ring_order) in *; simpl in *.
    now replace (0+-(r+s))%Q with (-s+-r)%Q by ring.
  - rewrite (reify H), despecify in *.
    set (v := exist H : Q) in *.
    set (w := (-v * 2^-1)%Q).
    assert (0 < 2)%Z as H1 by apply (ordered_rings.zero_lt_2 ℤ_order).
    assert (0 < w)%Q as H2.
    { unfold w.
      apply rationals.O2; try now apply (lt_neg_0 ℚ_ring_order).
      now apply (O4 ℚ_order), IZQ_lt. }
    destruct (cut_archimedean α w) as [n [H3 H4]]; auto.
    apply Specify_classification.
    split; auto.
    exists (n*w)%Q, (-(n+2)*w)%Q.
    repeat split; auto.
    + unfold IQS.
      f_equal.
      unfold w.
      ring_simplify.
      rewrite <-M2, inv_l; try ring.
      intros H5.
      apply IZQ_eq in H5.
      rewrite H5 in H1.
      contradiction (ordered_rings.lt_irrefl ℤ_order 0%Z).
    + apply Specify_classification.
      split; unfold IQS; auto using elts_in_set.
      exists (-(n+2)*w), w.
      repeat split; auto.
      replace ((-(-(n+2)*w)-w))%Q with (n*w+2*w+-w)%Q by ring.
      replace (IZQ 2) with (1/1+1/1)%Q.
      * rewrite D1, M3, <-? rationals.A2, A4, (rationals.A1 w), rationals.A3.
        now replace (n*w+w)%Q with ((n+1)*w)%Q by ring.
      * unfold IZQ; rewrite add_wf, Qequiv; rewrite ? integers.M3;
          auto using integers.zero_ne_1; ring.
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
    f_equal.
    apply set_proj_injective in H0.
    assert (-a+(a+b) = -a+(a+c)) by congruence.
    now rewrite ? A2, ? (A1 (-a)), ? A4, ? (A1 0), ? A3 in H1.
Qed.

Theorem lt_irrefl : ∀ a, ¬ a < a.
Proof.
  now intros a [H H0].
Qed.

Theorem lt_antisym : ∀ a b, a < b → ¬ b < a.
Proof.
  intros a b H H0.
  eapply lt_irrefl; eauto using lt_trans.
Qed.

Definition mul_pos_set (a b : R) :=
  {x in 𝐐 | (∃ r s ξ : Q, x = ξ ∧ r ∈ a ∧ s ∈ b ∧ 0 < r ∧ 0 < s ∧ ξ ≤ r * s)%Q}.

Definition one : R := IQR 1.
Notation "1" := one : R_scope.
Notation "- 1" := (neg one) : R_scope.

Theorem pos_nonempty : ∀ a, 0 < a → ∃ c : Q, (0 < c)%Q ∧ c ∈ a.
Proof.
  intros a H.
  apply proper_subset_inhab in H as [c [H H0]].
  assert (c ∈ 𝐐) as H1.
  { pose proof (elts_in_set a) as H1; simpl in *.
    apply Specify_classification in H1 as [H1 [H2 [H3 [H4 H5]]]].
    apply Powerset_classification in H1.
    now apply H1. }
  set (γ := exist H1 : Q).
  assert (¬ γ < 0)%Q as H2.
  { contradict H0.
    unfold zero, IQR, iqr_set.
    apply Specify_classification.
    split; auto.
    now rewrite (reify H1), despecify. }
  destruct (rationals.T γ 0) as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]];
    try tauto; try now (exists γ).
  pose proof elts_in_set a as H6; simpl in *.
  apply Specify_classification in H6 as [H6 [H7 [H8 [H9 H10]]]].
  destruct (H10 γ H) as [x [H11 H12]].
  exists x.
  split; auto; congruence.
Qed.

Theorem mul_pos_in : ∀ a b, 0 < a → 0 < b → mul_pos_set a b ∈ 𝐑.
Proof.
  intros a b H H0.
  apply Specify_classification.
  repeat split.
  - apply Powerset_classification.
    intros x H1.
    apply Specify_classification in H1
      as [H1 [r [s [ξ [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]].
    now subst.
  - apply Nonempty_classification.
    apply pos_nonempty in H as [c [H H1]].
    apply pos_nonempty in H0 as [d [H0 H2]].
    exists (c*d - 1).
    apply Specify_classification.
    simpl.
    split; unfold IQS; auto using elts_in_set.
    exists c, d, (c*d - 1).
    repeat split; auto.
    left.
    apply lt_sub_pos, (ordered_rings.zero_lt_1 ℚ_ring_order).
  - destruct (Dedekind_cut_6 a) as [c H1], (Dedekind_cut_6 b) as [d H2].
    intros H3.
    apply Subset_equality_iff in H3 as [H3 H4].
    assert (c*d ∈ mul_pos_set a b) as H5 by eauto using elts_in_set.
    apply Specify_classification in H5
      as [H5 [r [s [ξ [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]].
    apply set_proj_injective in H6.
    subst.
    rewrite (le_not_gt ℚ_ring_order) in H11; simpl in *.
    contradict H11.
    eapply (lt_cross_mul ℚ_ring_order); simpl; eauto using Dedekind_cut_4.
  - intros p q H1 H2.
    apply Specify_classification in H1
      as [H1 [r [s [ξ [H3 [H4 [H5 [H6 [H7 H8]]]]]]]]].
    apply Specify_classification.
    split; unfold IQS; auto using elts_in_set.
    exists r, s, q.
    apply set_proj_injective in H3.
    subst.
    repeat split; auto.
    destruct H8 as [H8 | H8]; left; simpl in *; eauto using rationals.lt_trans.
    congruence.
  - intros p H1.
    apply Specify_classification in H1
      as [H1 [r [s [ξ [H3 [H4 [H5 [H6 [H7 H8]]]]]]]]].
    apply Dedekind_cut_3 in H4 as [ρ [H4 H9]].
    apply Dedekind_cut_3 in H5 as [σ [H5 H10]].
    exists (ρ * σ)%Q.
    apply set_proj_injective in H3.
    assert (r*s < ρ*σ)%Q as H2 by (apply (lt_cross_mul ℚ_ring_order); eauto).
    split.
    + rewrite H3.
      destruct H8 as [H8 | H8]; eauto using rationals.lt_trans.
      congruence.
    + apply Specify_classification.
      split; unfold IQS; auto using elts_in_set.
      exists ρ, σ, (ρ * σ).
      repeat split; eauto using rationals.lt_trans.
      now right.
Qed.

Definition mul_pos : R → R → R.
Proof.
  intros a b.
  destruct (excluded_middle_informative (0 < a)),
  (excluded_middle_informative (0 < b)).
  - exact (exist (mul_pos_in a b l l0)).
  - exact 0.
  - exact 0.
  - exact 0.
Defined.

Infix "·" := mul_pos (at level 40) : R_scope.

Theorem M1_pos : ∀ a b, 0 < a → 0 < b → a · b = b · a.
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

Theorem O2_pos : ∀ a b, 0 < a → 0 < b → 0 < a · b.
Proof.
  intros a b H H0.
  unfold mul_pos.
  repeat destruct excluded_middle_informative; try tauto.
  split.
  - intros z H1.
    unfold zero, IQR in H1.
    apply Specify_classification in H1 as [H1 H2].
    rewrite (reify H1), despecify in *.
    apply Specify_classification.
    split; auto.
    apply pos_nonempty in H as [c [H H3]].
    apply pos_nonempty in H0 as [d [H0 H4]].
    set (ξ := exist H1 : Q).
    exists c, d, ξ.
    repeat split; auto.
    left; simpl.
    eauto using O2, rationals.lt_trans.
  - intros H1.
    apply pos_nonempty in H as [c [H H2]].
    apply pos_nonempty in H0 as [d [H0 H3]].
    apply lt_dense in H as [e [H H4]].
    apply lt_dense in H0 as [f [H0 H5]].
    assert ((e * f)%Q ∈ 0).
    { rewrite H1.
      apply Specify_classification.
      split; unfold IQS; auto using elts_in_set.
      exists c, d, (e*f)%Q.
      repeat split; eauto using rationals.lt_trans.
      left; simpl in *.
      apply (lt_cross_mul ℚ_ring_order); auto. }
    unfold IRS, zero, IQR in H6.
    apply Specify_classification in H6 as [H6 H7].
    rewrite despecify in *.
    rewrite (lt_not_ge ℚ_ring_order) in H7; fold rationals.le in *.
    contradict H7.
    left; simpl; eauto using O2.
Qed.

Theorem M2_pos : ∀ a b c, 0 < a → 0 < b → 0 < c → a · (b · c) = (a · b) · c.
Proof.
  intros a b c H H0 H1.
  assert (0 < a · b) as H2 by auto using O2_pos.
  assert (0 < b · c) as H3 by auto using O2_pos.
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
      split; unfold IQS; auto using elts_in_set.
      exists ρ, s, (ρ*s)%Q.
      repeat split; auto.
      now right.
    + destruct H16 as [H16 | H16], H10 as [H10 | H10].
      * apply (O3 ℚ_ring_order ρ) in H16; auto.
        rewrite M2 in H16.
        left; simpl in *.
        eauto using rationals.lt_trans.
      * subst.
        left.
        apply (O3 ℚ_ring_order ρ) in H16; auto.
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
      split; unfold IQS; auto using elts_in_set.
      exists s, τ, (s*τ)%Q.
      repeat split; auto.
      now right.
    + destruct H16 as [H16 | H16], H10 as [H10 | H10].
      * apply (O3 ℚ_ring_order τ) in H16; auto.
        rewrite ? (M1 τ), <-M2 in H16.
        left; simpl in *.
        eauto using rationals.lt_trans.
      * subst.
        left.
        apply (O3 ℚ_ring_order τ) in H16; auto.
        now rewrite ? (M1 τ), <-M2 in H16.
      * left.
        subst.
        now rewrite <-M2 in H10.
      * right.
        subst.
        now rewrite M2.
Qed.

Theorem zero_ne_1 : 1 ≠ 0.
Proof.
  intros H.
  unfold zero, one, IQR, iqr_set in H.
  inversion H as [H0].
  apply Subset_equality_iff in H0 as [H0 H1].
  pose proof (ordered_rings.zero_lt_1 ℚ_ring_order) as H2.
  apply lt_dense in H2 as [c [H2 H3]].
  contradiction (ordered_rings.lt_antisym ℚ_ring_order c 0%Q).
  pose proof (H0 c) as H4.
  apply Specify_classification in H4.
  - now rewrite despecify in H4.
  - apply Specify_classification.
    rewrite despecify.
    eauto using elts_in_set.
Qed.

Theorem zero_lt_1 : 0 < 1.
Proof.
  unfold lt.
  split.
  - intros z H.
    unfold zero, one, IQR, iqr_set in *.
    apply Specify_classification in H as [H H0].
    apply Specify_classification.
    rewrite (reify H), despecify in *.
    split; eauto using rationals.lt_trans,
           (ordered_rings.zero_lt_1 ℚ_ring_order : 0 < 1)%Q.
  - intros H.
    apply set_proj_injective in H.
    now contradiction zero_ne_1.
Qed.

Theorem M3_pos : ∀ a, 0 < a → 1 · a = a.
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
      apply Specify_classification in H2 as [H2 H7].
      rewrite despecify in *.
      apply (O3 ℚ_ring_order s) in H7; auto.
      rewrite ? (M1 s), M3 in H7.
      destruct H6 as [H6 | H6]; eauto using rationals.lt_trans.
      now subst.
    + apply Specify_classification.
      split; eauto using Dedekind_cut_0.
      apply Dedekind_cut_0 in H0 as H1.
      set (ζ := exist H1 : Q).
      replace z with (ζ : set) in * by auto.
      destruct (classic (0 < ζ)%Q) as [H2 | H2].
      * apply Dedekind_cut_3 in H0 as [t [H0 H3]].
        exists (ζ * t^-1)%Q, t, ζ.
        assert (t ≠ 0)%Q as H4.
        { eapply (lt_neq ℚ_ring_order), rationals.lt_trans; eauto. }
        repeat split; eauto using rationals.lt_trans.
        -- unfold one, IQR, iqr_set.
           apply Specify_classification.
           rewrite despecify.
           split; unfold IQS; auto using elts_in_set.
           rewrite <-(inv_l t), (M1 ζ); auto.
           apply (O3 ℚ_ring_order); try apply (inv_lt ℚ_order); simpl; auto.
           eauto using rationals.lt_trans.
        -- apply O2, (inv_lt ℚ_order); auto; simpl.
           eauto using rationals.lt_trans.
        -- rewrite <-M2, inv_l, M1, M3; auto.
           now right.
      * apply pos_nonempty in l as [c [H3 H4]].
        apply pos_nonempty in l0 as [d [H5 H6]].
        exists c, d, ζ.
        repeat split; auto.
        left; simpl.
        rewrite <-(le_not_gt ℚ_ring_order) in H2; fold rationals.le in *.
        destruct H2 as [H2 | H2]; eauto using rationals.lt_trans, O2.
        rewrite H2.
        now apply O2.
  - contradiction n.
    now apply zero_lt_1.
Qed.

Definition inv_pos_set (α : R) :=
  {p in 𝐐 | ∃ ρ r : Q,
     p = ρ ∧ (1 < r)%Q ∧ ((ρ ≤ 0)%Q ∨ ((0 < ρ)%Q ∧ (ρ*r)^-1 ∉ α))}.

Theorem inv_pos_in : ∀ a, 0 < a → inv_pos_set a ∈ 𝐑.
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
    split; unfold IQS; auto using elts_in_set.
    exists 0%Q, 2.
    repeat split; eauto using zero_lt_1, one_lt_2, rationals.lt_trans.
    now left; right.
  - pose proof H as H0.
    apply pos_nonempty in H0 as [c [H0 H1]].
    intros H2.
    assert (c^-1 ∈ 𝐐) by (unfold IQS; auto using elts_in_set).
    rewrite <-H2 in H3.
    apply Specify_classification in H3
      as [H3 [p [r [H4 [H5 [[H6 | H6] | [H6 H7]]]]]]];
      apply set_proj_injective in H4; subst.
    + apply (inv_lt ℚ_order) in H0.
      pose proof (rationals.T (c^-1) 0).
      tauto.
    + unfold inv in H6.
      repeat destruct constructive_indefinite_description.
      destruct a0.
      unfold rationals.zero, IZQ in H6.
      apply Qequiv in H6; eauto using integers.zero_ne_1.
      * replace (x*0)%Z with 0%Z in * by ring.
        rewrite (M3_r ℤ) in H6.
        contradiction.
      * intros H7.
        subst.
        rewrite inv_div, (mul_0_l ℚ_ring) in H0; auto; simpl in *.
        contradiction (ordered_rings.lt_irrefl ℚ_ring_order 0%Q).
    + contradict H7.
      eapply Dedekind_cut_2; eauto.
      rename H6 into H4.
      assert (0 < r)%Q as H6.
      { eapply (rationals.lt_trans _ 1); auto.
        apply IZQ_lt, integers.zero_lt_1. }
      rewrite <-(rationals.M3 c) at 2.
      rewrite <-(inv_l (c^-1*r)), <-rationals.M2,
      <-(M3_r ℚ_ring ((c^-1*r)^-1)) at 1;
        try now apply (lt_neq ℚ_ring_order), O2.
      apply (O3 ℚ_ring_order); try now apply (inv_lt ℚ_order), O2.
      rewrite M1, M2, (M1 c), inv_l, M3; auto using (lt_neq ℚ_ring_order).
  - intros p q H0 H1.
    apply Specify_classification in H0 as [H0 [ρ [r [H2 [H3 [H4 | [H4 H5]]]]]]];
      apply set_proj_injective in H2; subst; apply Specify_classification;
        split; unfold IQS; auto using elts_in_set; exists q, r;
          repeat split; auto.
    + left.
      destruct H4 as [H4 | H4]; left; simpl in *;
        eauto using rationals.lt_trans.
      congruence.
    + destruct (classic (q ≤ 0)%Q) as [H2 | H2]; try tauto; right.
      rewrite <-(lt_not_ge ℚ_ring_order) in H2; simpl in *.
      assert (0 < r)%Q as H6.
      { eapply (rationals.lt_trans _ 1); eauto.
        apply IZQ_lt, integers.zero_lt_1. }
      split; auto.
      eapply Dedekind_cut_5; eauto.
      rewrite <-(lt_cross_inv ℚ_order), ? (M1 _ r); simpl;
        try apply (ordered_rings.O3 ℚ_ring_order);
        eauto using O3, O2, rationals.lt_trans.
  - intros p H0.
    apply Specify_classification in H0
      as [H0 [ρ [r [H1 [H2 [[H3 | H3] | [H3 H4]]]]]]];
      apply set_proj_injective in H1; subst.
    + exists 0%Q.
      split; auto.
      apply Specify_classification.
      split; unfold IQS; auto using elts_in_set.
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
      assert (c ≠ 0%Q) as H5 by eauto using (lt_neq ℚ_ring_order).
      assert (r ≠ 0%Q) as H6 by eauto using (lt_neq ℚ_ring_order).
      split.
      * repeat apply O2; now apply (inv_lt ℚ_order).
      * apply Specify_classification.
        split; unfold IQS; auto using elts_in_set.
        exists (c^-1 * r^-1 * r^-1)%Q, r.
        repeat split; auto.
        right.
        split.
        -- repeat apply O2; now apply (inv_lt ℚ_order).
        -- eapply Dedekind_cut_5; eauto.
           rewrite <-M2, inv_l, (M1 _ 1), M3, inv_mul, inv_inv,
           <-(M3 c), ? (M1 _ c) at 1; try apply (O3 ℚ_ring_order); auto.
    + apply lt_dense in H2 as [c [H2 H5]].
      exists (ρ * r * c^-1)%Q.
      assert (0 < c)%Q as H6.
      { apply (rationals.lt_trans _ 1); auto.
        apply IZQ_lt, integers.zero_lt_1. }
      split.
      * apply (lt_div ℚ_order) in H5; auto; simpl in *.
        apply (O3 ℚ_ring_order ρ) in H5; auto.
        now rewrite M1, M3, M2 in H5.
      * apply Specify_classification.
        split; unfold IQS; auto using elts_in_set.
        exists (ρ * r * c^-1)%Q, c.
        repeat split; auto.
        right.
        rewrite <-? M2, inv_l, (M1 _ 1), M3; auto using (lt_neq ℚ_ring_order).
        split; auto.
        assert (0 < r)%Q by eauto using rationals.lt_trans,
                            (ordered_rings.zero_lt_1 ℚ_ring_order : 0 < 1)%Q.
        repeat apply O2; auto; now apply (inv_lt ℚ_order).
Qed.

Definition inv_pos : R → R.
Proof.
  intros a.
  destruct (excluded_middle_informative (0 < a)).
  - exact (exist (inv_pos_in _ l)).
  - exact 0.
Defined.

Notation "a '^-1' " := (inv_pos a) (at level 30, format "a '^-1'") : R_scope.

Lemma pos_not_in_0 : ∀ x : Q, (0 < x)%Q → x ∉ 0.
Proof.
  intros x H H0.
  unfold zero, IQR, iqr_set in H0.
  apply Specify_classification in H0 as [H0 H1].
  rewrite despecify in H1.
  contradiction (ordered_rings.lt_antisym ℚ_ring_order 0%Q x).
Qed.

Theorem inv_lt : ∀ a, 0 < a → 0 < a^-1.
Proof.
  intros a H.
  unfold lt.
  split.
  - intros z H0.
    unfold zero, IQR in H0.
    apply Specify_classification in H0 as [H0 H1].
    unfold inv_pos.
    repeat destruct excluded_middle_informative; try tauto.
    apply Specify_classification.
    split; auto.
    rewrite (reify H0), despecify in *.
    set (ξ := exist H0 : Q) in *.
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
    apply (inv_lt ℚ_order) in H4 as H5.
    assert (0 < 2)%Q as H6.
    { rewrite <-IZQ_add.
      apply (ordered_rings.zero_lt_2 ℚ_ring_order). }
    apply (inv_lt ℚ_order) in H6 as H7.
    assert ((x^-1 * 2^-1)%Q ∉ 0) as H8 by auto using pos_not_in_0, O2.
    contradiction H8.
    rewrite H2.
    unfold inv_pos, inv_pos_set.
    destruct excluded_middle_informative; try tauto.
    apply Specify_classification.
    split; unfold IQS; auto using elts_in_set.
    exists (x^-1 * 2^-1)%Q, 2%Q.
    repeat split; auto using one_lt_2.
    right.
    split; auto using O2.
    rewrite <-M2, inv_l, M1, M3, inv_inv; auto using (lt_neq ℚ_ring_order).
Qed.

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
  assert (0 < r)%Q as H7 by eauto using rationals.lt_trans,
                            (ordered_rings.zero_lt_1 ℚ_ring_order : 0 < 1)%Q.
  - intros x H8.
    destruct (integers.T 0 x) as [[H9 _] | [[_ [H9 _]] | [_ [_ H9]]]]; auto.
    + subst.
      contradict H8.
      rewrite integers.A1, integers.A3.
      eauto using Dedekind_cut_2.
    + rewrite (pow_add_r ℚ) in H8; auto using (lt_neq ℚ_ring_order);
        simpl in *; fold pow in *.
      contradict H8.
      eapply Dedekind_cut_2; eauto.
      rewrite <-(M3 c), (M1 1).
      apply (lt_cross_mul ℚ_ring_order); auto; try now apply (pow_pos ℚ_order).
      now apply (pow_lt_1 ℚ_order).
  - exists (n+-m)%Z.
    split.
    + rewrite <-(ordered_rings.lt_shift ℤ_order); simpl.
      eauto using integers.lt_trans.
    + replace (m+(n+-m))%Z with n%Z by ring.
      eauto using Dedekind_cut_5.
  - exists (m+(x+-1))%Z.
    split.
    + apply NNPP.
      intros H9.
      pose proof (lt_succ ℤ_order (x+-1)%Z) as H10; simpl in *.
      replace (x+-1+1)%Z with x in H10 by ring.
      apply H8 in H9 as [H9 | H9]; simpl in *.
      * contradiction (ordered_rings.lt_antisym ℤ_order x (x+-1)%Z).
      * contradiction (ordered_rings.lt_irrefl ℤ_order x).
        now rewrite H9 at 1.
    + now replace (m + (x + - 1) + 1)%Z with (m+x)%Z by ring.
Qed.

Theorem M4_pos : ∀ a, 0 < a → a^-1 · a = 1.
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
    apply Specify_classification in H2
      as [H2 [p [q [H7 [H8 [H9 | [H9 H10]]]]]]];
      apply set_proj_injective in H7; subst.
    + destruct H9 as [H9 | H9].
      * contradiction (ordered_rings.lt_antisym ℚ_ring_order 0%Q p).
      * subst.
        contradiction (ordered_rings.lt_irrefl ℚ_ring_order 0%Q).
    + assert (0 < q)%Q as H1 by
            eauto using rationals.lt_trans,
            (ordered_rings.zero_lt_1 ℚ_ring_order : 0 < 1)%Q.
      apply (inv_lt_1 ℚ_order) in H8; simpl in *; auto.
      eapply Dedekind_cut_4 in H10; eauto.
      rewrite <-inv_mul in H10.
      apply (O3 ℚ_ring_order (p^-1)%Q) in H8;
        try now apply (ordered_fields.inv_lt ℚ_order).
      rewrite (rationals.M1 _ 1), rationals.M3 in H8.
      assert (s < p^-1)%Q as H11 by eauto using rationals.lt_trans.
      apply (O3 ℚ_ring_order p) in H11; auto.
      rewrite (M1 _ (p^-1)), inv_l in H11; auto using (lt_neq ℚ_ring_order).
      apply Specify_classification.
      rewrite despecify.
      split; auto.
      destruct H6 as [H6 | H6]; eauto using rationals.lt_trans.
      simpl in *.
      congruence.
  - unfold IQR, one in H0.
    simpl in H0.
    unfold iqr_set in H0.
    apply Specify_classification in H0 as [H0 H1].
    rewrite (reify H0), despecify in H1.
    set (ξ := exist H0 : Q) in *.
    set (w := (ξ^-1)%Q).
    apply NNPP; intros H2.
    assert (0 < ξ)%Q as H3.
    { destruct (rationals.T 0 ξ) as [[H4 _] | [[_ [H4 _]] | [_ [_ H4]]]];
        try tauto; contradict H2.
      + unfold mul_pos, mul_pos_set.
        repeat destruct excluded_middle_informative; try contradiction.
        * simpl.
          apply Specify_classification.
          split; auto.
          apply pos_nonempty in l as [c [H2 H5]].
          apply pos_nonempty in l0 as [d [H6 H7]].
          exists c, d, ξ.
          repeat split; auto; left; simpl in *; rewrite <-H4; eauto using O2.
        * now apply inv_lt in l.
      + unfold mul_pos, mul_pos_set.
        repeat destruct excluded_middle_informative; try contradiction.
        * simpl.
          apply Specify_classification.
          split; auto.
          apply pos_nonempty in l as [c [H2 H5]].
          apply pos_nonempty in l0 as [d [H6 H7]].
          exists c, d, ξ.
          repeat split; auto; left; simpl; eauto using rationals.lt_trans, O2.
        * now apply inv_lt in l. }
    assert (1 < w)%Q as H4.
    { rewrite (inv_lt_1 ℚ_order); unfold w;
        try now apply (ordered_fields.inv_lt ℚ_order).
      now rewrite inv_inv. }
    contradict H2.
    pose proof H4 as H2.
    apply square_in_interval in H4 as [r [H4 [H5 H6]]].
    assert (1 < r)%Q as H7 by now apply (square_ge_1 ℚ_ring_order).
    pose proof H7 as H8.
    eapply pow_archimedean in H8 as [n [H9 H10]]; eauto.
    unfold mul_pos.
    repeat destruct excluded_middle_informative; try tauto;
      try now (exfalso; auto using inv_lt).
    apply Specify_classification.
    split; auto.
    exists (r^(-(n+2))), (r^n), ξ.
    repeat split; auto; try now apply (pow_pos ℚ_order).
    + unfold inv_pos.
      destruct excluded_middle_informative; try tauto.
      apply Specify_classification.
      split; unfold IQS; auto using elts_in_set.
      exists (r^(-(n+2))), r.
      repeat split; auto.
      right.
      split.
      * now apply (pow_pos ℚ_order).
      * rewrite <-inv_mul, <-? inv_pow, <-pow_mul_r, <-(pow_add_r ℚ);
          auto using (lt_neq ℚ_ring_order).
        replace (-(n+2)*-1+-1)%Z with (n+1)%Z by ring; auto.
    + unfold w in *.
      rewrite <-(pow_add_r ℚ); auto using (lt_neq ℚ_ring_order).
      left; simpl; fold pow.
      replace (-(n+2)+n)%Z with (-2%Z)%Z by ring.
      apply (O3 ℚ_ring_order (ξ * r^(-2%Z))) in H6;
        try (apply O2; try apply (pow_pos ℚ_order); auto).
      rewrite <-M2, (M1 _ (ξ^-1)), ? M2, inv_l, M3 in H6;
        auto using (lt_neq ℚ_ring_order).
      rewrite <-(pow_1_r ℚ r) in H6 at 2 3; fold pow in *.
      rewrite <-(M2 ξ), <-(pow_add_r ℚ), <-M2,
      <-(pow_add_r ℚ) in H6; auto using (lt_neq ℚ_ring_order).
      replace (-(2)+1+1)%Z with 0%Z in H6 by ring.
      now rewrite pow_0_r, M1, M3 in H6.
Qed.

Theorem D1_pos : ∀ a b c, 0 < a → 0 < b → 0 < c → (a + b) · c = a · c + b · c.
Proof.
  intros a b c H H0 H1.
  assert (0 < a + b) as H2.
  { apply (O1 a) in H0.
    rewrite A3 in H0.
    eauto using lt_trans. }
  unfold mul_pos, add_set, mul_pos_set.
  repeat destruct excluded_middle_informative; try tauto;
    try (contradict n; unfold mul_pos in *;
         repeat destruct excluded_middle_informative; tauto).
  apply set_proj_injective.
  simpl.
  apply Extensionality.
  split; intros H3; apply Specify_classification;
    apply Specify_classification in H3; repeat split; try tauto.
  - destruct H3 as [H3 [r [s [ξ [H4 [H5 [H6 [H7 [H8 H9]]]]]]]]].
    apply Specify_classification in H5 as [H5 [r' [s' [H10 [H11 H12]]]]].
    apply set_proj_injective in H10.
    subst.
    destruct (classic (0 < r')%Q) as [H4 | H4], (classic (0 < s')%Q)
        as [H10 | H10].
    + exists (ξ+-s'*s)%Q, (s'*s)%Q.
      repeat split; try (apply f_equal; ring); apply Specify_classification;
        split; unfold IQS; auto using elts_in_set.
      * exists r', s, (ξ+-s'*s)%Q.
        repeat split; auto.
        destruct H9 as [H9 | H9]; simpl in *.
        -- left; simpl.
           apply (rationals.O1 (-s'*s)) in H9.
           replace (-s'*s+(r'+s')*s)%Q with (r'*s)%Q in H9 by ring.
           now rewrite rationals.A1 in H9.
        -- right; subst.
           now ring_simplify.
      * exists s', s, (s'*s)%Q.
        repeat split; try right; auto.
    + destruct (pos_nonempty b) as [t [H13 H14]]; auto.
      destruct (lt_dense2 t (r'+s')) as [k [H15 [H16 H17]]]; auto.
      exists (ξ+-k*s)%Q, (k*s)%Q.
      repeat split; simpl; try (apply f_equal; ring);
        apply Specify_classification; split; eauto using elts_in_set.
      * exists (r'+s'+-k)%Q, s, (ξ+-k*s)%Q.
        repeat split; auto.
        -- eapply Dedekind_cut_2; eauto.
           rewrite (ordered_rings.lt_shift ℚ_ring_order); simpl.
           replace (r'+-(r'+s'+-k))%Q with (k+-s')%Q by ring.
           rewrite <-(ordered_rings.lt_shift ℚ_ring_order); simpl.
           rewrite <-(le_not_gt ℚ_ring_order) in H10; fold rationals.le in *.
           destruct H10 as [H10 | H10]; simpl in *.
           ++ eauto using rationals.lt_trans.
           ++ now subst.
        -- now rewrite <-(ordered_rings.lt_shift ℚ_ring_order).
        -- replace ((r'+s'+-k)*s)%Q with ((r'+s')*s+-k*s)%Q by ring.
           now apply add_le_r.
      * exists k, s, (k*s)%Q.
        repeat split; eauto using Dedekind_cut_2.
        now right.
    + destruct (pos_nonempty a) as [t [H13 H14]]; auto.
      destruct (lt_dense2 t (r'+s')) as [k [H15 [H16 H17]]]; auto.
      exists (k*s)%Q, (ξ+-k*s)%Q.
      repeat split; simpl; try (apply f_equal; ring);
        apply Specify_classification; split; eauto using elts_in_set.
      * exists k, s, (k*s)%Q.
        repeat split; eauto using Dedekind_cut_2.
        now right.
      * exists (r'+s'+-k)%Q, s, (ξ+-k*s)%Q.
        repeat split; auto.
        -- eapply Dedekind_cut_2; eauto.
           rewrite (ordered_rings.lt_shift ℚ_ring_order); simpl.
           replace (s'+-(r'+s'+-k))%Q with (k+-r')%Q by ring.
           rewrite <-(ordered_rings.lt_shift ℚ_ring_order); simpl.
           rewrite <-(le_not_gt ℚ_ring_order) in H4; fold rationals.le in *.
           destruct H4 as [H4 | H4]; simpl in *.
           ++ eauto using rationals.lt_trans.
           ++ now subst.
        -- now rewrite <-(ordered_rings.lt_shift ℚ_ring_order).
        -- replace ((r' + s' + - k) * s)%Q with ((r'+s')*s + -k*s)%Q by ring.
           now apply add_le_r.
    + apply (O0_opp ℚ_ring_order) in H7.
      tauto.
  - destruct H3 as [H3 [ac [bc [H4 [H5 H6]]]]].
    set (ζ := exist H3 : Q).
    replace z with (IQS ζ) in * by auto.
    apply set_proj_injective in H4.
    apply Specify_classification in H5
      as [H5 [a' [c' [a'c' [H7 [H8 [H9 [H10 [H11 H12]]]]]]]]].
    apply set_proj_injective in H7.
    apply Specify_classification in H6
      as [H6 [b' [c'' [b'c'' [H13 [H14 [H15 [H16 [H17 H18]]]]]]]]].
    apply set_proj_injective in H13.
    subst.
    exists (a'+b')%Q, (ordered_rings.max ℚ_ring_order c' c''), ζ.
    repeat split; auto using O0.
    + apply Specify_classification.
      split; eauto using elts_in_set.
    + destruct (max_eq ℚ_ring_order c' c'') as [H19 | H19]; now rewrite H19.
    + destruct (max_eq ℚ_ring_order c' c'') as [H19 | H19]; now rewrite H19.
    + rewrite H4, rationals.D1.
      destruct (max_eq ℚ_ring_order c' c'') as [H19 | H19]; rewrite H19.
      * apply le_cross_add; fold rationals.le; auto.
        eapply (ordered_rings.le_trans ℚ_ring_order); eauto.
        apply mul_le_l; simpl; auto; fold rationals.le.
        rewrite <-H19.
        now apply max_le_r.
      * apply le_cross_add; fold rationals.le; auto.
        eapply (ordered_rings.le_trans ℚ_ring_order); eauto.
        apply mul_le_l; simpl; auto; fold rationals.le.
        rewrite <-H19.
        now apply max_le_l.
Qed.

Definition mul : R → R → R.
Proof.
  intros a b.
  destruct (excluded_middle_informative (0 < a)),
  (excluded_middle_informative (0 < b)).
  - exact (a·b).
  - destruct (excluded_middle_informative (0 = b)).
    + exact 0.
    + exact (-(a·(-b))).
  - destruct (excluded_middle_informative (0 = a)).
    + exact 0.
    + exact (-((-a)·b)).
  - destruct (excluded_middle_informative (0 = b)).
    + exact 0.
    + destruct (excluded_middle_informative (0 = a)).
      * exact 0.
      * exact ((-a)·(-b)).
Defined.

Infix "*" := mul : R_scope.

Theorem mul_0_r : ∀ a, a * 0 = 0.
Proof.
  intros a.
  unfold mul.
  repeat destruct excluded_middle_informative; try tauto;
    contradiction (lt_irrefl 0).
Qed.

Theorem mul_0_l : ∀ a, 0 * a = 0.
Proof.
  intros a.
  unfold mul.
  repeat destruct excluded_middle_informative; try tauto;
    contradiction (lt_irrefl 0).
Qed.

Theorem R_mul_pos_pos : ∀ a b, 0 < a → 0 < b → a * b = a · b.
Proof.
  intros a b H H0.
  unfold mul.
  repeat destruct excluded_middle_informative; tauto.
Qed.

Theorem R_mul_pos_neg : ∀ a b, 0 < a → b < 0 → a * b = -(a · -b).
Proof.
  intros a b H H0.
  unfold mul.
  repeat destruct excluded_middle_informative; try tauto.
  - contradiction (lt_antisym 0 b).
  - now subst.
Qed.

Theorem R_mul_neg_pos : ∀ a b, a < 0 → 0 < b → a * b = -(-a · b).
Proof.
  intros a b H H0.
  unfold mul.
  repeat destruct excluded_middle_informative; try tauto.
  - contradiction (lt_antisym 0 a).
  - now subst.
Qed.

Theorem R_mul_neg_neg : ∀ a b, a < 0 → b < 0 → a * b = (-a · -b).
Proof.
  intros a b H H0.
  unfold mul.
  repeat destruct excluded_middle_informative; try tauto;
    subst; exfalso; eapply lt_antisym; eauto.
  contradiction (lt_irrefl 0).
Qed.

Theorem lt_shift : ∀ a b, a < b ↔ 0 < b + -a.
Proof.
  split; intros H.
  - apply (O1 (-a)) in H.
    now rewrite A1, A4, A1 in H.
  - apply (O1 a) in H.
    now rewrite A3, A1, <-A2, (A1 _ a), A4, A3 in H.
Qed.

Theorem lt_neg_0 : ∀ a, a < 0 ↔ 0 < -a.
Proof.
  intros a.
  now rewrite lt_shift, A1, A3.
Qed.

Theorem neg_lt_0 : ∀ a, -a < 0 ↔ 0 < a.
Proof.
  intros a.
  rewrite lt_shift.
  rewrite <-(A4 a) at 2.
  now rewrite <-A2, A4, A3.
Qed.

Theorem neg_neg : ∀ a, - - a = a.
Proof.
  intros a.
  rewrite <-(A3 a) at 2.
  now rewrite <-(A4 (-a)), A2, A4, A1, A3.
Qed.

Theorem M1 : ∀ a b, a * b = b * a.
Proof.
  intros a b.
  destruct (T 0 a) as [[H [H0 H1]] | [[H [H0 H1]] | [H [H0 H1]]]], (T 0 b)
      as [[H2 [H3 H4]] | [[H2 [H3 H4]] | [H2 [H3 H4]]]]; unfold mul;
    repeat destruct excluded_middle_informative; try tauto; subst;
      rewrite lt_neg_0 in *; now rewrite M1_pos.
Qed.

Theorem M2 : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  intros a b c.
  destruct (T 0 a) as [[H [H0 H1]] | [[H [H0 H1]] | [H [H0 H1]]]], (T 0 b)
      as [[H2 [H3 H4]] | [[H2 [H3 H4]] | [H2 [H3 H4]]]], (T 0 c)
        as [[H5 [H6 H7]] | [[H5 [H6 H7]] | [H5 [H6 H7]]]]; subst;
    try now rewrite ? mul_0_l, ? mul_0_r, ? mul_0_l.
  - rewrite ? R_mul_pos_pos, M2_pos, ? R_mul_pos_pos; auto;
      rewrite ? R_mul_pos_pos; auto using O2_pos.
  - rewrite ? (R_mul_pos_neg _ c), (R_mul_pos_pos a b), (R_mul_pos_neg a),
    neg_neg, M2_pos; auto; try now rewrite lt_neg_0 in *.
    + rewrite lt_neg_0, neg_neg in *; auto using O2_pos.
    + rewrite (R_mul_pos_pos a b); auto using O2_pos.
  - rewrite ? (R_mul_pos_neg a), ? (R_mul_neg_pos _ c), ? neg_neg, M2_pos;
      auto; try now rewrite lt_neg_0 in *.
    + rewrite lt_neg_0, neg_neg in *; auto using O2_pos.
    + rewrite R_mul_neg_pos, lt_neg_0, neg_neg in *; auto using O2_pos.
  - rewrite ? (R_mul_neg_neg _ c), (R_mul_pos_neg a b), (R_mul_pos_pos a),
    ? neg_neg, M2_pos; auto; try now rewrite lt_neg_0 in *.
    + rewrite lt_neg_0 in *; auto using O2_pos.
    + rewrite R_mul_pos_neg, lt_neg_0, neg_neg in *; auto using O2_pos.
  - rewrite ? (R_mul_neg_pos a), (R_mul_pos_pos b), R_mul_neg_pos,
    neg_neg, M2_pos; auto; try now rewrite lt_neg_0 in *.
    + rewrite lt_neg_0, neg_neg in *; auto using O2_pos.
    + rewrite R_mul_pos_pos; auto using O2_pos.
  - rewrite (R_mul_pos_neg b c), (R_mul_neg_neg _ c), (R_mul_neg_pos a b),
    (R_mul_neg_neg a), ? neg_neg, M2_pos; auto; try now rewrite lt_neg_0 in *.
    + rewrite lt_neg_0, neg_neg in *; auto using O2_pos.
    + rewrite R_mul_neg_pos, lt_neg_0, neg_neg in *; auto using O2_pos.
  - rewrite ? (R_mul_neg_neg a), (R_mul_neg_pos b), R_mul_pos_pos,
    ? neg_neg, M2_pos; auto; try now rewrite lt_neg_0 in *.
    + rewrite lt_neg_0 in *; auto using O2_pos.
    + rewrite R_mul_neg_pos, lt_neg_0, neg_neg in *; auto using O2_pos.
  - rewrite R_mul_neg_pos, R_mul_neg_neg, R_mul_pos_neg, R_mul_neg_neg, M2_pos;
      auto; try (now rewrite lt_neg_0 in * );
        rewrite R_mul_neg_neg, lt_neg_0 in *; auto using O2_pos.
Qed.

Theorem M3 : ∀ a, 1 * a = a.
Proof.
  intros a.
  destruct (T 0 a) as [[H [H0 H1]] | [[H [H0 H1]] | [H [H0 H1]]]].
  - rewrite R_mul_pos_pos, M3_pos; auto using zero_lt_1.
  - subst.
    now rewrite mul_0_r.
  - rewrite R_mul_pos_neg, lt_neg_0, M3_pos, neg_neg in *; auto using zero_lt_1.
Qed.

Theorem O0 : ∀ a b, 0 < a → 0 < b → 0 < a + b.
Proof.
  intros a b H H0.
  apply (O1 a) in H0.
  rewrite A3 in H0.
  eauto using lt_trans.
Qed.

Theorem neg_add : ∀ a b, - (a + b) = - a + - b.
Proof.
  intros a b.
  now rewrite <-(A3 (-a+-b)), <-(A4 (a+b)), A2, (A1 a), A2, <-A2,
  <-(A2 (-a)), (A1 _ b), A4, A3, A2, (A1 (-a)), A4, (A1 0), A3.
Qed.

Lemma D1_opp : ∀ a b c, 0 < a → b < 0 → (a + b) * c = a * c + b * c.
Proof.
  intros a b c H H0.
  destruct (T 0 c) as [[H1 [H2 H3]] | [[H1 [H2 H3]] | [H1 [H2 H3]]]].
  - destruct (T 0 (a+b)) as [[H4 [H5 H6]] | [[H4 [H5 H6]] | [H4 [H5 H6]]]].
    + rewrite R_mul_pos_pos, R_mul_pos_pos, R_mul_neg_pos, lt_neg_0 in *; auto.
      replace a with (a+b+-b) at 2.
      rewrite (D1_pos (a+b)), <-A2, A4, A3; auto.
      now rewrite <-A2, A4, A3.
    + replace a with (a+b+-b) at 2.
      rewrite <-H5, mul_0_l, (A1 0), A3, R_mul_pos_pos, R_mul_neg_pos, A4 in *;
        auto.
      * now rewrite <-lt_neg_0.
      * now rewrite <-A2, A4, A3.
    + rewrite R_mul_neg_pos, R_mul_pos_pos, R_mul_neg_pos; auto.
      replace (-b) with (-(b+a)+a).
      rewrite (D1_pos (-(b+a))), (A1 (a·c)), ? neg_add,
      <-A2, (A1 _ (a·c)), A4, A3, A1; auto.
      * now rewrite <-lt_neg_0, A1.
      * now rewrite neg_add, <-A2, (A1 _ a), A4, A3.
  - subst.
    now rewrite ? mul_0_r, A3.
  - destruct (T 0 (a+b)) as [[H4 [H5 H6]] | [[H4 [H5 H6]] | [H4 [H5 H6]]]].
    + rewrite R_mul_pos_neg, R_mul_pos_neg, R_mul_neg_neg, lt_neg_0 in *; auto.
      replace a with (a+b+-b) at 2.
      rewrite (D1_pos (a+b)), neg_add, <-A2, (A1 _ (-b·-c)), A4, A3; auto.
      now rewrite <-A2, A4, A3.
    + replace a with (a+b+-b) at 2.
      rewrite <-H5, mul_0_l, (A1 0), A3, R_mul_pos_neg, R_mul_neg_neg,
      A1, A4 in *; auto.
      * now rewrite <-lt_neg_0.
      * now rewrite <-A2, A4, A3.
    + rewrite R_mul_neg_neg, R_mul_pos_neg, R_mul_neg_neg; auto.
      replace (-b) with (-(b+a)+a).
      rewrite (D1_pos (-(b+a))), (A1 (-(a·(-c)))), ? neg_add,
      <-A2, A4, A3, A1; auto.
      * now rewrite <-lt_neg_0, A1.
      * now rewrite <-lt_neg_0.
      * now rewrite neg_add, <-A2, (A1 _ a), A4, A3.
Qed.

Theorem D1 : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  intros a b c.
  destruct (T 0 a) as [[H [H0 H1]] | [[H [H0 H1]] | [H [H0 H1]]]], (T 0 b)
      as [[H2 [H3 H4]] | [[H2 [H3 H4]] | [H2 [H3 H4]]]], (T 0 c)
        as [[H5 [H6 H7]] | [[H5 [H6 H7]] | [H5 [H6 H7]]]]; subst;
    try now rewrite ? (A1 0), ? A3, ? mul_0_l, ? mul_0_r, ? (A1 0), ? A3.
  - rewrite ? R_mul_pos_pos, D1_pos; auto using O0.
  - rewrite ? R_mul_pos_neg, D1_pos, neg_add in *; auto using O0.
    now rewrite <-lt_neg_0.
  - auto using D1_opp.
  - auto using D1_opp.
  - rewrite A1, (A1 (a*c)).
    auto using D1_opp.
  - rewrite A1, (A1 (a*c)).
    auto using D1_opp.
  - rewrite ? R_mul_neg_pos, neg_add, D1_pos, neg_add; auto;
      try now rewrite <-lt_neg_0.
    rewrite lt_neg_0, neg_add in *.
    auto using O0.
  - rewrite ? R_mul_neg_neg, neg_add, D1_pos; auto; try now rewrite <-lt_neg_0.
    rewrite lt_neg_0, neg_add in *.
    auto using O0.
Qed.

Definition sub a b := a + -b.

Infix "-" := sub : R_scope.

Theorem A3_l : ∀ a, 0 + a = a.
Proof.
  intros a.
  now rewrite A1, A3.
Qed.

Theorem sub_neg : ∀ a b, a - b = a + -b.
Proof.
  auto.
Qed.

Definition inv : R → R.
Proof.
  intros a.
  destruct (excluded_middle_informative (0 < a)).
  - exact (a^-1).
  - destruct (excluded_middle_informative (0 = a)).
    + exact 0.
    + exact (-(-a)^-1).
Defined.

Notation "a '^-1' " := (inv a) (at level 30, format "a '^-1'") : R_scope.

Theorem inv_l : ∀ a, a ≠ 0 → a^-1 * a = 1.
Proof.
  intros a H.
  unfold inv.
  repeat destruct excluded_middle_informative.
  - rewrite R_mul_pos_pos, M4_pos; auto using inv_lt.
  - subst; contradiction.
  - assert (a < 0) as H0 by (pose proof (T 0 a); tauto).
    rewrite R_mul_neg_neg, neg_neg, M4_pos; auto.
    + now rewrite <-lt_neg_0.
    + rewrite lt_neg_0, neg_neg.
      apply inv_lt.
      now rewrite <-lt_neg_0.
Qed.

Definition div a b := a * b^-1.

Theorem div_inv : ∀ a b, div a b = a * b^-1.
Proof.
  auto.
Qed.

Theorem O2 : ∀ a b, 0 < a → 0 < b → 0 < a * b.
Proof.
  intros a b H H0.
  rewrite R_mul_pos_pos; auto using O2_pos.
Qed.

Definition ℝ_ring := mkRing _ 0 1 add mul neg A3_l A1 A2 M3 M1 M2 D1 A4.

Definition ℝ := mkField ℝ_ring inv inv_l zero_ne_1.

Add Field real_field_raw : (fieldify ℝ).

Add Field real_field :
  (fieldify ℝ : field_theory 0 1 add mul sub neg div inv eq).

Definition real_order := mkOR ℝ_ring lt lt_trans T O1 O2 zero_ne_1.

Definition real_field_order := mkOF ℝ lt lt_trans T O1 O2.

Theorem IQR_add : ∀ a b : Q, a + b = (a + b)%Q.
Proof.
  intros r s.
  apply set_proj_injective, Subset_equality_iff.
  split; intros p H.
  - unfold add, add_set, IQR, iqr_set in *.
    apply Specify_classification in H as [H [a [b [H0 [H1 H2]]]]]; subst.
    apply Specify_classification in H1 as [H1 H3].
    apply Specify_classification in H2 as [H2 H4].
    apply Specify_classification.
    rewrite despecify in *.
    split; auto.
    apply (lt_cross_add ℚ_ring_order); auto.
  - unfold IQR, iqr_set in *; simpl.
    apply Specify_classification in H as [H H0].
    apply Specify_classification.
    rewrite (reify H), despecify in *.
    set (ρ := exist H : Q) in *.
    split; auto.
    rewrite (ordered_rings.lt_shift ℚ_ring_order) in H0; simpl in H0.
    apply lt_dense in H0 as [c [H0 H1]].
    exists (r+-c)%Q, (c+ρ+-r)%Q.
    repeat split; unfold IQS; f_equal; try ring; apply Specify_classification;
      split; auto using elts_in_set; rewrite despecify.
    + rewrite (ordered_rings.lt_shift ℚ_ring_order); simpl.
      now replace (r+-(r+-c))%Q with c by ring.
    + rewrite (ordered_rings.lt_shift ℚ_ring_order) in *; simpl in *.
      now replace (s+-(c+ρ+-r))%Q with (r+s+-ρ+-c)%Q by ring.
Qed.

Theorem IQR_lt : ∀ a b : Q, a < b ↔ (a < b)%Q.
Proof.
  split.
  - intros [H H0].
    destruct (proper_subset_inhab (IQR a) (IQR b)) as [p [H1 H2]];
      try split; auto.
    unfold IQR, iqr_set in H1, H2.
    apply Specify_classification in H1 as [H1 H3].
    rewrite (reify H1), despecify in *.
    set (ρ := exist H1 : Q) in *.
    assert (a ≤ ρ)%Q as [H4 | H4].
    { rewrite (le_not_gt ℚ_ring_order); simpl.
      contradict H2.
      apply Specify_classification.
      rewrite despecify.
      split; auto. }
    + eauto using rationals.lt_trans.
    + congruence.
  - intros H.
    split.
    + intros z H0.
      unfold IQR in *.
      apply Specify_classification in H0 as [H0 H1].
      apply Specify_classification.
      rewrite (reify H0), despecify in *.
      subst.
      eauto using rationals.lt_trans.
    + intros H0.
      assert (a ∈ (IQR a)) as H1.
      { rewrite H0.
        unfold IQR.
        apply Specify_classification.
        rewrite despecify.
        split; eauto using elts_in_set. }
      unfold IQR in H1.
      apply Specify_classification in H1 as [H1 H2].
      rewrite despecify in *.
      contradiction (ordered_rings.lt_irrefl ℚ_ring_order a).
Qed.

Theorem IQR_eq : ∀ a b : Q, (a : R) = (b : R) ↔ a = b.
Proof.
  split; intros H.
  - destruct (rationals.T a b) as [[H0 _] | [[_ [H0 _]] | [_ [_ H0]]]];
      try tauto; rewrite <-IQR_lt in H0; pose proof (T a b); tauto.
  - destruct (T a b) as [[H0 _] | [[_ [H0 _]] | [_ [_ H0]]]]; try tauto;
      now subst.
Qed.

Theorem IQR_mul_pos : ∀ a b : Q, 0 < a → 0 < b → a · b = (a * b)%Q.
Proof.
  intros a b H H0.
  unfold zero in *.
  pose proof H as H1.
  pose proof H0 as H2.
  rewrite IQR_lt in H1, H2.
  apply set_proj_injective, Subset_equality_iff.
  split; intros p H3; unfold mul_pos, mul_pos_set, IQR, iqr_set in *;
    repeat destruct excluded_middle_informative; try tauto; simpl in *.
  - apply Specify_classification in H3
      as [H3 [r [s [ξ [H4 [H5 [H6 [H7 [H8 H9]]]]]]]]]; subst.
    apply Specify_classification in H5 as [H5 H4].
    apply Specify_classification in H6 as [H6 H11].
    apply Specify_classification.
    rewrite despecify in *.
    split; auto.
    assert (r * s < a * b)%Q as H10 by
          (eapply (lt_cross_mul ℚ_ring_order);
           eauto using (ordered_rings.le_lt_trans ℚ_ring_order)).
    destruct H9 as [H9 | H9].
    + eauto using rationals.lt_trans.
    + congruence.
  - apply Specify_classification in H3 as [H3 H4].
    apply Specify_classification.
    rewrite (reify H3), despecify in *.
    set (ξ := exist H3 : Q) in *.
    split; auto.
    destruct (rationals.T 0 ξ) as [[H5 _] | [[_ [H5 _]] | [_ [_ H5]]]].
    + assert (1 < a * (b * ξ^-1))%Q.
      { rewrite rationals.M2, <-(rationals.inv_l ξ), rationals.M1;
          auto using (lt_neq ℚ_ring_order).
        apply (ordered_rings.O3_r ℚ_ring_order); auto;
          now apply (ordered_fields.inv_lt ℚ_order). }
      apply square_in_interval in H6 as [z [H6 [H7 H8]]].
      exists (a*z^-1)%Q, (b*z^-1)%Q, ξ.
      apply (square_ge_1 ℚ_ring_order) in H7; simpl in *;
        repeat split; auto.
      * apply Specify_classification.
        rewrite despecify.
        split; unfold IQS; auto using elts_in_set.
        rewrite <-(rationals.M3 a) at 2.
        rewrite (rationals.M1 1).
        apply (O3 ℚ_ring_order); auto.
        now apply (inv_lt_1 ℚ_order).
      * apply Specify_classification.
        rewrite despecify.
        split; unfold IQS; auto using elts_in_set.
        rewrite <-(rationals.M3 b) at 2.
        rewrite (rationals.M1 1).
        apply (O3 ℚ_ring_order); auto.
        now apply (inv_lt_1 ℚ_order).
      * apply rationals.O2; auto.
        now apply (ordered_fields.inv_lt ℚ_order).
      * apply rationals.O2; auto.
        now apply (ordered_fields.inv_lt ℚ_order).
      * left; simpl.
        apply (O3 ℚ_ring_order (z^-1 * z^-1 * ξ))%Q in H8; simpl in *.
        -- replace ((z^-1*z^-1*ξ*(z*z)))%Q with ξ
            in * by (field; auto using (lt_neq ℚ_ring_order)).
           now replace (z^-1*z^-1*ξ*(a*(b*ξ^-1)))%Q with (a*z^-1*(b*z^-1))%Q
             in * by (field; auto using (lt_neq ℚ_ring_order)).
        -- repeat apply rationals.O2; auto;
             now apply (ordered_fields.inv_lt ℚ_order).
    + apply pos_nonempty in l as [c [H6 H7]].
      apply pos_nonempty in l0 as [d [H8 H9]].
      exists c, d, ξ.
      repeat split; auto.
      apply Specify_classification in H7 as [H7 H10].
      apply Specify_classification in H9 as [H9 H12].
      rewrite despecify, <-H5 in *.
      left.
      now apply rationals.O2.
    + apply pos_nonempty in l as [c [H6 H7]].
      apply pos_nonempty in l0 as [d [H8 H9]].
      exists c, d, ξ.
      repeat split; auto.
      apply Specify_classification in H7 as [H7 H10].
      apply Specify_classification in H9 as [H9 H12].
      rewrite despecify in *.
      left; simpl.
      eapply rationals.lt_trans; eauto.
      now apply rationals.O2.
Qed.

Theorem IQR_neg : ∀ a : Q, -a = (-a)%Q.
Proof.
  intros a.
  now rewrite <-(A3 (-a)%Q), <-(A4 a), A2,
  (A1 (-a)%Q), IQR_add, rationals.A4, A3_l.
Qed.

Theorem IQR_mul : ∀ a b : Q,  a * b = (a * b)%Q.
Proof.
  intros a b.
  destruct (T 0 a)
    as [[H [H0 H1]] | [[H [H0 H1]] | [H [H0 H1]]]], (T 0 b)
      as [[H2 [H3 H4]] | [[H2 [H3 H4]] | [H2 [H3 H4]]]]; unfold mul, zero in *;
    repeat destruct excluded_middle_informative; try tauto; subst.
  - rewrite IQR_mul_pos; auto.
  - apply IQR_eq in H3.
    subst.
    now rewrite (rings.mul_0_r ℚ_ring).
  - replace (a*b)%Q with (-(a*-b))%Q by ring.
    rewrite <-IQR_neg, <-IQR_mul_pos, IQR_neg; auto.
    now rewrite <-IQR_neg, <-lt_neg_0.
  - apply IQR_eq in H0.
    subst.
    now rewrite (rings.mul_0_l ℚ_ring).
  - apply IQR_eq in H0.
    subst.
    now rewrite (rings.mul_0_l ℚ_ring).
  - apply IQR_eq in H0.
    subst.
    now rewrite (rings.mul_0_l ℚ_ring).
  - replace (a*b)%Q with (-(-a*b))%Q by ring.
    rewrite <-IQR_neg, <-IQR_mul_pos, IQR_neg; auto.
    now rewrite <-IQR_neg, <-lt_neg_0.
  - apply IQR_eq in H3.
    subst.
    now rewrite (rings.mul_0_r ℚ_ring).
  - replace (a*b)%Q with (-a*-b)%Q by ring.
    rewrite <-IQR_mul_pos, ? IQR_neg; auto; now rewrite <-IQR_neg, <-lt_neg_0.
Qed.
