Set Warnings "-notation-overridden,-ambiguous-paths".
Require Export rationals.

Definition 𝐑 :=
  {α in P ℚ | α ≠ ∅ ∧ α ≠ ℚ ∧ (∀ p q : Q, p ∈ α → q < p → q ∈ α) ∧
              ∀ p : Q, p ∈ α → ∃ r : Q, p < r ∧ r ∈ α}.

Definition R := elts 𝐑.

Definition IRS (a : R) := elt_to_set a : set.
Coercion IRS : R >-> set.

Lemma Dedekind_cut_0 : ∀ (α : R) (p : set), p ∈ α → p ∈ ℚ.
Proof.
  move=> [α /[dup] /Specify_classification
            [/Powerset_classification H _] ?] ? /H //.
Qed.

Lemma Dedekind_cut_1 : ∀ α : R, ∅ ≠ α.
Proof.
  move=> [α /[dup] /Specify_classification [?]]
           [] /[swap] _ /[swap] ? /[swap] -> //.
Qed.

Lemma Dedekind_cut_2 : ∀ (α : R) (p q : Q), p ∈ α → q < p → q ∈ α.
Proof.
  move=> [α /[dup] /Specify_classification [? [? [? []]]]] //.
Qed.

Lemma Dedekind_cut_3 : ∀ (α : R) (p : Q), p ∈ α → ∃ r : Q, p < r ∧ r ∈ α.
Proof.
  move=> [α /[dup] /Specify_classification [? [? [? []]]]] //.
Qed.

Lemma Dedekind_cut_4 : ∀ α : R, ∀ p q : Q, p ∈ α → q ∉ α → p < q.
Proof.
  move=> [α /[dup] /Specify_classification [? [? [? [? ?]]]]] *.
  apply (ordered_rings.lt_not_ge ℚ_ring_order) => [[/= ? | ?]]; subst; eauto.
Qed.

Lemma Dedekind_cut_5 : ∀ α : R, ∀ r s : Q, r ∉ α → r < s → s ∉ α.
Proof.
  move=> [α /[dup] /Specify_classification
            [? [? [? [H ?]]]] ?] ? ? ? /H /[apply] //.
Qed.

Lemma Dedekind_cut_6 : ∀ a : R, ∃ q : Q, q ∉ a.
Proof.
  move=> [α /[dup] /Specify_classification
            [/Powerset_classification H
              [? [/[dup] ? /neq_sym /not_proper_subset_inhab]]]]
           [[] /Subset_equality /(_ H) // | ? [H0 ?] _ ?].
    by exists (mkSet H0 : Q).
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
  rewrite /le /lt /proper_subset => a b.
  split => [[[H H0] | H] | H]; subst; auto using Set_is_subset.
  case (classic (a = b)); intuition eauto using set_proj_injective.
Qed.

Theorem lt_trans : ∀ a b c : R, a < b → b < c → a < c.
Proof.
  move=> a b c [H H0] [H1 H2].
  split => [z H3 | ]; eauto.
  move: H1 => /[swap] <- /Subset_equality /(_ H) /(@eq_sym set) //.
Qed.

Theorem lt_trichotomy : ∀ a b : R, a < b ∨ a = b ∨ b < a.
Proof.
  move=> a b.
  (case (classic (a < b)); case (classic (a = b)); auto) => H H0.
  have [p [/[dup] /Dedekind_cut_0 H1 H2 H3]]: ∃ p, p ∈ a ∧ p ∉ b
      by eauto using not_proper_subset_inhab, set_proj_injective.
  (apply or_intror, or_intror, conj) =>
  [q /[dup] /Dedekind_cut_0 H4 H5 | ]; eauto using set_proj_injective.
  move: H2 H3 H5.
  rewrite (reify H1) (reify H4).
  eauto using Dedekind_cut_2, Dedekind_cut_4.
Qed.

Theorem T : ∀ a b : R, a < b ∧ a ≠ b ∧ ¬ b < a
                       ∨ ¬ a < b ∧ a = b ∧ ¬ b < a
                       ∨ ¬ a < b ∧ a ≠ b ∧ b < a.
Proof.
  (move: lt_trichotomy => /[swap] a /[swap] b /(_ a b) [[H H0] | [-> | [H H0]]];
                          [left | right; left | right; right]); repeat split;
  auto; try (contradict H0; subst; auto; move: H0 =>
               [] /Subset_equality /(_ H) -> //); move=> [H0 []] //.
Qed.

Theorem lub : ∀ A, A ⊂ 𝐑 → A ≠ ∅ → (∃ β : R, ∀ α : R, α ∈ A → α ≤ β) →
                   ∃ γ : R, (∀ α : R, α ∈ A → α ≤ γ) ∧
                            ∀ δ : R, (∀ α : R, α ∈ A → α ≤ δ) → γ ≤ δ.
Proof.
  move=> A H /Nonempty_classification [z /[dup] H0 /H H1]
           [[b /[dup] /Specify_classification [H2 [H3 [H4 [H5 H6]]]] B] H7].
  have H8: ⋃ A ∈ 𝐑.
  { apply Specify_classification.
    (repeat split) =>
      [ | | H8 | p q /Union_classification
                   [x [/[dup] H8 /H /Specify_classification
                        [H9 [H10 [H11 [H12 H13]]]] H14]] /H12 ? |
        p /Union_classification
          [x [/[dup] H8 /H /Specify_classification
               [H9 [H10 [H11 [H12 H13]]]] /H13 [r [H14 H15]]]]].
    - apply Powerset_classification => x /Union_classification [a [/H H8]].
      by apply (Dedekind_cut_0 (mkSet H8)).
    - rewrite (reify H1) in H0.
      move: (Dedekind_cut_1 (mkSet H1)) => /neq_sym.
      rewrite ? Nonempty_classification => [[x H8]].
      exists x.
      apply Union_classification; eauto.
    - move: H2 H4 => /Powerset_classification /Subset_equality -> //.
      rewrite -H8 => x /Union_classification [y [/[dup] H9 /H H10]].
      move: (H7 (mkSet H10) H9) => [[] /[swap] _ /[apply] | [] ->] //.
    - apply Union_classification; eauto.
    - exists r.
      rewrite Union_classification; eauto. }
  exists (mkSet H8).
  split => [α H9 | δ H9]; rewrite /le.
  - case (classic (α = (mkSet H8))); auto; left; split => [x H11 | ] /=.
    + apply Union_classification; eauto.
    + contradict H10.
      by apply set_proj_injective.
  - case (T (mkSet H8) δ) => [H10 | [H10 | [H10 [H11 H12]]]]; try tauto.
    have /= [s [/Union_classification [a /[swap] H13 [/[dup] /H H14]]]]:
      (∃ s, s ∈ (mkSet H8) ∧ s ∉ δ)
      by eauto using not_proper_subset_inhab, set_proj_injective.
    rewrite (reify H14) => /H9.
    rewrite /le => H16 H17.
    have []: ¬ δ < (mkSet H14) by (move: (T (mkSet H14) δ); tauto).
    split => [x H18 | ].
    + move: (H17) (H18) => /[dup] /(Dedekind_cut_0 (mkSet H14))
                            H19 /[swap] /Dedekind_cut_0 H20.
      rewrite (reify H19) (reify H20) => ?.
      eauto using Dedekind_cut_2, Dedekind_cut_4.
    + move: H13 => /[swap] -> [] //.
Qed.

Definition iqr_set (q : Q) := {x of type ℚ | (x < q)%Q}.

Theorem iqr_in : ∀ q, iqr_set q ∈ 𝐑.
Proof.
  move=> q.
  rewrite Specify_classification Powerset_classification
          Nonempty_classification.
  have G: (q + 1 ∈ ℚ) by eauto using elts_in_set.
  (((repeat split) => [z /Specify_classification [] | | H |
                        p x /[swap] H /Specify_classification [H0] |
                        p /Specify_classification [H]] //);
   first exists (q - 1); rewrite -? H ? Specify_classification ? despecify)
  => [ | | | /lt_dense [r []]]; eauto using elts_in_set, rationals.lt_trans.
  - rewrite -[rationals.lt]/(ordered_rings.lt ℚ_ring_order)
                           (ordered_rings.lt_shift ℚ_ring_order) /=.
    replace (q + -(q - 1)) with 1 by field.
    eauto using elts_in_set, (ordered_rings.zero_lt_1 ℚ_ring_order : 0 < 1)%Q.
  - move: G.
    rewrite -H Specify_classification despecify =>
              [[]] _ /(lt_antisym ℚ_ring_order) [].
    eauto using (lt_succ ℚ_ring_order).
  - exists r.
    rewrite Specify_classification despecify.
    eauto using elts_in_set.
Qed.

Definition IQR (q : Q) := (mkSet (iqr_in q)) : R.
Definition zero := IQR 0.

Coercion IQR : Q >-> R.

Notation "0" := zero : R_scope.

Definition add_set (α β : R) := {x in ℚ | ∃ r s, x = r + s ∧ r ∈ α ∧ s ∈ β}.

Lemma not_Q_subset : ∀ α : R, ¬ ℚ ⊊ α.
Proof.
  move: Dedekind_cut_0 => /[swap] α /(_ α) H [/Subset_equality] /(_ H) //.
Qed.

Lemma not_Q_eq : ∀ α : R, (α : set) ≠ ℚ.
Proof.
  move=> [α /[dup] /Specify_classification [_ [_ [_]]]] //.
Qed.

Theorem add_in : ∀ α β, add_set α β ∈ 𝐑.
Proof.
  move=> α β.
  (rewrite Specify_classification Powerset_classification
           Nonempty_classification); (repeat split) =>
    [z /Specify_classification [] | | |
      p q /Specify_classification [H [r [s [/set_proj_injective -> [H0 H1]]]]]
        /(O1 (-s)) H2 | p /Specify_classification
                          [H [r [s [/set_proj_injective ->
                                    [/Dedekind_cut_3 [t [H0 H1]] H2]]]]]] //.
  - move: (Dedekind_cut_1 α) (Dedekind_cut_1 β) => /neq_sym =>
          /Nonempty_classification [x /[dup] /Dedekind_cut_0 H H0]
           /neq_sym /Nonempty_classification [y /[dup] /Dedekind_cut_0 H1 H2].
    exists (mkSet H + mkSet H1).
    apply Specify_classification.
    split; eauto using elts_in_set.
  - move: (not_proper_subset_inhab ℚ α) (not_proper_subset_inhab ℚ β) =>
          [ | | r' [H H0] [ | | s' [H1 H2]]]; auto using not_Q_subset, not_Q_eq
          => /Subset_equality_iff [H3 H4].
    move: (elts_in_set ((mkSet H) + (mkSet H1))) => /H4 =>
          /Specify_classification [H5 [r [s [/set_proj_injective H6 [H7 H8]]]]].
    contradiction (lt_irrefl ℚ_ring_order (r + s)).
    rewrite -{2}H6.
    apply (lt_cross_add ℚ_ring_order) => /=; eauto using Dedekind_cut_4.
  - apply Specify_classification.
    split; eauto using elts_in_set.
    exists (-s + q), s.
    ring_simplify in H2.
    intuition (eauto using Dedekind_cut_2 || f_equal; ring).
  - exists (t+s).
    rewrite Specify_classification {1}(rationals.A1 t s) (rationals.A1 r).
    intuition eauto using elts_in_set, O1.
Qed.

Definition add (a b : R) := mkSet (add_in a b) : R.

Infix "+" := add : R_scope.

Theorem A1 : ∀ a b, a + b = b + a.
Proof.
  rewrite /add => a b.
  apply set_proj_injective, Extensionality => /= z.
  rewrite ? Specify_classification.
  split => [[H [r [s [H0 [H1 H2]]]]] | [H [r [s [H0 [H1 H2]]]]]];
  repeat split; auto; exists s, r; rewrite A1; repeat split; auto.
Qed.

Theorem A2 : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  rewrite /add => a b c.
  apply set_proj_injective, Extensionality => z.
  rewrite ? Specify_classification.
  (split => [[H [r [s [H0 [H1 /Specify_classification
                              [H2 [t [u [/set_proj_injective H3 [H4 H5]]]]]]]]]]
            | [H [r [s [H0 [/Specify_classification
                             [H1 [t [u [/set_proj_injective H2 [H3 H4]]]]]
                             H5]]]]]]); subst; split; auto;
  [exists (r + t)%Q, u | exists t, (u + s)%Q]; rewrite Specify_classification;
  repeat split; eauto using elts_in_set; f_equal; ring.
Qed.

Theorem A3 : ∀ a, a + 0 = a.
Proof.
  rewrite /add /zero => α.
  apply set_proj_injective, Extensionality => z.
  split => [/Specify_classification
             [H [r [s [-> [H0 /Specify_classification [H1]]]]]] |
             /[dup] /Dedekind_cut_0 H].
  - rewrite despecify => H2.
    eapply Dedekind_cut_2; eauto.
    have {2}->: r = (r + 0)%Q by ring.
    auto using O1.
  - rewrite Specify_classification (reify H) => /Dedekind_cut_3 [r [H0 H1]].
    split; auto.
    exists r, ((mkSet H) + -r)%Q.
    repeat split; auto; rewrite 1 ? (rationals.A1 _ (-r)) ? (rationals.A2);
      rewrite ? (rationals.A4) ? (rationals.A3) // ? Specify_classification
              ? despecify -(A4 r) ? (rationals.A1 _ (-r)).
    eauto using elts_in_set, O1.
Qed.

Definition neg_set (α : R) :=
  {p of type ℚ | ∃ r : Q, (0 < r)%Q ∧ (- p - r)%Q ∉ α}.

Theorem neg_in : ∀ a, neg_set a ∈ 𝐑.
Proof.
  move=> α.
  rewrite Specify_classification Powerset_classification
          Nonempty_classification.
  (repeat split) => [z /Specify_classification [] | | | p q | p ] //.
  - move: (elts_in_set α) => /Specify_classification =>
          [[/Powerset_classification H [H0 [/neq_sym H1 [H2 H3]]]]].
    elim (not_proper_subset_inhab ℚ α) =>
           [s [H4 H5] | [] /Subset_equality /(_ H) | ] //.
    set (σ := mkSet H4 : Q).
    exists (-σ - 1 : Q).
    rewrite Specify_classification despecify.
    split; eauto using elts_in_set.
    exists 1.
    repeat split; auto using (ordered_rings.zero_lt_1 ℚ_ring_order : 0 < 1)%Q.
    by have ->: (-(-σ - 1) - 1)%Q = σ by ring.
  - move: (Dedekind_cut_1 α) => /neq_sym /Nonempty_classification
                                 [s /[dup] /Dedekind_cut_0 H H0].
    set (σ := (mkSet H) : Q) => H1.
    move: (elts_in_set (-σ)) => /[dup]; simpl in *.
    rewrite -{2 4}H1 => H2.
    rewrite Specify_classification despecify => [[H3 [r [H4 []]]]].
    apply (Dedekind_cut_2 _ σ); auto.
    rewrite -[rationals.lt]/(ordered_rings.lt ℚ_ring_order)
                           (ordered_rings.lt_shift ℚ_ring_order) /=.
    by have ->: (σ + -(--σ - r))%Q = r by ring.
  - rewrite ? Specify_classification ? despecify => [[H [r [H1 H2]]]] H3.
    split; eauto using elts_in_set.
    exists r.
    repeat split; auto.
    contradict H2.
    apply (Dedekind_cut_2 _ (-q - r)); auto.
    rewrite /sub ? (rationals.A1 _ (-r)).
    by apply O1, (neg_neg_lt ℚ_ring_order).
  - rewrite ? Specify_classification ? despecify =>
              [[H [r [/[dup] H0 /(O1 p) /[swap] H1]]]].
    rewrite rationals.A1 rationals.A3 => /lt_dense [t [H2 H3]].
    exists t.
    rewrite Specify_classification despecify.
    repeat split; eauto using elts_in_set.
    exists (p + r - t).
    repeat split; auto.
    + by apply (ordered_rings.lt_shift ℚ_ring_order) in H3.
    + by have ->: (-t - (p + r - t) = -p - r) by ring.
Qed.

Definition neg (a : R) := mkSet (neg_in a) : R.

Notation "- a" := (neg a) : R_scope.

Theorem cut_archimedean : ∀ (α : R) (b : Q),
    (0 < b)%Q → ∃ n : Z, n * b ∈ α ∧ (n + 1) * b ∉ α.
Proof.
  move=> α b H.
  move: (elts_in_set α) => /Specify_classification =>
        [[/Powerset_classification H0 [/Nonempty_classification
                                        [x /[dup] /Dedekind_cut_0 H1]]]].
  rewrite ? (reify H1) => [H2 [H3 [H4 H5]]].
  elim (Q_archimedean (mkSet H1) b) => [k [H6 H7] | ] //.
  elim (WOP (λ m, (k + m)%Z * b ∉ α)) => [n [H8 H9] | m H8 | ].
  - exists (k + (n + -1))%Z.
    rewrite ? IZQ_add.
    split; last by have ->: (k + (n + -1) + 1 = k + n)%Z by ring.
    apply NNPP => /[dup] H10 /H9 /(le_not_gt ℤ_order) [].
    rewrite (ordered_rings.lt_shift ℤ_order) /=.
    have ->: (n + -(n + -1) = 1)%Z by ring.
    auto using integers.zero_lt_1.
  - apply NNPP.
    contradict H8.
    move: H8 => /(le_not_gt ℤ_order) => [[H8 | ->]].
    + apply (H4 (mkSet H1)); auto; (case: H6 => [H6 | H6]);
        rewrite -IZQ_add -[rationals.lt]/(ordered_rings.lt ℚ_ring_order);
        ring_simplify; [apply (ordered_rings.lt_trans ℚ_ring_order _ (k*b)) | ];
        auto; (rewrite -? H6 (ordered_rings.lt_shift ℚ_ring_order) /=);
        (have ->: (k * b + -(k * b + m * b) = -m * b)%Q by field);
        apply O2; auto; by rewrite (lt_neg_0 ℤ_order) /= IZQ_lt -IZQ_neg in H8.
    + rewrite -> (A3_r ℤ).
      case: H6 => [H6 | ->]; eauto.
  - elim: (not_proper_subset_inhab ℚ α) =>
          [z [H8 H9] | [/Subset_equality /(_ H0) H8 H9] | ]; auto.
    elim: (Q_archimedean (mkSet H8) b) => [m [H10 H11] | ] //.
    exists (m - k + 1)%Z.
    have ->: (k + (m - k + 1) = m + 1)%Z by ring.
    apply (Dedekind_cut_5 α (mkSet H8)); auto.
    by rewrite -IZQ_add.
Qed.

Theorem A4 : ∀ a, a + -a = 0.
Proof.
  move=> α.
  apply set_proj_injective, Extensionality => z.
  split => [/Specify_classification [H [r [p [-> [] H1]]]] |
             /Specify_classification [H]].
  - rewrite ? Specify_classification ? despecify =>
              [[H2 [q [/[dup] H3 /(O1 (-p - q)) H4 H5]]]].
    ring_simplify in H4.
    (have: (-p ∉ α)%Q by eauto using Dedekind_cut_5) =>
      /Dedekind_cut_4 => /(_ _ H1) /(O1 p) H6.
    rewrite A4 rationals.A1 in H6.
    eauto using elts_in_set.
  - rewrite (reify H) despecify => H0.
    set (v := mkSet H : Q).
    set (w := (-v * 2^-1)%Q).
    have H1: (0 < 2)%Z by apply (ordered_rings.zero_lt_2 ℤ_order).
    have H2: (0 < w)%Q.
    { apply rationals.O2; try now apply (lt_neg_0 ℚ_ring_order).
      now apply (O4 ℚ_order), IZQ_lt. }
    elim: (cut_archimedean α w) => [n [H3 H4] | ] //.
    apply Specify_classification.
    split; auto.
    exists (n * w)%Q, (-(n + 2) * w)%Q.
    repeat split; auto; rewrite /IQS /w ? Specify_classification ? despecify.
    + f_equal.
      ring_simplify.
      rewrite -M2 inv_l 1 ? M1 ? M3 // => /IZQ_eq H5.
      contradiction (ordered_rings.lt_irrefl ℤ_order 0%Z).
      by rewrite -{2}H5.
    + split; eauto using elts_in_set.
      exists w.
      repeat split; auto.
      have ->: (-(-(n + 2) * w) - w = n * w + 2 * w + -w)%Q by ring.
      have ->: ((2 : Q) = 1 / 1 + 1 / 1)%Q; first rewrite add_wf;
        auto using integers.zero_ne_1;
        rewrite /IZQ ? Qequiv ? (integers.M1 2) ? integers.M3 ? D1 ? M3
                -? rationals.A2 ? A4 ? (rationals.A1 w) ? rationals.A3
                -1 ? {2}(M3 w) -? D1 //; auto using integers.zero_ne_1.
Qed.

Theorem O1 : ∀ a b c, b < c → a + b < a + c.
Proof.
  move=> a b c [H H0].
  split => [z /Specify_classification [H1 [r [s [H2 [H3 /H H4]]]]] | ].
  - apply Specify_classification.
    intuition eauto.
  - move: H0 => /[swap] /set_proj_injective /(f_equal (add (-a))).
    rewrite ? A2 ? (A1 (-a)) ? A4 ? (A1 0) ? A3 => -> //.
Qed.

Theorem lt_irrefl : ∀ a, ¬ a < a.
Proof.
  move=> a [H H0] //.
Qed.

Theorem lt_antisym : ∀ a b, a < b → ¬ b < a.
Proof.
  move=> a b /lt_trans /[apply] /lt_irrefl //.
Qed.

Definition mul_pos_set (a b : R) :=
  {x of type ℚ | (∃ r s : Q, r ∈ a ∧ s ∈ b ∧ 0 < r ∧ 0 < s ∧ x ≤ r * s)%Q}.

Definition one : R := IQR 1.
Notation "1" := one : R_scope.
Notation "- 1" := (neg one) : R_scope.

Theorem pos_nonempty : ∀ a, 0 < a → ∃ c : Q, (0 < c)%Q ∧ c ∈ a.
Proof.
  move=> a /proper_subset_inhab [c [/[dup] /Dedekind_cut_0 H H0 H1]].
  have H2: ¬ (mkSet H < 0)%Q by
    rewrite Specify_classification (reify H) despecify in H1; auto.
  (case (classic (mkSet H = 0%Q)) => [ | H3]);
  first by elim: (Dedekind_cut_3 a (mkSet H) H0) => [x] /[swap] ->; eauto.
  exists (mkSet H).
  split; auto.
  apply (ordered_rings.lt_not_ge ℚ_ring_order) => [[ | ]] //.
Qed.

Theorem mul_pos_in : ∀ a b, 0 < a → 0 < b → mul_pos_set a b ∈ 𝐑.
Proof.
  move=> a b /[dup] H /pos_nonempty [c [H0 H1]]
           /[dup] H2 /pos_nonempty [d [H3 H4]].
  rewrite Specify_classification Powerset_classification
          Nonempty_classification.
  (repeat split) => [x | | /Subset_equality_iff [H5 H6] | p q | p].
  - rewrite Specify_classification => [[]] //.
  - exists (c * d - 1).
    rewrite Specify_classification despecify.
    split; eauto using elts_in_set.
    exists c, d.
    repeat split; auto.
    left.
    apply lt_sub_pos, (ordered_rings.zero_lt_1 ℚ_ring_order).
  - move: (Dedekind_cut_6 a) (Dedekind_cut_6 b) => [c' H7] [d' H8].
    have: c' * d' ∈ mul_pos_set a b by eauto using elts_in_set.
    rewrite Specify_classification despecify
            -[rationals.le]/(ordered_rings.le ℚ_ring_order)
            => [[H9 [r [s [H10 [H11 [H12 [H13]]]]]]]].
    rewrite (le_not_gt ℚ_ring_order) => [[]].
    eapply (lt_cross_mul ℚ_ring_order); simpl; eauto using Dedekind_cut_4.
  - rewrite ? Specify_classification ? despecify =>
              [[H5 [r [s [H6 [H7 [H8 [H9 H10]]]]]]]] H11.
    split; eauto using elts_in_set.
    exists r, s.
    repeat split; auto; left.
    move: H10 H11 => [ | ->] // /= /[swap] /rationals.lt_trans /[apply] //.
  - rewrite Specify_classification despecify =>
              [[H5 [r [s [/Dedekind_cut_3 [ρ [H6 H7]]
                           [/Dedekind_cut_3 [σ [H8 H9]] [H10 [H11 H12]]]]]]]].
    exists (ρ * σ)%Q.
    have H13: (r * s < ρ * σ)%Q by (apply (lt_cross_mul ℚ_ring_order); eauto).
    split.
    + move: H12 => [ | ->] // /rationals.lt_trans /(_ H13) //.
    + rewrite Specify_classification despecify /rationals.le /ordered_rings.le.
      split; eauto using elts_in_set.
      exists ρ, σ.
      repeat split; eauto using rationals.lt_trans.
Qed.

Definition mul_pos : R → R → R.
Proof.
  move=> a b.
  case: (excluded_middle_informative (0 < a))
          (excluded_middle_informative (0 < b)) =>
        H [H0 | H0]; first exact (mkSet (mul_pos_in a b H H0)); exact 0.
Defined.

Local Infix "·" := mul_pos (at level 40) : R_scope.

Theorem M1_pos : ∀ a b, 0 < a → 0 < b → a · b = b · a.
Proof.
  rewrite /mul_pos /mul_pos_set => a b H H0.
  repeat elim excluded_middle_informative => * //.
  apply set_proj_injective, Extensionality => z.
  rewrite ? Specify_classification ? despecify.
  (split => [[H1] | [H1]]; rewrite ? (reify H1) ? despecify) =>
    [[r [s [H2 [H3 [H4 [H5 H6]]]]]] | [r [s [H2 [H3 [H4 [H5 H6]]]]]]];
    split; auto; exists s, r; rewrite M1; split; auto.
Qed.

Theorem O2_pos : ∀ a b, 0 < a → 0 < b → 0 < a · b.
Proof.
  rewrite /mul_pos => a b /[dup] ? /pos_nonempty
                        [c [/[dup] ? /lt_dense [c' [? ?]] ?]] /[dup] ?
                        /pos_nonempty [d [/[dup] ? /lt_dense [d' [? ?]] ?]].
  repeat elim excluded_middle_informative => * //.
  split => [z /Specify_classification [H] | H].
  - rewrite (reify H) Specify_classification ? despecify.
    split; auto.
    exists c, d.
    repeat split; auto; left => /=.
    eauto using O2, rationals.lt_trans.
  - (have: (c' * d')%Q ∈ 0; first rewrite H;
     rewrite Specify_classification despecify) =>
      [ | [] _ /(lt_not_ge ℚ_ring_order) []]; last by apply or_introl, O2.
    split; eauto using elts_in_set.
    exists c, d.
    repeat split; eauto using rationals.lt_trans; left => /=.
    by apply (lt_cross_mul ℚ_ring_order).
Qed.

Theorem M2_pos : ∀ a b c, 0 < a → 0 < b → 0 < c → a · (b · c) = (a · b) · c.
Proof.
  rewrite /mul_pos => a b c /[dup] H /O2_pos H0 /[dup] /H0 {}H0 /[dup] H1
                        /O2_pos H2 /[dup] /H2 {}H2 H3.
  repeat destruct excluded_middle_informative; try tauto;
    try (contradict n; unfold mul_pos in *;
         repeat destruct excluded_middle_informative; tauto).
  apply set_proj_injective, Extensionality => z.
  rewrite ? Specify_classification.
  (split => [[H4] | [H4]]; rewrite (reify H4) ? despecify /= =>
     [[ρ [τ [H5 [H6 [H7 [H8 H9]]]]]]]); [move: (H6) | move: (H5)];
  rewrite Specify_classification despecify =>
    [[H10 [r [s [H11 [H12 [H13 [H14 H15]]]]]]]]; split;
    eauto using elts_in_set; [exists (ρ * r)%Q, s | exists r, (s * τ)%Q];
    rewrite ? Specify_classification ? despecify; repeat split;
    eauto using O2, elts_in_set; [exists ρ, r | | exists s, τ | ];
    try (repeat split; auto; by right);
    [apply (mul_le_l ℚ_ring_order ρ) in H15; auto; rewrite -M2 |
      apply (mul_le_r ℚ_ring_order _ _ τ) in H15; auto; rewrite M2];
    eapply (ordered_rings.le_trans ℚ_ring_order); eauto.
Qed.

Theorem zero_ne_1 : 1 ≠ 0.
Proof.
  rewrite /zero /one => H.
  inversion H as [H0].
  move: H0 (ordered_rings.zero_lt_1 ℚ_ring_order) =>
        /Subset_equality_iff [H0 H1] /lt_dense [c [H2 H3]].
  contradiction (ordered_rings.lt_antisym ℚ_ring_order c 0%Q).
  move: (H0 c).
  rewrite ? Specify_classification ? despecify => [[]]; eauto using elts_in_set.
Qed.

Theorem zero_lt_1 : 0 < 1.
Proof.
  split => [z | /set_proj_injective /(@eq_sym R) /zero_ne_1] //.
  rewrite ? Specify_classification => [[]] H.
  rewrite ? (reify H) ? despecify =>
            /rationals.lt_trans /(_ (ordered_rings.zero_lt_1 ℚ_ring_order)) //.
Qed.

Theorem M3_pos : ∀ a, 0 < a → 1 · a = a.
Proof.
  rewrite /mul_pos => a H.
  repeat elim excluded_middle_informative => *; try (move: zero_lt_1; tauto).
  apply set_proj_injective, Extensionality => z.
  ((split => [ | /[dup] /Dedekind_cut_0]; rewrite Specify_classification) =>
     [[H0] | H0]; rewrite (reify H0) despecify) =>
    [[r [s [/Specify_classification [H1] /[swap] [[H2 [H3 [/[swap] H4]]]]]]] |
      /[dup] H1 /Dedekind_cut_3 [t [H2 H3]]].
  - rewrite despecify => /[swap] /(O3 ℚ_ring_order s) /[apply] H6.
    eapply Dedekind_cut_2; eauto.
    rewrite ? (M1 r s) /= -? (rationals.M1 1%Q) ? rationals.M3 in H4 H6.
    eapply (le_lt_trans ℚ_ring_order); eauto.
  - case: (classic (0 < (mkSet H0))%Q) => [H4 | ].
    + split; eauto using elts_in_set.
      exists ((mkSet H0) * t^-1)%Q, t.
      have H5: (t ≠ 0)%Q by eapply (lt_neq ℚ_ring_order),
          rationals.lt_trans; eauto.
      repeat split; eauto using rationals.lt_trans.
      * rewrite Specify_classification despecify.
        split; eauto using elts_in_set.
        rewrite -(inv_l t) ? (M1 (mkSet H0)); auto.
        apply (O3 ℚ_ring_order); try apply (inv_lt ℚ_order) => /=; auto.
        eauto using rationals.lt_trans.
      * apply O2, (inv_lt ℚ_order) => /=; eauto using rationals.lt_trans.
      * rewrite -M2 inv_l 1 ? M1 ? M3 /rationals.le /ordered_rings.le; auto.
    + rewrite -(le_not_gt ℚ_ring_order)
              -[(ordered_rings.le ℚ_ring_order)]/(rationals.le) => H4.
      move: zero_lt_1 H => /pos_nonempty [c [H5 H6]] /pos_nonempty [d [H7 H8]].
      split; eauto using elts_in_set.
      exists c, d.
      repeat split; auto; left.
      eapply (le_lt_trans ℚ_ring_order) => /=; eauto using O2.
Qed.

Definition inv_pos_set (α : R) :=
  {p of type ℚ | ∃ r : Q, 1 < r ∧ (p ≤ 0 ∨ (0 < p ∧ (p * r)^-1 ∉ α))}%Q.

Theorem inv_pos_in : ∀ a, 0 < a → inv_pos_set a ∈ 𝐑.
Proof.
  move=> a /[dup] H /pos_nonempty [c [/[dup] H0 /[dup] /(lt_neq ℚ_ring_order)
                                       H1 /(inv_lt ℚ_order) /= H2 H3]].
  rewrite Specify_classification Powerset_classification
          Nonempty_classification.
  (repeat split) => [x /Specify_classification [] | | H4 | p q | p] //.
  - exists 0%Q.
    rewrite Specify_classification despecify.
    split; eauto using elts_in_set.
    exists 2.
    repeat split; eauto using zero_lt_1, one_lt_2, rationals.lt_trans.
    by left; right.
  - have: c^-1 ∈ ℚ by eauto using elts_in_set.
    rewrite -H4 Specify_classification despecify =>
              [[H5 [r [/[dup] H6 /[dup] /(ordered_fields.inv_lt_1 ℚ_order) /=
                        H7 /(one_lt ℚ_ring_order) /= /[dup] H8
                        /(lt_neq ℚ_ring_order) H9 [[/= ? | H10] | [? H11]]]]]].
    + move: H2 => /(ordered_rings.lt_antisym ℚ_ring_order) [] //.
    + move: H10 H2 -> => /(ordered_rings.lt_antisym ℚ_ring_order) //.
    + contradict H11.
      eapply Dedekind_cut_2; eauto.
      have ->: (c^-1 * r)^-1 = r^-1 * c by (field; auto).
      rewrite -{2}(rationals.M3 c).
      apply (O3_r ℚ_ring_order) => /=; auto.
  - (rewrite ? Specify_classification ? despecify) =>
      [[H4 [r [/[dup] H5 /(one_lt ℚ_ring_order) /= H6
                [H7 H8 | [H7 H8] /[dup] H9 /(ordered_rings.O3 ℚ_ring_order r)
                                 /= H10]]]]]; split; eauto using elts_in_set;
      exists r; repeat split; auto.
    + repeat left.
      eapply (lt_le_trans ℚ_ring_order); eauto.
    + (elim (classic (q ≤ 0)%Q); try tauto) => /lt_not_ge /= H11.
      eapply or_intror, conj, Dedekind_cut_5; eauto.
      (rewrite -[rationals.lt]/(ordered_fields.lt ℚ_order) -lt_cross_inv /=);
      rewrite ? (M1 _ r); eauto using O3, O2, rationals.lt_trans.
  - rewrite Specify_classification despecify =>
              [[? [r [/[dup] ? /[dup] /lt_dense
                       [c' [/[dup] ? /(one_lt ℚ_ring_order) /= /[dup] /[dup]
                             ? /(inv_lt ℚ_order) /= ? /(lt_neq ℚ_ring_order)
                             /= ? ?]] /(one_lt ℚ_ring_order) /= /[dup]
                       /(lt_neq ℚ_ring_order) /= ? /[dup] ?
                       /(inv_lt ℚ_order) /= ? [[/= ? | ?] | [? ?]]]]]].
    + exists 0%Q.
      rewrite Specify_classification despecify.
      eauto 6 using elts_in_set, one_lt_2, (le_refl ℚ_ring_order 0 : 0 ≤ 0)%Q.
    + subst.
      move: (Dedekind_cut_6 a) => [c'' H14].
      exists (c''^-1 * r^-1 * r^-1)%Q.
      have /[dup] /(inv_lt ℚ_order) /= *: (0 < c'')%Q.
      { eapply Dedekind_cut_4; eauto.
        move: H => /pos_nonempty [d] [] /Dedekind_cut_2 /[apply] //. }
      rewrite Specify_classification despecify.
      repeat split; eauto using elts_in_set, O2.
      exists r.
      repeat (split; try right); auto using O2.
      eapply Dedekind_cut_5; eauto.
      rewrite -M2 inv_l // -(M1 1) M3 inv_mul inv_inv -{1}(M3 c'') -(M1 c'').
      apply (O3 ℚ_ring_order); auto.
    + exists (p * r * c'^-1)%Q.
      rewrite -{1}(M3 p) -(M1 p) -M2 Specify_classification despecify.
      repeat split; eauto using elts_in_set.
      * apply (O3 ℚ_ring_order), (lt_div ℚ_order); auto.
      * exists c'.
        rewrite -? M2 inv_l // -(M1 1) M3.
        auto 6 using O2.
Qed.

Definition inv_pos : R → R.
Proof.
  move=> a.
  case (excluded_middle_informative (0 < a)) => [H | H].
  - exact (mkSet (inv_pos_in _ H)).
  - exact 0.
Defined.

Local Notation "a '^-1' " :=
  (inv_pos a) (at level 30, format "a '^-1'") : R_scope.

Lemma pos_not_in_0 : ∀ x : Q, (0 < x)%Q → x ∉ 0.
Proof.
  move=> x H /Specify_classification [H0].
  rewrite despecify => /(ordered_rings.lt_antisym ℚ_ring_order) //.
Qed.

Theorem inv_lt : ∀ a, 0 < a → 0 < a^-1.
Proof.
  rewrite /lt /inv_pos => a /[dup] H /pos_nonempty [c [H0 H1]].
  split => [z /Specify_classification [H2] | ].
  - elim excluded_middle_informative => // H4.
    rewrite Specify_classification ? (reify H2) ? despecify.
    split; auto.
    exists 2%Q.
    repeat split; auto using one_lt_2.
    by repeat left.
  - elim excluded_middle_informative => // H2 H3.
    elim: (Dedekind_cut_6 a) => x H4.
    have /[dup] /(inv_lt ℚ_order) /= /[swap]: (0 < 2)%Q => [ | H5].
    { rewrite -IZQ_add.
      apply (ordered_rings.zero_lt_2 ℚ_ring_order). }
    (have /[dup] /(inv_lt ℚ_order) /= /[swap]: (0 < x)%Q by
      eauto using Dedekind_cut_2, Dedekind_cut_4) =>
      H6 /O2 /[apply] /[dup] H7 /pos_not_in_0 [].
    rewrite -> H3.
    unfold inv_pos, inv_pos_set.
    rewrite Specify_classification despecify.
    split; eauto using elts_in_set.
    exists 2%Q.
    repeat split; auto using one_lt_2.
    right.
    split; auto using O2.
    rewrite <-M2, inv_l, M1, M3, inv_inv; auto using (lt_neq ℚ_ring_order).
Qed.

Theorem pow_archimedean : ∀ (a : R) (r : Q),
    0 < a → (1 < r)%Q → ∃ n : Z, (r^n)%Q ∈ a ∧ (r^(n + 1))%Q ∉ a.
Proof.
  move=> a r /[dup] H /pos_nonempty [c [H0 H1]] /[dup]
           /(ordered_rings.one_lt ℚ_ring_order) /= H2.
  move: (Dedekind_cut_6 a) => [q H3] /[dup] /(neg_pow_archimedean c r H0)
      => [[m [H4 H5]]] /[dup] H6 /(pos_pow_archimedean q r) [n [H7 H8]].
  move: (WOP (λ x, (r^(m + x))%Q ∉ a)) => [x H9 | | x [H9 H10]].
  - apply (lt_not_ge ℤ_order) => /= [[/= H10 | H10]].
    + rewrite -[rationals.pow]/(fields.pow ℚ) (pow_add_r ℚ) /= in H9;
        auto using (lt_neq ℚ_ring_order).
      eapply H9, Dedekind_cut_2; eauto.
      rewrite -(M3 c) (M1 1).
      apply (lt_cross_mul ℚ_ring_order); auto; try by apply (pow_pos ℚ_order).
      by apply (pow_lt_1 ℚ_order).
    + rewrite H10 integers.A1 integers.A3 in H9.
      eauto using Dedekind_cut_2.
  - exists (n + -m)%Z.
    have ->: (m + (n + -m) = n)%Z by ring.
    eauto using Dedekind_cut_5.
  - exists (m + (x + -1))%Z.
    split; last by have ->: (m + (x + -1) + 1 = m + x)%Z by ring.
    apply NNPP => /H10 /le_not_gt [] /=.
    have {2}->: (x = x + 1 + -1)%Z by ring.
    apply (O1_r ℤ_order), lt_succ.
Qed.

Theorem M4_pos : ∀ a, 0 < a → a^-1 · a = 1.
Proof.
  rewrite /mul_pos => a H.
  apply set_proj_injective, Extensionality => z.
  (repeat case excluded_middle_informative) => // => [ | /inv_lt] // {}H H0.
  rewrite ? Specify_classification.
  (split => [[H1] | [H1]]; rewrite ? (reify H1) ? despecify) =>
    [[r [s [/[swap] [[H2 [H3 [H4 H5]]]]]]] | H2].
  - rewrite /inv_pos.
    case excluded_middle_informative => // {}H.
    rewrite Specify_classification despecify /= =>
              [[H6 [q [/[dup] H7 /[dup] /(one_lt ℚ_ring_order) /= /[dup]
                        /(lt_neq ℚ_ring_order) H8 H9 /(inv_lt_1 ℚ_order) /=
                        /(_ H9) H10 [/le_lt_trans /(_ H3)
                                      /ordered_rings.lt_irrefl |
                                      [/[dup] H11 /(lt_neq ℚ_ring_order) H12
                                        /(Dedekind_cut_4 _ _ _ H2) H13]]]]]] //.
    split; auto.
    eapply (ordered_rings.lt_trans ℚ_ring_order); eauto.
    eapply le_lt_trans; eauto => /=.
    have ->: (q^-1 = r * (r * q)^-1)%Q by field.
    by apply (O3 ℚ_ring_order).
  - split; auto.
    move: (H) (H0) (H2) => /pos_nonempty [c [H3 H4]] /pos_nonempty [d [H5 H6]].
    rewrite -{1} (inv_inv (mkSet H1)) => /(inv_lt_1 ℚ_order) /=.
    (case (classic (0 < (mkSet H1))%Q) =>
       [/[dup] H7 /(ordered_fields.inv_lt ℚ_order) /= /[dup] H8 /[swap]
         /[apply] /[dup] H9 /square_in_interval
         [r [/[dup] H10 /(lt_neq ℚ_ring_order) H11
              [/[dup] /(square_ge_1 ℚ_ring_order _ H10) /=
                /[dup] H12 /(pow_archimedean _ _ H) [n [H13 H14]] H15 H16]]] |
         /(le_not_gt ℚ_ring_order) H7]);
    last by rewrite /rationals.le /ordered_rings.le;
    eauto 10 using le_lt_trans, (ordered_rings.O2 ℚ_ring_order).
    exists (r^(-(n+2))), (r^n).
    (repeat split; auto; try now apply (pow_pos ℚ_order));
    rewrite /inv_pos /pow -? [rationals.mul]/(rings.mul ℚ) -? pow_add_r //.
    + case excluded_middle_informative => // {}H.
      rewrite Specify_classification despecify.
      split; eauto using elts_in_set.
      exists r.
      split; auto.
      right.
      split; first by apply (pow_pos ℚ_order).
      rewrite -inv_mul -? inv_pow -pow_mul_r /pow -[rationals.mul]/(rings.mul ℚ)
              -pow_add_r //.
      by have ->: (-(n + 2) * -1 + -1 = n + 1)%Z by ring.
    + have ->: (-(n + 2) + n = -2%Z)%Z by ring.
      rewrite -/pow (neg_pow r 2%Z) -(inv_inv (mkSet H1)).
      apply or_introl, (lt_cross_inv ℚ_order (r^2)%Q); auto;
        rewrite /pow /fields.pow INZ_add add_1_r pow_nonneg pow_2_r // /=.
      by apply O2.
Qed.

Theorem D1_pos : ∀ a b c, 0 < a → 0 < b → 0 < c → (a + b) · c = a · c + b · c.
Proof.
  rewrite /mul_pos /add_set /mul_pos_set => a b c H /[dup] H0 /(O1 a) /[swap].
  move: A3 (H) -> => /lt_trans /[swap] H1 /[apply] H2.
  repeat destruct excluded_middle_informative; try tauto;
    try (contradict n; unfold mul_pos in *;
         repeat destruct excluded_middle_informative; tauto).
  apply set_proj_injective, Extensionality => z.
  (split => /Specify_classification [H3];
            rewrite ? Specify_classification ? (reify H3) ? despecify) =>
    [[r [s [/Specify_classification
             [H4 [r' [s' [/set_proj_injective -> [H5 H6]]]]]
             [H7 [/[dup] H8 /(O0_opp ℚ_ring_order) H9 [H10 H11]]]]]] |
      [ac [bc [/set_proj_injective H4 [H5 H6]]]]];
    repeat split; auto; set (ζ := mkSet H3 : Q).
  - move: (pos_nonempty a H) (pos_nonempty b H0) => [t [H12 ?]] [t' [H14 ?]].
    move: (lt_dense2 t (r'+s') H12 H8) (lt_dense2 t' (r'+s') H14 H8) =>
    [k [? [? ?]]] [k' [? [? ?]]].
    (case: (classic (0 < r')%Q) (classic (0 < s')%Q) =>
       [? | ?] [? | ?]; try tauto);
    [ exists (ζ + -s' * s)%Q, (s' * s)%Q | exists (ζ + -k' * s)%Q, (k' * s)%Q |
      exists (k * s)%Q, (ζ + -k * s)%Q ];
    rewrite /IQS ? Specify_classification ? despecify;
    repeat split; eauto 8 using elts_in_set, Dedekind_cut_2,
      (le_refl ℚ_ring_order : ∀ a, a ≤ a)%Q; try (f_equal; ring).
    + exists r', s.
      repeat split; auto.
      move: H11 => /(add_le_l ℚ_ring_order) /= /(_ (-s' * s)%Q).
      rewrite -[(ordered_rings.le ℚ_ring_order)]/(rationals.le) => H11.
      ring_simplify in H11; ring_simplify.
      by have ->: (ζ - s' * s = - s' * s + ζ)%Q by ring.
    + exists (r' + s' + -k')%Q, s.
      have ->: ((r' + s' + -k')*s = (r' + s') * s + -k' * s)%Q by ring.
      (repeat split; auto; last by apply add_le_r);
      rewrite -? [rationals.lt]/(ordered_rings.lt ℚ_ring_order)
              -? (ordered_rings.lt_shift ℚ_ring_order) //.
      eapply (Dedekind_cut_2 _ r'), (lt_shift ℚ_ring_order); auto => /=.
      have ->: (r' + -(r' + s' + -k') = k' + -s')%Q by ring.
      eapply (lt_shift ℚ_ring_order s'), (le_lt_trans ℚ_ring_order); eauto.
      by apply le_not_gt.
    + exists (r' + s' + -k)%Q, s.
      have ->: ((r' + s' + -k) * s = (r' + s') * s + -k * s)%Q by ring.
      (repeat split; auto; last by apply add_le_r);
      rewrite -? [rationals.lt]/(ordered_rings.lt ℚ_ring_order)
              -? (ordered_rings.lt_shift ℚ_ring_order) //.
      eapply (Dedekind_cut_2 _ s'), (lt_shift ℚ_ring_order); auto => /=.
      have ->: (s' + -(r' + s' + -k) = k + -r')%Q by ring.
      eapply (lt_shift ℚ_ring_order r'), (le_lt_trans ℚ_ring_order); eauto.
      by apply le_not_gt.
  - move: H6 H5 => /Specify_classification /[swap] /Specify_classification.
    rewrite ? despecify => [[H5 [a' [c' [H6 [H7 [H8 [H9 H10]]]]]]]]
                             [H11 [b' [c'' [H12 [H13 [H14 [H15 H16]]]]]]].
    exists (a' + b')%Q, (ordered_rings.max ℚ_ring_order c' c'').
    rewrite Specify_classification.
    repeat split; eauto using O0, elts_in_set; rewrite /ζ ? H4 ? rationals.D1;
      try by case: (max_eq ℚ_ring_order c' c'') => -> //.
    apply le_cross_add; fold rationals.le; auto;
      eapply (ordered_rings.le_trans ℚ_ring_order); eauto;
      apply mul_le_l; simpl; auto; fold rationals.le;
      [apply max_le_l | apply max_le_r].
Qed.

Definition mul : R → R → R.
Proof.
  move=> a b.
  case: (excluded_middle_informative (0 < a))
          (excluded_middle_informative (0 < b)) => [H | H] [H0 | H0].
  - exact (a·b).
  - exact (If (0 = b) then 0 else (-(a·(-b)))).
  - exact (If (0 = a) then 0 else (-((-a)·b))).
  - case: (excluded_middle_informative (0 = b)) => [H1 | H1].
    + exact 0.
    + exact (If (0 = a) then 0 else ((-a)·(-b))).
Defined.

Infix "*" := mul : R_scope.

Theorem mul_0_r : ∀ a, a * 0 = 0.
Proof.
  rewrite /mul => a.
  (repeat case excluded_middle_informative => // [ | _]) => /lt_irrefl //.
Qed.

Theorem mul_0_l : ∀ a, 0 * a = 0.
Proof.
  rewrite /mul => a.
  (repeat case excluded_middle_informative => //) => [_ | _ _] /lt_irrefl //.
Qed.

Theorem R_mul_pos_pos : ∀ a b, 0 < a → 0 < b → a * b = a · b.
Proof.
  rewrite /mul => a b.
  repeat case excluded_middle_informative => //.
Qed.

Theorem R_mul_pos_neg : ∀ a b, 0 < a → b < 0 → a * b = -(a · -b).
Proof.
  rewrite /mul => a b.
  (repeat case excluded_middle_informative => //) => [/lt_antisym | <-] //.
Qed.

Theorem R_mul_neg_pos : ∀ a b, a < 0 → 0 < b → a * b = -(-a · b).
Proof.
  rewrite /mul => a b.
  (repeat case excluded_middle_informative => //) => [_ /lt_antisym | <-] //.
Qed.

Theorem R_mul_neg_neg : ∀ a b, a < 0 → b < 0 → a * b = (-a · -b).
Proof.
  rewrite /mul => a b.
  (repeat case excluded_middle_informative => //) =>
    [/lt_antisym | <- | _ _ | <- | _ | <- | <- ] // /lt_antisym //.
Qed.

Theorem lt_shift : ∀ a b, a < b ↔ 0 < b + -a.
Proof.
  (split => [/(O1 (-a)) | /(O1 a)]);
  rewrite -? (A1 a) ? A4 ? (A1 b) ? A3 ? (A1 b) ? A2 ? A4 -? (A1 b) ? A3 //.
Qed.

Theorem lt_neg_0 : ∀ a, a < 0 ↔ 0 < -a.
Proof.
  move=> a.
  by rewrite lt_shift A1 A3.
Qed.

Theorem neg_lt_0 : ∀ a, -a < 0 ↔ 0 < a.
Proof.
  move=> a.
  by rewrite lt_shift -{2}(A4 a) -A2 A4 A3.
Qed.

Theorem neg_neg : ∀ a, - - a = a.
Proof.
  move=> a.
  by rewrite -{2}(A3 a) -(A4 (-a)) A2 A4 A1 A3.
Qed.

Theorem M1 : ∀ a b, a * b = b * a.
Proof.
  intros a b.
  destruct (T 0 a) as [[H [H0 H1]] | [[H [H0 H1]] | [H [H0 H1]]]], (T 0 b)
      as [[H2 [H3 H4]] | [[H2 [H3 H4]] | [H2 [H3 H4]]]]; unfold mul;
    repeat destruct excluded_middle_informative; try tauto; subst;
      rewrite -> lt_neg_0 in *; now rewrite -> M1_pos.
Qed.

Theorem M2 : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  intros a b c.
  destruct (T 0 a) as [[H [H0 H1]] | [[H [H0 H1]] | [H [H0 H1]]]], (T 0 b)
      as [[H2 [H3 H4]] | [[H2 [H3 H4]] | [H2 [H3 H4]]]], (T 0 c)
        as [[H5 [H6 H7]] | [[H5 [H6 H7]] | [H5 [H6 H7]]]]; subst;
    try now rewrite -> ? mul_0_l, ? mul_0_r, ? mul_0_l.
  - rewrite -> ? R_mul_pos_pos, M2_pos, ? R_mul_pos_pos; auto;
      rewrite -> ? R_mul_pos_pos; auto using O2_pos.
  - rewrite -> ? (R_mul_pos_neg _ c), (R_mul_pos_pos a b), (R_mul_pos_neg a),
    neg_neg, M2_pos; auto; try now rewrite -> lt_neg_0 in *.
    + rewrite -> lt_neg_0, neg_neg in *; auto using O2_pos.
    + rewrite -> (R_mul_pos_pos a b); auto using O2_pos.
  - rewrite -> ? (R_mul_pos_neg a), ? (R_mul_neg_pos _ c), ? neg_neg, M2_pos;
      auto; try now rewrite -> lt_neg_0 in *.
    + rewrite -> lt_neg_0, neg_neg in *; auto using O2_pos.
    + rewrite -> R_mul_neg_pos, lt_neg_0, neg_neg in *; auto using O2_pos.
  - rewrite -> ? (R_mul_neg_neg _ c), (R_mul_pos_neg a b), (R_mul_pos_pos a),
    ? neg_neg, M2_pos; auto; try now rewrite -> lt_neg_0 in *.
    + rewrite -> lt_neg_0 in *; auto using O2_pos.
    + rewrite -> R_mul_pos_neg, lt_neg_0, neg_neg in *; auto using O2_pos.
  - rewrite -> ? (R_mul_neg_pos a), (R_mul_pos_pos b), R_mul_neg_pos,
    neg_neg, M2_pos; auto; try now rewrite -> lt_neg_0 in *.
    + rewrite -> lt_neg_0, neg_neg in *; auto using O2_pos.
    + rewrite -> R_mul_pos_pos; auto using O2_pos.
  - rewrite -> (R_mul_pos_neg b c), (R_mul_neg_neg _ c), (R_mul_neg_pos a b),
    (R_mul_neg_neg a), ? neg_neg, M2_pos; auto;
      try now rewrite -> lt_neg_0 in *.
    + rewrite -> lt_neg_0, neg_neg in *; auto using O2_pos.
    + rewrite -> R_mul_neg_pos, lt_neg_0, neg_neg in *; auto using O2_pos.
  - rewrite -> ? (R_mul_neg_neg a), (R_mul_neg_pos b), R_mul_pos_pos,
    ? neg_neg, M2_pos; auto; try now rewrite -> lt_neg_0 in *.
    + rewrite -> lt_neg_0 in *; auto using O2_pos.
    + rewrite -> R_mul_neg_pos, lt_neg_0, neg_neg in *; auto using O2_pos.
  - rewrite -> R_mul_neg_pos, R_mul_neg_neg, R_mul_pos_neg, R_mul_neg_neg,
    M2_pos; auto; try (now rewrite -> lt_neg_0 in * );
        rewrite -> R_mul_neg_neg, lt_neg_0 in *; auto using O2_pos.
Qed.

Theorem M3 : ∀ a, 1 * a = a.
Proof.
  intros a.
  destruct (T 0 a) as [[H [H0 H1]] | [[H [H0 H1]] | [H [H0 H1]]]].
  - rewrite -> R_mul_pos_pos, M3_pos; auto using zero_lt_1.
  - subst.
    now rewrite -> mul_0_r.
  - rewrite -> R_mul_pos_neg, lt_neg_0, M3_pos, neg_neg in *;
      auto using zero_lt_1.
Qed.

Theorem O0 : ∀ a b, 0 < a → 0 < b → 0 < a + b.
Proof.
  intros a b H H0.
  apply (O1 a) in H0.
  rewrite -> A3 in H0.
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
    + rewrite -> R_mul_pos_pos, R_mul_pos_pos, R_mul_neg_pos, lt_neg_0 in *;
        auto.
      replace a with (a+b+-b) at 2.
      rewrite -> (D1_pos (a+b)), <-A2, A4, A3; auto.
      now rewrite <-A2, A4, A3.
    + replace a with (a+b+-b) at 2.
      rewrite <-H5, mul_0_l, (A1 0), A3, R_mul_pos_pos, R_mul_neg_pos, A4 in *;
        auto.
      * now rewrite <-lt_neg_0.
      * now rewrite <-A2, A4, A3.
    + rewrite -> R_mul_neg_pos, R_mul_pos_pos, R_mul_neg_pos; auto.
      replace (-b) with (-(b+a)+a).
      rewrite -> (D1_pos (-(b+a))), (A1 (a·c)), ? neg_add,
      <-A2, (A1 _ (a·c)), A4, A3, A1; auto.
      * now rewrite <-lt_neg_0, A1.
      * now rewrite -> neg_add, <-A2, (A1 _ a), A4, A3.
  - subst.
    now rewrite -> ? mul_0_r, A3.
  - destruct (T 0 (a+b)) as [[H4 [H5 H6]] | [[H4 [H5 H6]] | [H4 [H5 H6]]]].
    + rewrite -> R_mul_pos_neg, R_mul_pos_neg, R_mul_neg_neg,
      lt_neg_0 in *; auto.
      replace a with (a+b+-b) at 2.
      rewrite -> (D1_pos (a+b)), neg_add, <-A2, (A1 _ (-b·-c)), A4, A3; auto.
      now rewrite <-A2, A4, A3.
    + replace a with (a+b+-b) at 2.
      rewrite <-H5, mul_0_l, (A1 0), A3, R_mul_pos_neg, R_mul_neg_neg,
      A1, A4 in *; auto.
      * now rewrite <-lt_neg_0.
      * now rewrite <-A2, A4, A3.
    + rewrite -> R_mul_neg_neg, R_mul_pos_neg, R_mul_neg_neg; auto.
      replace (-b) with (-(b+a)+a).
      rewrite -> (D1_pos (-(b+a))), (A1 (-(a·(-c)))), ? neg_add,
      <-A2, A4, A3, A1; auto.
      * now rewrite <-lt_neg_0, A1.
      * now rewrite <-lt_neg_0.
      * now rewrite -> neg_add, <-A2, (A1 _ a), A4, A3.
Qed.

Theorem D1 : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  intros a b c.
  destruct (T 0 a) as [[H [H0 H1]] | [[H [H0 H1]] | [H [H0 H1]]]], (T 0 b)
      as [[H2 [H3 H4]] | [[H2 [H3 H4]] | [H2 [H3 H4]]]], (T 0 c)
        as [[H5 [H6 H7]] | [[H5 [H6 H7]] | [H5 [H6 H7]]]]; subst;
    try now rewrite -> ? (A1 0), ? A3, ? mul_0_l, ? mul_0_r, ? (A1 0), ? A3.
  - rewrite -> ? R_mul_pos_pos, D1_pos; auto using O0.
  - rewrite -> ? R_mul_pos_neg, D1_pos, neg_add in *; auto using O0.
    now rewrite <-lt_neg_0.
  - auto using D1_opp.
  - auto using D1_opp.
  - rewrite -> A1, (A1 (a*c)).
    auto using D1_opp.
  - rewrite -> A1, (A1 (a*c)).
    auto using D1_opp.
  - rewrite -> ? R_mul_neg_pos, neg_add, D1_pos, neg_add; auto;
      try now rewrite <-lt_neg_0.
    rewrite -> lt_neg_0, neg_add in *.
    auto using O0.
  - rewrite -> ? R_mul_neg_neg, neg_add, D1_pos; auto;
      try now rewrite <-lt_neg_0.
    rewrite -> lt_neg_0, neg_add in *.
    auto using O0.
Qed.

Definition sub a b := a + -b.

Infix "-" := sub : R_scope.

Theorem A3_l : ∀ a, 0 + a = a.
Proof.
  intros a.
  now rewrite -> A1, A3.
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
  - rewrite -> R_mul_pos_pos, M4_pos; auto using inv_lt.
  - subst; contradiction.
  - assert (a < 0) as H0 by (pose proof (T 0 a); tauto).
    rewrite -> R_mul_neg_neg, neg_neg, M4_pos; auto.
    + now rewrite <-lt_neg_0.
    + rewrite -> lt_neg_0, neg_neg.
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
  rewrite -> R_mul_pos_pos; auto using O2_pos.
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
    rewrite -> despecify in *.
    split; auto.
    apply (lt_cross_add ℚ_ring_order); auto.
  - unfold IQR, iqr_set in *; simpl.
    apply Specify_classification in H as [H H0].
    apply Specify_classification.
    rewrite -> (reify H), despecify in *.
    set (ρ := mkSet H : Q) in *.
    split; auto.
    rewrite -> (ordered_rings.lt_shift ℚ_ring_order) in H0; simpl in H0.
    apply lt_dense in H0 as [c [H0 H1]].
    exists (r+-c)%Q, (c+ρ+-r)%Q.
    repeat split; unfold IQS; f_equal; try ring; apply Specify_classification;
      split; auto using elts_in_set; rewrite -> despecify.
    + rewrite -> (ordered_rings.lt_shift ℚ_ring_order); simpl.
      now replace (r+-(r+-c))%Q with c by ring.
    + rewrite -> (ordered_rings.lt_shift ℚ_ring_order) in *; simpl in *.
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
    rewrite -> (reify H1), despecify in *.
    set (ρ := mkSet H1 : Q) in *.
    assert (a ≤ ρ)%Q as [H4 | H4].
    { rewrite -> (le_not_gt ℚ_ring_order); simpl.
      contradict H2.
      apply Specify_classification.
      rewrite -> despecify.
      split; auto. }
    + eauto using rationals.lt_trans.
    + congruence.
  - intros H.
    split.
    + intros z H0.
      unfold IQR in *.
      apply Specify_classification in H0 as [H0 H1].
      apply Specify_classification.
      rewrite -> (reify H0), despecify in *.
      subst.
      eauto using rationals.lt_trans.
    + intros H0.
      assert (a ∈ (IQR a)) as H1.
      { rewrite -> H0.
        unfold IQR.
        apply Specify_classification.
        rewrite -> despecify.
        split; eauto using elts_in_set. }
      unfold IQR in H1.
      apply Specify_classification in H1 as [H1 H2].
      rewrite -> despecify in *.
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
  rewrite -> IQR_lt in H1, H2.
  apply set_proj_injective, Subset_equality_iff.
  split; intros p H3; unfold mul_pos, mul_pos_set, IQR, iqr_set in *;
    repeat destruct excluded_middle_informative; try tauto; simpl in *.
  - move: H3.
    rewrite Specify_classification => [[H3]].
    rewrite (reify H3) despecify => [[r [s [H4 [H5 [H6 [H7 H8]]]]]]].
    apply Specify_classification in H4 as [H4 H9].
    apply Specify_classification in H5 as [H5 H10].
    apply Specify_classification.
    rewrite -> despecify in *.
    split; auto.
    assert (r * s < a * b)%Q as H11 by
          (eapply (lt_cross_mul ℚ_ring_order);
           eauto using (ordered_rings.le_lt_trans ℚ_ring_order)).
    destruct H8 as [H8 | H8].
    + eauto using rationals.lt_trans.
    + congruence.
  - apply Specify_classification in H3 as [H3 H4].
    apply Specify_classification.
    rewrite -> (reify H3), despecify in *.
    set (ξ := mkSet H3 : Q) in *.
    split; auto.
    destruct (rationals.T 0 ξ) as [[H5 _] | [[_ [H5 _]] | [_ [_ H5]]]].
    + assert (1 < a * (b * ξ^-1))%Q.
      { rewrite -> rationals.M2, <-(rationals.inv_l ξ), rationals.M1;
          auto using (lt_neq ℚ_ring_order).
        apply (ordered_rings.O3_r ℚ_ring_order); auto;
          now apply (ordered_fields.inv_lt ℚ_order). }
      apply square_in_interval in H6 as [z [H6 [H7 H8]]].
      exists (a*z^-1)%Q, (b*z^-1)%Q.
      apply (square_ge_1 ℚ_ring_order) in H7; simpl in *;
        repeat split; auto.
      * apply Specify_classification.
        rewrite -> despecify.
        split; unfold IQS; auto using elts_in_set.
        rewrite <-(rationals.M3 a) at 2.
        rewrite -> (rationals.M1 1).
        apply (O3 ℚ_ring_order); auto.
        now apply (inv_lt_1 ℚ_order).
      * apply Specify_classification.
        rewrite -> despecify.
        split; unfold IQS; auto using elts_in_set.
        rewrite <-(rationals.M3 b) at 2.
        rewrite -> (rationals.M1 1).
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
      exists c, d.
      repeat split; auto.
      apply Specify_classification in H7 as [H7 H10].
      apply Specify_classification in H9 as [H9 H12].
      rewrite -> despecify, <-H5 in *.
      left.
      now apply rationals.O2.
    + apply pos_nonempty in l as [c [H6 H7]].
      apply pos_nonempty in l0 as [d [H8 H9]].
      exists c, d.
      repeat split; auto.
      apply Specify_classification in H7 as [H7 H10].
      apply Specify_classification in H9 as [H9 H12].
      rewrite -> despecify in *.
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
  - rewrite -> IQR_mul_pos; auto.
  - apply IQR_eq in H3.
    subst.
    now rewrite -> (rings.mul_0_r ℚ_ring).
  - replace (a*b)%Q with (-(a*-b))%Q by ring.
    rewrite <-IQR_neg, <-IQR_mul_pos, IQR_neg; auto.
    now rewrite <-IQR_neg, <-lt_neg_0.
  - apply IQR_eq in H0.
    subst.
    now rewrite -> (rings.mul_0_l ℚ_ring).
  - apply IQR_eq in H0.
    subst.
    now rewrite -> (rings.mul_0_l ℚ_ring).
  - apply IQR_eq in H0.
    subst.
    now rewrite -> (rings.mul_0_l ℚ_ring).
  - replace (a*b)%Q with (-(-a*b))%Q by ring.
    rewrite <-IQR_neg, <-IQR_mul_pos, IQR_neg; auto.
    now rewrite <-IQR_neg, <-lt_neg_0.
  - apply IQR_eq in H3.
    subst.
    now rewrite -> (rings.mul_0_r ℚ_ring).
  - replace (a*b)%Q with (-a*-b)%Q by ring.
    rewrite <-IQR_mul_pos, ? IQR_neg; auto; now rewrite <-IQR_neg, <-lt_neg_0.
Qed.
