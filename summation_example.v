Set Warnings "-ambiguous-paths".
Require Export rationals.

Example Gauss : ∀ n, (2 * (sum ℤ (λ k, k : Z) 1 n) = n * (n + 1))%Z.
Proof.
  intros n.
  induction n using Induction.
  - rewrite sum_neg; simpl rings.zero; replace (0%N : Z) with 0%Z;
      try ring; eauto using naturals.succ_lt.
  - destruct (classic (n = 0%N)) as [H | H];
      try apply succ_0 in H as [c H]; subst.
    + rewrite -> sum_0; replace (S 0 : Z) with 1%Z by auto; ring.
    + rewrite sum_succ; simpl; try apply one_le_succ.
      rewrite -> integers.M1, integers.D1, (integers.M1 _ 2), IHn,
      <-add_1_r, <-(add_1_r (c+1)), <-? INZ_add.
      replace (1%N : Z) with 1%Z by auto.
      ring.
Qed.

Lemma IZQ_sum : ∀ a b f,
    (sum ℚ_ring (compose IZQ f) a b) = IZQ (sum ℤ f a b).
Proof.
  intros a b f.
  destruct (excluded_middle_informative (a ≤ b)%N) as [[c H] | H]; subst.
  - induction c using Induction.
    + now rewrite -> add_0_r, ? sum_0.
    + rewrite -> add_succ_r, ? sum_succ, IHc; simpl;
        try (now rewrite <-IZQ_add); exists (S c); now rewrite add_succ_r.
  - now rewrite <-naturals.lt_not_ge, ? sum_neg in *.
Qed.

Example Gauss_Q : ∀ n, (sum ℚ_ring (λ x, x : Q) 1 n) = n * (n + 1) / 2.
Proof.
  intros n.
  rewrite inv_div; auto using (ordered_rings.zero_ne_2 ℤ_order).
  assert ((2 : Q) ≠ 0).
  { intros H.
    apply IZQ_eq in H.
    auto using (ordered_rings.zero_ne_2 ℤ_order). }
  apply (cancellation_mul_r (integral_domain_from_field ℚ) (2 : Q));
    auto.
  replace (λ x : N, IZQ (INZ x) + 1) with (λ x : N, IZQ (x + 1)%Z).
  - pose proof IZQ_sum as H0.
    unfold compose in *.
    rewrite <-M2, inv_l, (M1 _ 1), M3, M1, H0, IZQ_mul, Gauss; auto.
  - extensionality x.
    now rewrite <-IZQ_add.
Qed.
