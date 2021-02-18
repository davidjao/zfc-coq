Set Warnings "-ambiguous-paths".
Require Export rationals.

Example Gauss : ∀ n, (2 * (sum ℤ (λ k, k : Z) 1 n) = n * (n + 1))%Z.
Proof.
  intros n.
  induction n using Induction; unfold sum.
  - unfold iterate_with_bounds.
    destruct excluded_middle_informative.
    + exfalso.
      rewrite naturals.le_not_gt in l.
      eauto using naturals.lt_succ.
    + now rewrite (mul_0_r ℤ), (mul_0_l ℤ).
  - destruct (classic (n = 0%N)).
    + subst.
      rewrite iterate_0.
      replace (S 0 : Z) with 1%Z by auto.
      ring.
    + apply succ_0 in H as [c H].
      subst.
      rewrite iterate_succ.
      * rewrite (rings.D1_l ℤ).
        unfold sum in IHn.
        simpl in *.
        rewrite IHn, <-add_1_r, <-(add_1_r (c+1)), <-? INZ_add.
        replace (1%N : Z) with 1%Z by auto.
        ring.
      * exists c.
        now rewrite add_comm, add_1_r.
Qed.

Lemma IZQ_sum : ∀ a b f,
    (sum ℚ_ring (compose IZQ f) a b) = IZQ (sum ℤ f a b).
Proof.
  intros a b f.
  unfold sum, iterate_with_bounds, compose.
  destruct excluded_middle_informative; auto.
  destruct constructive_indefinite_description.
  clear e.
  induction x using Induction.
  - now rewrite ? iterated_op_0.
  - now rewrite ? iterated_op_succ, IHx, ? IZQ_add.
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
