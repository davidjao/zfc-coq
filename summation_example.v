Set Warnings "-ambiguous-paths".
Require Export ssreflect ssrbool ssrfun rationals.

Example Gauss : ∀ n, (2 * (sum ℤ (λ k, k : Z) 1 n) = n * (n + 1))%Z.
Proof.
  induction n using Induction; rewrite ? sum_succ; auto using one_le_succ.
  - rewrite sum_neg -? [rings.zero ℤ]/0%Z -? [0%N : Z]/0%Z;
      eauto using naturals.succ_lt; ring.
  - rewrite -add_1_r integers.M1 integers.D1 -(integers.M1 2) IHn -? INZ_add
            -[1%N : Z]/1%Z; ring.
Qed.

Lemma IZQ_sum : ∀ (a b : N) (f : N → Z),
    sum ℚ (λ x, f x : Q) a b = ((sum ℤ f a b : Z) : Q).
Proof.
  move=> a b f; case: (classic (a ≤ b)%N) =>
        [[c <-] | /naturals.lt_not_ge H]; last rewrite ? sum_neg //.
  induction c using Induction.
  - rewrite add_0_r ? sum_0 //.
  - rewrite add_succ_r ? sum_succ ? IHc -? IZQ_add // -add_succ_r;
      by exists (S c).
Qed.

Example Gauss_Q : ∀ n, (sum ℚ (λ x, x : Q) 1 n) = n * (n + 1) / 2.
Proof.
  move: (ordered_rings.zero_ne_2 ℤ_order) => /= /[dup] H /[swap] n.
  rewrite inv_div // -IZQ_eq => {}H.
  apply (cancellation_mul_r (integral_domain_from_field ℚ) (2 : Q)) => //=.
  by rewrite -M2 inv_l // -(M1 1) M3 M1 IZQ_sum IZQ_mul Gauss.
Qed.
