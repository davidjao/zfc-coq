Set Warnings "-ambiguous-paths,-type-checker".
Require Export polynomials integers.

Theorem binomial :
  ∀ (n : N) (x : Z), (1 + x)^n = sum ℤ (λ k, binomial n k * x^k) 0 n.
Proof.
  induction n as [ | n IHn] using Induction =>
              [x | x]; first rewrite sum_0 binomial_zero M3 ? pow_0_r //.
  (rewrite /sum -add_1_r add_comm iterate_lower ? (add_comm (S 0));
   auto using A2; erewrite iterate_extensionality =>
     [ | k [H H0]]; try by rewrite -? Pascal's_identity //);
  rewrite -[iterate_with_bounds _ _ _ _ _]/(sum _ _ _ _)
  -[rings.add ℤ]/add -[S 0]/1%N.
  have ->: (λ k : N, (binomial n k + binomial n (k - 1))%N * x ^ k) =
         (λ k : N, (rings.add ℤ (binomial n k * x ^ k)
                      (binomial n (k - 1) * x ^ k)));
    first (extensionality k; rewrite -INZ_add -[rings.add ℤ]/add; ring).
  rewrite add_1_r sum_dist pow_succ_r -[rings.mul ℤ]/mul M1 D1 IHn M3 A2.
  f_equal.
  - rewrite binomial_zero M3 pow_0_r /= sum_succ ? binomial_overflow
      -? [rings.add ℤ]/add; auto using one_le_succ, naturals.succ_lt.
    have ->: 0 * (x ^ S n) = 0 by ring.
    rewrite (A1 _ 0) A3.
    case (classic (n = 0%N)) => [-> | /succ_0 [m] ->].
    + rewrite /sum iterate_0 iterate_neg ? binomial_zero ? pow_0_r
        -? [rings.one ℤ]/one -? [rings.zero ℤ]/zero ? (A1 1) ? A3 ? M3 //;
        apply naturals.succ_lt.
    + rewrite /sum -add_1_r add_comm iterate_lower ? binomial_zero ? pow_0_r
                      ? M3; auto using A2.
  - rewrite -[mul]/(rings.mul ℤ) sum_mul -add_1_r add_comm /sum iterate_shift.
    apply iterate_extensionality => * /=.
    rewrite sub_abba add_1_r pow_succ_r M1 M2 //.
Qed.
