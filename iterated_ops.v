Require Export naturals.

Section Iterated_op.
  Variable R : Type.

  Definition iterate_with_bounds : (R → R → R) → (N → R) → R → N → N → R.
  Proof.
    intros op f start a b.
    destruct (excluded_middle_informative (a ≤ b)).
    - destruct (constructive_indefinite_description _ l) as [c H].
      exact (iterated_op R op (f a) (λ x, f (a + x + 1)%N) c).
    - exact start.
  Defined.

  Theorem iterate_0 : ∀ op f start a, iterate_with_bounds op f start a a = f a.
  Proof.
    intros op f start a.
    unfold iterate_with_bounds.
    destruct excluded_middle_informative.
    - destruct constructive_indefinite_description.
      rewrite <-(add_0_r a) in e at 2.
      apply naturals.cancellation_add in e.
      subst.
      now rewrite iterated_op_0.
    - exfalso; eauto using le_refl.
  Qed.

  Theorem iterate_succ : ∀ op f start a b,
      a ≤ b → iterate_with_bounds op f start a (S b)
              = op (iterate_with_bounds op f start a b) (f (S b)).
  Proof.
    intros op f start a b H.
    unfold iterate_with_bounds.
    destruct excluded_middle_informative.
    - destruct constructive_indefinite_description as [x].
      destruct excluded_middle_informative; try tauto.
      destruct constructive_indefinite_description as [c].
      replace x with (S c).
      + now rewrite iterated_op_succ, e0, add_1_r.
      + apply (naturals.cancellation_add a).
        now rewrite add_succ_r, e0, e.
    - contradict n.
      eauto using le_trans, le_succ.
  Qed.

  Theorem iterate_extensionality : ∀ op f g start a b,
      (∀ k, a ≤ k ≤ b → f k = g k) →
      iterate_with_bounds op f start a b =
      iterate_with_bounds op g start a b.
  Proof.
    intros op f g start a b H.
    destruct (classic (a ≤ b)) as [[c H0] | H0].
    2: { unfold iterate_with_bounds.
         destruct excluded_middle_informative; tauto. }
    subst.
    induction c using Induction.
    - rewrite add_0_r, ? iterate_0 in *.
      eauto using le_refl.
    - rewrite add_succ_r, ? iterate_succ; try now (exists c).
      rewrite IHc, H; auto.
      + split.
        * exists (S c).
          now rewrite add_succ_r.
        * exists 0%N.
          now rewrite add_0_r, add_succ_r.
      + intros k [H0 [d H1]].
        rewrite H; auto.
        split; auto.
        exists (S d).
        now rewrite ? add_succ_r, H1.
  Qed.

  Theorem iterate_lower : ∀ op f start a c,
      (∀ x y z, op x (op y z) = op (op x y) z) →
      iterate_with_bounds op f start a (S a+c) =
      op (f a) (iterate_with_bounds op f start (S a) (S a+c)).
  Proof.
    intros op f start a c H.
    induction c using Induction.
    - rewrite ? add_0_r, iterate_succ, ? iterate_0; auto using le_refl.
    - rewrite ? add_succ_r, ? iterate_succ, IHc, H; auto.
      + now (exists c).
      + exists (c+1)%N.
        now rewrite add_assoc, (add_comm a), add_1_r, <-add_succ_r, add_comm.
  Qed.

  Theorem iterate_shift : ∀ op f start a c,
      iterate_with_bounds op f start a (a+c) =
      iterate_with_bounds op (λ n, (f (n+a)%N)) start 0 c.
  Proof.
    intros op f start a c.
    induction c using Induction.
    - now rewrite add_0_r, ? iterate_0, add_0_l.
    - rewrite add_succ_r, ? iterate_succ, IHc, <-add_succ_r, add_comm;
        auto using zero_le.
      now (exists c).
  Qed.

  Theorem iterate_1 : ∀ op f start,
      iterate_with_bounds op f start 0 1 = op (f 0%N) (f 1%N).
  Proof.
    intros op f start.
    unfold naturals.one.
    rewrite iterate_succ, iterate_0; auto using zero_le.
  Qed.

  Theorem iterate_2 : ∀ op f start,
      iterate_with_bounds op f start 0 2 = op (op (f 0%N) (f 1%N)) (f 2).
  Proof.
    intros op f start.
    rewrite iterate_succ, iterate_1; auto using zero_le.
  Qed.

  Theorem iterate_succ_lower_limit : ∀ op f start a b,
      a ≤ S b → op start (f (S b)) = f (S b) →
      iterate_with_bounds op f start a (S b) =
      op (iterate_with_bounds op f start a b) (f (S b)).
  Proof.
    intros op f start a b H H0.
    destruct (classic (a ≤ b)) as [H1 | H1]; auto using iterate_succ.
    replace a with (S b) in *.
    - rewrite iterate_0.
      unfold iterate_with_bounds.
      destruct excluded_middle_informative; congruence.
    - eapply le_antisymm; eauto.
      apply le_not_gt.
      contradict H1.
      now apply le_lt_succ.
  Qed.

End Iterated_op.

Definition sum_N f a b := iterate_with_bounds _ add f 0 a b.
Definition prod_N f a b := iterate_with_bounds _ mul f 1 a b.

Theorem sum_N_succ : ∀ f a b,
    a ≤ S b → (sum_N f a (S b)) = (sum_N f a b) + (f (S b)).
Proof.
  intros f a b H.
  apply iterate_succ_lower_limit; auto.
  now ring_simplify.
Qed.

Theorem prod_N_succ : ∀ f a b,
    a ≤ S b → (prod_N f a (S b)) = (prod_N f a b) * (f (S b)).
Proof.
  intros f a b H.
  apply iterate_succ_lower_limit; auto.
  now ring_simplify.
Qed.

Theorem sum_N_dist :
  ∀ f g a b, sum_N (λ n, (f n) + (g n)) a b = sum_N f a b + sum_N g a b.
Proof.
  intros f g a b.
  destruct (classic (a ≤ b)) as [[c H] | H].
  2: { unfold sum_N, iterate_with_bounds.
       repeat destruct excluded_middle_informative; try tauto; ring. }
  subst.
  induction c using Induction.
  - rewrite add_0_r.
    unfold sum_N.
    now rewrite ? iterate_0.
  - rewrite add_succ_r, ? sum_N_succ, IHc; try (now ring_simplify);
      exists (c+1)%N; now rewrite add_1_r, add_succ_r.
Qed.

Theorem sum_N_mul : ∀ f a b c, c * sum_N f a b = sum_N (λ n, c * (f n)) a b.
Proof.
  intros f a b c.
  destruct (classic (a ≤ b)) as [[d H] | H].
  2: { unfold sum_N, iterate_with_bounds.
       repeat destruct excluded_middle_informative; try tauto; ring. }
  subst.
  induction d using Induction.
  - rewrite add_0_r.
    unfold sum_N.
    now rewrite ? iterate_0.
  - now rewrite add_succ_r, ? sum_N_succ, mul_distr_l, IHd;
      try (exists (d+1)%N; now rewrite add_1_r, add_succ_r).
Qed.

Theorem prod_dist :
  ∀ f g a b, prod_N (λ n, (f n) * (g n)) a b = prod_N f a b * prod_N g a b.
Proof.
  intros f g a b.
  destruct (classic (a ≤ b)) as [[c H] | H].
  2: { unfold prod_N, iterate_with_bounds.
       repeat destruct excluded_middle_informative; try tauto; ring. }
  subst.
  induction c using Induction.
  - rewrite add_0_r.
    unfold prod_N.
    now rewrite ? iterate_0.
  - rewrite add_succ_r, ? prod_N_succ, IHc; try (now ring_simplify);
      exists (c+1)%N; now rewrite add_1_r, add_succ_r.
Qed.

Theorem sum_of_0 : ∀ d, (sum_N (λ n, 0) 0 d) = 0.
Proof.
  induction d using Induction.
  - apply iterate_0.
  - rewrite sum_N_succ, IHd, add_0_r; auto using zero_le.
Qed.

Theorem sum_of_0_a_b : ∀ a b, (sum_N (λ n, 0) a b) = 0.
Proof.
  intros a b.
  destruct (classic (a ≤ b)) as [[c H] | H]; subst.
  - unfold sum_N.
    rewrite iterate_shift.
    fold (sum_N (λ n, 0) 0 c).
    now rewrite sum_of_0.
  - unfold sum_N, iterate_with_bounds.
    destruct excluded_middle_informative; tauto.
Qed.

Theorem prod_N_mul : ∀ f a b c,
    a ≤ b → c^(S (b-a)) * prod_N f a b = prod_N (λ n, c * (f n)) a b.
Proof.
  intros f a b c [d H].
  subst.
  induction d using Induction.
  - rewrite add_0_r, sub_diag, pow_1_r.
    unfold prod_N.
    now rewrite ? iterate_0.
  - rewrite ? (add_comm a), sub_abba, ? pow_succ_r, ? (add_comm _ a),
    add_succ_r, ? prod_N_succ, (add_comm a), <-IHd in *;
      try (exists (d+1); rewrite <-? add_1_r); ring.
Qed.
