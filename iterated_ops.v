Require Export naturals.

Definition swap {X Y} (a b : X) (f : X → Y) : X → Y.
Proof.
  intros x.
  destruct (excluded_middle_informative (x = a)).
  - exact (f b).
  - destruct (excluded_middle_informative (x = b)).
    + exact (f a).
    + exact (f x).
Defined.

Theorem swap_refl : ∀ {X Y} a (f : X → Y), swap a a f = f.
Proof.
  intros X Y a f.
  extensionality x.
  unfold swap.
  destruct excluded_middle_informative; auto; now subst.
Qed.

Theorem swap_sym : ∀ {X Y} a b (f : X → Y), swap a b f = swap b a f.
Proof.
  intros X Y a b f.
  extensionality x.
  unfold swap.
  destruct excluded_middle_informative; auto; subst.
  destruct excluded_middle_informative; auto; now subst.
Qed.

Section Iterated_op_construction.

  Context {R : Type}.
  Variable op : R → R → R.
  Variable f : N → R.
  Variable start : R.
  Infix "*" := op.
  Hypothesis M2 : ∀ x y z, x * (y * z) = (x * y) * z.

  Definition iterate_with_bounds : N → N → R.
  Proof.
    intros a b.
    destruct (excluded_middle_informative (a ≤ b)).
    - destruct (constructive_indefinite_description l) as [c H].
      exact (iterated_op op (f a) (λ x, f (a + x + 1)%N) c).
    - exact start.
  Defined.

  Theorem iterate_neg : ∀ a b, b < a → iterate_with_bounds a b = start.
  Proof.
    intros a b H.
    unfold iterate_with_bounds.
    destruct excluded_middle_informative; auto.
    now apply lt_not_ge in H.
  Qed.

  Theorem iterate_0 : ∀ a, iterate_with_bounds a a = f a.
  Proof.
    intros a.
    unfold iterate_with_bounds.
    destruct excluded_middle_informative.
    - destruct constructive_indefinite_description.
      rewrite <-(add_0_r a) in e at 2.
      apply naturals.cancellation_add in e.
      subst.
      now rewrite iterated_op_0.
    - exfalso; eauto using le_refl.
  Qed.

  Theorem iterate_succ : ∀ a b,
      a ≤ b → iterate_with_bounds a (S b) = iterate_with_bounds a b * (f (S b)).
  Proof.
    intros a b H.
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

  Theorem iterate_lower : ∀ a c,
      iterate_with_bounds a (S a+c) =
      op (f a) (iterate_with_bounds (S a) (S a+c)).
  Proof.
    intros a c.
    induction c using Induction.
    - rewrite ? add_0_r, iterate_succ, ? iterate_0; auto using le_refl.
    - rewrite ? add_succ_r, ? iterate_succ, IHc, M2; auto.
      + now (exists c).
      + exists (c+1)%N.
        now rewrite add_assoc, (add_comm a), add_1_r, <-add_succ_r, add_comm.
  Qed.

  Theorem iterate_1 : iterate_with_bounds 0 1 = op (f 0%N) (f 1%N).
  Proof.
    unfold naturals.one.
    rewrite iterate_succ, iterate_0; auto using zero_le.
  Qed.

  Theorem iterate_2 : iterate_with_bounds 0 2 = op (op (f 0%N) (f 1%N)) (f 2).
  Proof.
    rewrite iterate_succ, iterate_1; auto using zero_le.
  Qed.

  Theorem iterate_succ_lower_limit : ∀ a b,
      a ≤ S b → start * (f (S b)) = f (S b) →
      iterate_with_bounds a (S b) = iterate_with_bounds a b * (f (S b)).
  Proof.
    intros a b H H0.
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

End Iterated_op_construction.

Theorem iterate_extensionality : ∀ X op f g (start : X) a b,
      (∀ k, a ≤ k ≤ b → f k = g k) →
      iterate_with_bounds op f start a b = iterate_with_bounds op g start a b.
Proof.
  intros X op f g start a b H.
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

Section Iterated_op_theorems.

  Context {X : Type}.
  Variable op : X → X → X.
  Variable s : X.
  Infix "*" := op.
  Hypothesis M1 : ∀ x y, x * y = y * x.
  Hypothesis M2 : ∀ x y z, x * (y * z) = (x * y) * z.

  Theorem iterate_shift : ∀ f a c,
      iterate_with_bounds op f s a (a+c) =
      iterate_with_bounds op (λ n, (f (n+a)%N)) s 0 c.
  Proof.
  intros f a c.
  induction c using Induction.
  - now rewrite add_0_r, ? iterate_0, add_0_l.
  - rewrite add_succ_r, ? iterate_succ, IHc, <-add_succ_r, add_comm;
      auto using zero_le.
    now (exists c).
  Qed.

  Lemma iterate_swap_upper_two : ∀ m f,
    iterate_with_bounds op f s 0 (S (S m)) =
    iterate_with_bounds op (swap (S m) (S (S m)) f) s 0 (S (S m)).
  Proof.
    intros m f.
    rewrite ? iterate_succ, <-M2, (M1 (f (S m))), M2; auto using zero_le.
    do 2 f_equal; unfold swap;
      try (repeat destruct excluded_middle_informative; subst; congruence).
    apply iterate_extensionality.
    intros k [H H0].
    repeat destruct excluded_middle_informative; auto; subst.
    - now apply not_succ_le in H0.
    - contradiction (not_succ_le (S m)).
      eauto using naturals.le_trans, le_succ.
  Qed.

  Lemma iterate_swap_upper_one : ∀ n f i,
      0 ≤ i ≤ n → iterate_with_bounds op (swap i n f) s 0 n =
                  iterate_with_bounds op f s 0 n.
  Proof.
    induction n using Induction; intros f i [H H0].
    { replace i with 0%N by eauto using naturals.le_antisymm.
      now rewrite ? iterate_0, swap_refl. }
    apply le_lt_or_eq in H0 as [H0 | H0]; try now rewrite H0, swap_refl.
    destruct (classic (1 = S n)%N) as [H1 | H1].
    { rewrite <-H1 in *.
      apply squeeze_lower in H; auto.
      subst.
      unfold naturals.one, swap.
      rewrite ? iterate_succ, ? iterate_0; auto using zero_le.
      repeat destruct excluded_middle_informative;
        try now contradiction (PA4 0).
      now rewrite M1. }
    assert (n ≠ 0)%N as H2 by (contradict H1; now apply f_equal).
    apply succ_0 in H2 as [m H2].
    subst.
    symmetry.
    destruct (classic (i = (S m))) as [H2 | H2];
      try now rewrite H2, iterate_swap_upper_two.
    rewrite iterate_swap_upper_two, iterate_succ, <-(IHn _ i), ? iterate_succ,
    <-? M2; repeat split; auto using zero_le, le_refl.
    2: { now apply le_lt_succ. }
    f_equal.
    - apply iterate_extensionality.
      intros k H3.
      unfold swap.
      repeat destruct excluded_middle_informative; subst; try tauto;
        destruct H3.
      + now apply not_succ_le in H4.
      + contradiction (not_succ_le (S m)).
        eauto using le_trans, le_succ.
    - rewrite M1.
      f_equal; unfold swap; repeat destruct excluded_middle_informative;
        subst; try tauto; try now contradiction (neq_succ (S m)).
      now apply lt_irrefl in H0.
  Qed.

  Theorem iterate_swap_0 : ∀ n f i j,
      0 ≤ i ≤ n → 0 ≤ j ≤ n →
      iterate_with_bounds op (swap i j f) s 0 n =
      iterate_with_bounds op f s 0 n.
  Proof.
    induction n using Induction.
    { intros f i j [H H0] [H1 H2].
      rewrite ? iterate_0, (le_antisymm i 0),
      (le_antisymm j 0), swap_refl; auto. }
    intros f i j [H H0] [H1 H2].
    apply le_lt_or_eq in H0 as [H0 | H0];
      apply le_lt_or_eq in H2 as [H2 | H2]; subst.
    - rewrite <-le_lt_succ, ? iterate_succ, ? IHn in *;
        repeat split; auto using zero_le.
      repeat f_equal.
      unfold swap.
      destruct excluded_middle_informative; subst;
        try now apply not_succ_le in H0.
      destruct excluded_middle_informative; subst; auto.
      now apply not_succ_le in H2.
    - rewrite iterate_swap_upper_one; split; auto.
      rewrite le_lt_or_eq; tauto.
    - rewrite swap_sym, iterate_swap_upper_one; split; auto.
      rewrite le_lt_or_eq; tauto.
    - now rewrite swap_refl.
  Qed.

  Theorem iterate_swap : ∀ a b f i j,
      a ≤ i ≤ b → a ≤ j ≤ b →
      iterate_with_bounds op (swap i j f) s a b =
      iterate_with_bounds op f s a b.
  Proof.
    intros a b f i j [H H0] [H1 H2].
    destruct (classic (a ≤ b)) as [[c H3] | H3]; subst.
    2: { unfold iterate_with_bounds.
         destruct excluded_middle_informative; tauto. }
    rewrite ? iterate_shift.
    destruct H as [x H], H1 as [y H1]; subst.
    rewrite ? (add_comm a) in *.
    apply O1_le_iff in H0, H2.
    erewrite <-(iterate_swap_0 _ _ x y); eauto using zero_le.
    apply iterate_extensionality.
    intros k H.
    unfold swap.
    repeat destruct excluded_middle_informative; auto; try congruence;
      [ contradict n | contradict n1 ]; rewrite ? (add_comm _ a) in e;
        now apply naturals.cancellation_add in e.
  Qed.

  Theorem iterate_bijection_0 : ∀ n f g,
      (∀ j, 0 ≤ j ≤ n → exists ! i, 0 ≤ i ≤ n ∧ f i = g j) →
      (∀ i, 0 ≤ i ≤ n → exists ! j, 0 ≤ j ≤ n ∧ f i = g j) →
      iterate_with_bounds op f s 0 n = iterate_with_bounds op g s 0 n.
  Proof.
    induction n using Induction.
    { intros f g H H0.
      rewrite ? iterate_0.
      destruct (H 0%N) as [j [[[H1 H2] H3] H4]]; try split; auto using le_refl.
      now replace 0%N with j at 1 by now apply le_antisymm. }
    intros f g H H0.
    assert (∀ i1 i2 j, 0 ≤ i1 ≤ S n → 0 ≤ i2 ≤ S n → 0 ≤ j ≤ S n →
                       f i1 = g j → f i2 = g j → i1 = i2) as E1.
    { intros i1 i2 j H1 H2 H3 H4 H5.
      destruct (H j) as [k [[[H6 H7] H8] H9]]; auto.
      replace i1 with k; replace i2 with k; try (apply H9; split); auto. }
    assert (∀ i j1 j2, 0 ≤ i ≤ S n → 0 ≤ j1 ≤ S n → 0 ≤ j2 ≤ S n →
                       f i = g j1 → f i = g j2 → j1 = j2) as E2.
    { intros i j1 j2 H1 H2 H3 H4 H5.
      destruct (H0 i) as [k [[[H6 H7] H8] H9]]; auto.
      replace j1 with k; replace j2 with k; try (apply H9, split); auto. }
    destruct (H (S n)) as [k [[H1 H2] H3]]; eauto using le_refl, zero_le.
    destruct (classic (k = S n)) as [H4 | H4]; subst.
    { rewrite ? iterate_succ; auto using zero_le.
      f_equal; auto.
      apply IHn.
      - intros j [H4 H5].
        destruct (H j) as [k [[[H6 H7] H8] H9]]; eauto using le_trans, le_succ.
        exists k.
        repeat split; auto using zero_le.
        + rewrite le_lt_succ.
          apply le_lt_or_eq in H7 as [H7 | H7]; auto.
          subst.
          replace (S n) with j at 1 by eauto using le_trans, le_succ.
          now apply le_lt_succ.
        + intros x' [[H10 H11] H12].
          eauto using le_trans, le_succ.
      - intros i [H4 H5].
        destruct (H0 i) as [k [[[H6 H7] H8] H9]]; eauto using le_trans, le_succ.
        exists k.
        repeat split; auto using zero_le.
        + rewrite le_lt_succ.
          apply le_lt_or_eq in H7 as [H7 | H7]; auto.
          subst.
          replace (S n) with i at 1 by eauto using le_trans, le_succ.
          now apply le_lt_succ.
        + intros x' [[H10 H11] H12].
          eauto using le_trans, le_succ. }
    destruct H1 as [H1 H5].
    apply le_lt_or_eq in H5 as [H5 | H5]; try tauto.
    rewrite <-(iterate_swap _ _ f k (S n)); repeat split;
      eauto using le_refl, zero_le.
    2: { eapply lt_le_trans; eauto using le_refl. }
    rewrite ? iterate_succ; auto using zero_le.
    f_equal.
    2: { unfold swap.
         repeat destruct excluded_middle_informative; subst; tauto. }
    apply IHn.
    - intros j [H6 H7].
      destruct (H j) as [l [[[H8 H9] H10] H11]]; eauto using le_trans, le_succ.
      apply le_lt_or_eq in H9 as [H9 | H9].
      + exists l.
        repeat split; auto using zero_le.
        * now apply le_lt_succ.
        * rewrite <-H10.
          unfold swap.
          repeat destruct excluded_middle_informative; auto; subst;
            try now apply lt_irrefl in H9.
          replace j with (S n) in H7; try now apply not_succ_le in H7.
          eapply (E2 k); repeat split;
            eauto using zero_le, le_refl, le_trans, le_succ.
          eapply lt_le_trans; eauto using le_refl.
        * intros x' [[H12 H13] H14].
          unfold swap in H14.
          repeat destruct excluded_middle_informative; subst.
          2: { now apply not_succ_le in H13. }
          2: { eapply (E1 _ _ j); repeat split;
               eauto using zero_le, le_refl, le_trans, le_succ.
               eapply lt_le_trans; eauto using le_refl. }
          replace l with (S n) in H9; try now contradiction (lt_irrefl (S n)).
          eapply (E1 _ _ j); repeat split;
            eauto using zero_le, le_refl, le_trans, le_succ.
          eapply lt_le_trans; eauto using le_refl.
      + subst.
        exists k.
        repeat split; auto using zero_le.
        * now apply le_lt_succ.
        * unfold swap.
          destruct excluded_middle_informative; tauto.
        * intros x' [[H9 H12] H13].
          unfold swap in H13.
          repeat destruct excluded_middle_informative; subst; auto;
            try now apply not_succ_le in H12.
          contradict n1.
          eapply (E1 _ _ j); repeat split;
            eauto using zero_le, le_refl, le_trans, le_succ.
    - intros i [H6 H7].
      destruct (classic (i = k)) as [H8 | H8]; subst; unfold swap.
      + destruct (H0 (S n)) as [l [[[H8 H9] H10] H11]];
          eauto using zero_le, le_refl.
        exists l.
        repeat split; auto using zero_le.
        * apply le_lt_succ.
          apply le_lt_or_eq in H9 as [H9 | H9]; auto.
          subst.
          contradict H4.
          eapply (E1 _ _ (S n)); repeat split; auto using zero_le, le_refl.
          eapply lt_le_trans; eauto using le_refl.
        * destruct excluded_middle_informative; tauto.
        * intros x' [[H12 H13] H14].
          apply H11.
          repeat split; eauto using le_trans, le_succ.
          repeat destruct excluded_middle_informative; tauto.
      + destruct (H0 i) as [l [[[H9 H10] H11] H12]];
          eauto using le_trans, le_succ.
        exists l.
        repeat split; auto.
        * apply le_lt_succ.
          apply le_lt_or_eq in H10 as [H10 | H10]; auto.
          subst.
          contradict H8.
          eapply (E1 _ _ (S n)); repeat split;
            eauto using zero_le, le_refl, le_trans, le_succ.
          eapply lt_le_trans; eauto using le_refl.
        * repeat destruct excluded_middle_informative; subst; try tauto.
          now apply not_succ_le in H7.
        * intros x' [[H13 H14] H15].
          apply H12.
          repeat split; eauto using le_trans, le_succ.
          repeat destruct excluded_middle_informative; subst; try tauto.
          now apply not_succ_le in H7.
  Qed.

  Theorem iterate_bijection : ∀ a b f g,
      (∀ j, a ≤ j ≤ b → exists ! i, a ≤ i ≤ b ∧ f i = g j) →
      (∀ i, a ≤ i ≤ b → exists ! j, a ≤ j ≤ b ∧ f i = g j) →
      iterate_with_bounds op f s a b = iterate_with_bounds op g s a b.
  Proof.
    intros a b f g H H0.
    destruct (classic (a ≤ b)) as [[c H1] | H1]; subst.
    2: { unfold iterate_with_bounds.
         destruct excluded_middle_informative; tauto. }
    rewrite ? iterate_shift.
    apply iterate_bijection_0.
    - intros j [H1 H2].
      destruct (H (j + a)%N) as [y [[[[z H3] H4] H5] H6]]; subst.
      split.
      + rewrite <-(add_0_l a) at 1.
        auto using O1_le.
      + rewrite (add_comm a).
        auto using O1_le.
      + exists z; rewrite ? (add_comm a) in *.
        repeat split; auto using zero_le.
        * now apply O1_le_iff in H4.
        * intros x' [[H3 H7] H8].
          apply (naturals.cancellation_add a).
          rewrite ? (add_comm a) in *.
          apply H6.
          repeat split; auto using O1_le.
          exists x'.
          now rewrite add_comm.
    - intros i [H1 H2].
      destruct (H0 (i + a)%N) as [y [[[[z H3] H4] H5] H6]]; subst.
      split.
      + rewrite <-(add_0_l a) at 1.
        auto using O1_le.
      + rewrite (add_comm a).
        auto using O1_le.
      + exists z; rewrite ? (add_comm a) in *.
        repeat split; auto using zero_le.
        * now apply O1_le_iff in H4.
        * intros x' [[H3 H7] H8].
          apply (naturals.cancellation_add a).
          rewrite ? (add_comm a) in *.
          apply H6.
          repeat split; auto using O1_le.
          exists x'.
          now rewrite add_comm.
  Qed.

End Iterated_op_theorems.

Definition sum_N f a b := iterate_with_bounds add f 0 a b.
Definition prod_N f a b := iterate_with_bounds mul f 1 a b.

Theorem sum_N_0 : ∀ f a, sum_N f a a = f a.
Proof.
  intros f a.
  unfold sum_N.
  now rewrite iterate_0.
Qed.

Theorem sum_N_neg : ∀ f a b, b < a → sum_N f a b = 0.
Proof.
  intros f a b H.
  unfold sum_N.
  now rewrite iterate_neg.
Qed.

Theorem sum_N_succ : ∀ f a b,
    a ≤ S b → (sum_N f a (S b)) = (sum_N f a b) + (f (S b)).
Proof.
  intros f a b H.
  apply iterate_succ_lower_limit; auto.
  now ring_simplify.
Qed.

Theorem prod_N_0 : ∀ f a, prod_N f a a = f a.
Proof.
  intros f a.
  unfold prod_N.
  now rewrite iterate_0.
Qed.

Theorem prod_N_neg : ∀ f a b, b < a → prod_N f a b = 1.
Proof.
  intros f a b H.
  unfold prod_N.
  now rewrite iterate_neg.
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
  destruct (classic (a ≤ b)) as [[c H] | H]; subst.
  - induction c using Induction.
    + now rewrite add_0_r, ? sum_N_0.
    + rewrite add_succ_r, ? sum_N_succ, IHc; try (now ring_simplify);
        exists (c+1)%N; now rewrite add_1_r, add_succ_r.
  - now rewrite <-lt_not_ge, ? sum_N_neg, add_0_r in *.
Qed.

Theorem sum_N_mul : ∀ f a b c, c * sum_N f a b = sum_N (λ n, c * (f n)) a b.
Proof.
  intros f a b c.
  destruct (classic (a ≤ b)) as [[d H] | H]; subst.
  - induction d using Induction.
    + now rewrite add_0_r, ? sum_N_0.
    + now rewrite add_succ_r, ? sum_N_succ, mul_distr_l, IHd;
        try (exists (d+1)%N; now rewrite add_1_r, add_succ_r).
  - now rewrite <-lt_not_ge, ? sum_N_neg, mul_0_r in *.
Qed.

Theorem prod_dist :
  ∀ f g a b, prod_N (λ n, (f n) * (g n)) a b = prod_N f a b * prod_N g a b.
Proof.
  intros f g a b.
  destruct (classic (a ≤ b)) as [[c H] | H]; subst.
  - induction c using Induction.
    + now rewrite add_0_r, ? prod_N_0.
    + rewrite add_succ_r, ? prod_N_succ, IHc; try (now ring_simplify);
        exists (c+1)%N; now rewrite add_1_r, add_succ_r.
  - now rewrite <-lt_not_ge, ? prod_N_neg, mul_1_r in *.
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
    apply sum_of_0.
  - now rewrite <-lt_not_ge, ? sum_N_neg in *.
Qed.

Theorem prod_of_1 : ∀ d, (prod_N (λ n, 1) 0 d) = 1.
Proof.
  induction d using Induction.
  - apply iterate_0.
  - rewrite prod_N_succ, IHd, mul_1_r; auto using zero_le.
Qed.

Theorem prod_of_1_a_b : ∀ a b, (prod_N (λ n, 1) a b) = 1.
Proof.
  intros a b.
  destruct (classic (a ≤ b)) as [[c H] | H]; subst.
  - unfold prod_N.
    rewrite iterate_shift.
    apply prod_of_1.
  - now rewrite <-lt_not_ge, ? prod_N_neg in *.
Qed.

Theorem prod_N_mul : ∀ f a b c,
    a ≤ b → c^(S (b-a)) * prod_N f a b = prod_N (λ n, c * (f n)) a b.
Proof.
  intros f a b c [d H].
  subst.
  induction d using Induction.
  - now rewrite add_0_r, sub_diag, pow_1_r, ? prod_N_0.
  - rewrite ? (add_comm a), sub_abba, ? pow_succ_r, ? (add_comm _ a),
    add_succ_r, ? prod_N_succ, (add_comm a), <-IHd in *;
      try (exists (d+1); rewrite <-? add_1_r); ring.
Qed.
