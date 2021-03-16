Set Warnings "-ambiguous-paths".
Require Export rings integers.

Section Integer_powers.

  Variable Ring : rings.ring.
  Notation R := (elts (Rset Ring)).
  Declare Scope Ring_scope.
  Delimit Scope Ring_scope with R.
  Open Scope Ring_scope.
  Bind Scope Ring_scope with R.
  Notation "0" := (rings.zero Ring) : Ring_scope.
  Notation "1" := (rings.one Ring) : Ring_scope.
  Infix "+" := (rings.add Ring) : Ring_scope.
  Infix "-" := (rings.sub Ring) : Ring_scope.
  Infix "*" := (rings.mul Ring) : Ring_scope.
  Infix "**" := (rings.pow Ring) (at level 35) : Ring_scope.
  Notation "- a" := (rings.neg Ring a) : Ring_scope.

  Add Ring generic_ring : (ringify Ring).

  Definition inv : R → R.
  Proof.
    intros a.
    destruct (excluded_middle_informative (rings.unit a)).
    - destruct (constructive_indefinite_description u) as [x H0].
      exact x.
    - exact 0.
  Defined.

  Theorem inv_l : ∀ a, rings.unit a → (inv a) * a = 1.
  Proof.
    intros a H.
    unfold inv.
    destruct excluded_middle_informative; try tauto.
    now destruct constructive_indefinite_description.
  Qed.

  Theorem inv_r : ∀ a, rings.unit a → a * (inv a) = 1.
  Proof.
    intros a H.
    now rewrite rings.M1, inv_l.
  Qed.

  Theorem inv_1 : inv 1 = 1.
  Proof.
    unfold inv.
    destruct excluded_middle_informative.
    - destruct constructive_indefinite_description.
      now rewrite rings.M3_r in e.
    - contradiction n.
      apply one_unit.
  Qed.

  Theorem inv_neg_1 : inv (-(1)) = -(1).
  Proof.
    unfold inv.
    destruct excluded_middle_informative.
    - destruct constructive_indefinite_description.
      apply (f_equal (λ x, x * (-(1)))) in e.
      now rewrite <-rings.M2, rings.mul_neg_neg, ? rings.M3_r, rings.M3 in e.
    - contradict n.
      exists (-(1)).
      now rewrite rings.mul_neg_neg, rings.M3.
  Qed.

  Theorem inv_inv : ∀ a, rings.unit a → inv (inv a) = a.
  Proof.
    intros a H.
    unfold inv.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description; try tauto.
    - apply (f_equal (rings.mul _ x0)) in e.
      now rewrite rings.M2, <-e0, rings.M3, rings.M3_r in e.
    - contradict n.
      exists a.
      now rewrite rings.M1.
  Qed.

  Theorem unit_inv : ∀ a, rings.unit a → rings.unit (inv a).
  Proof.
    intros a H.
    exists a.
    now rewrite inv_r.
  Qed.

  Theorem inv_mul :
    ∀ a b, rings.unit a → rings.unit b → inv (a*b) = inv a * inv b.
  Proof.
    intros a b H H0.
    unfold inv.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description; try tauto.
    - apply eq_sym, (f_equal (rings.mul _ x0)), (f_equal (rings.mul _ x1)) in e.
      now rewrite rings.M1, <-? rings.M2, (rings.M1 _ b), <-e1, rings.M3_r,
      rings.M1, <-rings.M2, (rings.M1 _ a), <-e0, ? rings.M3_r, rings.M1 in e.
    - contradict n.
      now apply unit_closure.
  Qed.

  Theorem inv_unique : ∀ a b, a * b = 1 → b = inv a.
  Proof.
    intros a b H.
    destruct (classic (rings.unit a)).
    - unfold inv.
      destruct excluded_middle_informative; try tauto.
      destruct constructive_indefinite_description.
      apply (f_equal (rings.mul _ b)) in e.
      now rewrite ? (rings.M1 _ b), <-rings.M2, H, rings.M3, rings.M3_r in e.
    - contradiction H0.
      exists b.
      now rewrite rings.M1.
  Qed.

  Definition pow : R → Z → R.
  Proof.
    intros a n.
    destruct (excluded_middle_informative (0 ≤ n)).
    - apply le_def in l.
      destruct (constructive_indefinite_description l) as [c H].
      exact (a**c).
    - destruct (excluded_middle_informative (rings.unit a)).
      + rewrite <-(lt_not_ge ℤ_order), lt_shift, integers.A3, lt_def in n0.
        destruct (constructive_indefinite_description n0) as [c H].
        exact ((inv a)**c).
      + exact 0%R.
  Defined.

  Infix "^" := pow : Ring_scope.

  Theorem pow_nonneg : ∀ (a : R) (n : N), a^n = a**n.
  Proof.
    intros a n.
    unfold pow.
    destruct excluded_middle_informative.
    - destruct constructive_indefinite_description.
      rewrite integers.A3 in e.
      apply INZ_eq in e.
      congruence.
    - contradict n0.
      apply INZ_le, zero_le.
  Qed.

  Theorem pow_0_r : ∀ a, a^0 = 1.
  Proof.
    intros a.
    unfold integers.zero.
    now rewrite pow_nonneg, pow_0_r.
  Qed.

  Theorem pow_0_l : ∀ a : Z, a ≠ 0%Z → 0^a = 0.
  Proof.
    intros a H.
    destruct (classic (0 ≤ a)) as [[H0 | H0] | H0]; try now subst.
    - apply lt_def in H0 as [c [H0 H1]].
      unfold integers.zero, not in H0.
      rewrite INZ_eq in H0.
      apply neq_sym, succ_0 in H0 as [m H0].
      subst.
      rewrite integers.A3, pow_nonneg, pow_0_l; auto using neq_sym, PA4.
    - unfold pow.
      repeat destruct excluded_middle_informative; try tauto.
      apply zero_ring_degeneracy.
      destruct u as [x H1].
      now rewrite mul_0_r in H1.
  Qed.

  Theorem pow_1_r : ∀ a, a^1 = a.
  Proof.
    intros a.
    unfold integers.one.
    now rewrite pow_nonneg, pow_1_r.
  Qed.

  Theorem pow_1_l : ∀ a, 1^a = 1.
  Proof.
    intros a.
    unfold pow.
    destruct excluded_middle_informative; auto;
      repeat destruct constructive_indefinite_description;
      try destruct a0.
    - now rewrite pow_1_l.
    - destruct excluded_middle_informative.
      + now rewrite inv_1, pow_1_l.
      + contradict n0.
        apply one_unit.
  Qed.

  Theorem pow_neg : ∀ a b, rings.unit a → a^(-b) = (inv a)^b.
  Proof.
    intros a b H.
    unfold pow.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description;
      repeat destruct a0; repeat destruct a1; rewrite ? integers.A3 in *;
        subst; auto; simpl in *; try tauto.
    - rewrite <-(le_neg_0 ℤ_order) in l.
      replace x0 with 0%N in *; fold integers.zero in e.
      + rewrite <-(neg_0 ℤ : 0 = -0)%Z in e.
        apply INZ_eq in e.
        now rewrite <-e, ? rings.pow_0_r.
      + apply INZ_eq, (le_antisymm ℤ_order); auto.
    - rewrite inv_inv; auto.
      f_equal.
      apply INZ_eq.
      congruence.
    - contradict n0.
      now apply unit_inv.
    - rewrite (neg_neg ℤ) in H1.
      apply INZ_eq in H1.
      congruence.
    - apply lt_not_ge in n, n0.
      apply neg_lt_0 in n.
      contradiction (lt_antisym ℤ_order 0%Z b).
    - apply lt_not_ge in n, n0.
      apply neg_lt_0 in n.
      contradiction (lt_antisym ℤ_order 0%Z b).
  Qed.

  Theorem inv_pow : ∀ a, rings.unit a → a^(-(1)) = inv a.
  Proof.
    intros a H.
    now rewrite pow_neg, pow_1_r.
  Qed.

  Lemma pow_add_r_pos_pos :
    ∀ a b c, (0 ≤ b)%Z → (0 ≤ c)%Z → a^(b+c) = a^b * a^c.
  Proof.
    intros a b c H H0.
    apply le_def in H as [x H], H0 as [y H0].
    now rewrite integers.A3, H, H0, INZ_add, ? pow_nonneg, pow_add_r in *.
  Qed.

  Theorem unit_pow : ∀ a b, rings.unit a → rings.unit (a^b).
  Proof.
    intros a b H.
    unfold pow.
    destruct excluded_middle_informative, constructive_indefinite_description.
    - apply unit_prod_closure; auto.
    - destruct excluded_middle_informative; try tauto.
      apply unit_prod_closure; auto using unit_inv.
  Qed.

  Theorem pow_mul_l :
    ∀ a b c, rings.unit a → rings.unit b → (a*b)^c = a^c * b^c.
  Proof.
    intros a b c H H0.
    destruct (classic (0 ≤ c)) as [H1 | H1].
    - apply le_def in H1 as [m H1].
      rewrite integers.A3 in H1.
      subst.
      now rewrite ? pow_nonneg, pow_mul_l.
    - apply lt_not_ge, lt_shift in H1; simpl in H1.
      rewrite integers.A3 in H1.
      apply lt_def in H1 as [m [H1 H2]].
      rewrite <-(neg_neg ℤ c); simpl.
      rewrite H2, integers.A3, ? pow_neg, ? pow_nonneg, inv_mul, pow_mul_l;
        auto using unit_closure, unit_inv.
  Qed.

  Theorem neg_pow : ∀ a b, rings.unit a → a^(-b) = inv (a^b).
  Proof.
    intros a b H.
    destruct (classic (b = 0%Z)); try subst.
    - replace (-0)%Z with 0%Z by ring.
      now rewrite pow_0_r, inv_1.
    - apply inv_unique.
      rewrite pow_neg, <-pow_mul_l, inv_r, pow_1_l; auto using unit_inv.
  Qed.

  Theorem pow_mul_r_pos : ∀ a b c, rings.unit a → (0 ≤ c)%Z → a^(b*c) = (a^b)^c.
  Proof.
    intros a b c H H0.
    unfold pow at 2.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description; try destruct a0;
        try tauto; try rewrite integers.A3 in *; simpl in *; subst;
          try (contradict n; now left).
    destruct (classic (0 ≤ b)) as [H1 | H1].
    - apply le_def in H1 as [d H1].
      rewrite integers.A3 in *.
      subst.
      now rewrite INZ_mul, ? pow_nonneg, pow_mul_r.
    - replace b with (--b)%Z by ring.
      replace (--b*x)%Z with (-((-b)*x))%Z by ring.
      apply lt_not_ge, lt_neg_0, lt_def in H1 as [c [H1 H2]]; simpl in *.
      rewrite integers.A3 in *.
      rewrite H2, ? pow_neg, INZ_mul, ? pow_nonneg, pow_mul_r; auto.
  Qed.

  Theorem pow_mul_r : ∀ a b c, rings.unit a → a^(b*c) = (a^b)^c.
  Proof.
    intros a b c H.
    destruct (classic (0 ≤ c)) as [H0 | H0].
    - now rewrite pow_mul_r_pos.
    - replace c with (--c)%Z by ring.
      replace (b*--c)%Z with (-(b*(-c)))%Z by ring.
      apply lt_not_ge, lt_neg_0, lt_def in H0 as [d [H0 H1]]; simpl in *.
      rewrite integers.A3 in *.
      rewrite H1, pow_neg, pow_mul_r_pos, pow_neg, <-neg_pow, pow_neg;
        auto using unit_inv, unit_pow.
      apply INZ_le, zero_le.
  Qed.

  Theorem pow_div_distr : ∀ a b c,
      rings.unit a → rings.unit b → (a*(inv b))^c = a^c * inv (b^c).
  Proof.
    intros a b c H H0.
    rewrite pow_mul_l, <-neg_pow, pow_neg; auto using unit_inv.
  Qed.

  Lemma pow_add_r_opp : ∀ a b, rings.unit a → a^b * a^(-b) = 1.
  Proof.
    intros a b H.
    rewrite pow_neg, <-pow_mul_l, inv_r, pow_1_l; auto using unit_pow, unit_inv.
  Qed.

  Lemma pow_add_r_pos_neg :
    ∀ a b c, rings.unit a → (0 ≤ b)%Z → (c ≤ 0)%Z → a^(b+c) = a^b * a^c.
  Proof.
    intros a b c H H0 H1.
    rewrite <-(rings.M3 _ (a^(b+c))), <-(pow_add_r_opp a c), <-rings.M2,
    rings.M1; auto; f_equal.
    apply (le_neg_0 ℤ_order) in H1; simpl in *.
    apply le_def in H0 as [x H0], H1 as [y H1].
    rewrite integers.A3, H0, H1, ? pow_nonneg, <-H0 in *.
    destruct (classic (0 ≤ b+c)) as [H2 | H2].
    - apply le_def in H2 as [z H2].
      rewrite integers.A3, H2, ? pow_nonneg, <-pow_add_r in *.
      apply f_equal, INZ_eq.
      rewrite <-INZ_add, <-H1, <-H2, H0; ring.
    - apply lt_not_ge, lt_neg_0 in H2; simpl in *.
      replace (b+c)%Z with (-(-(b+c)))%Z by ring.
      apply lt_def in H2 as [z [H2 H3]].
      rewrite integers.A3, H3, pow_neg in *; auto.
      rewrite <-(M3_r _ (a**x)), <-(pow_1_l z), <-(inv_r a), pow_div_distr,
      rings.M2; auto; f_equal.
      2: { now rewrite <-pow_neg, neg_pow. }
      rewrite pow_nonneg, <-pow_add_r.
      apply f_equal, INZ_eq.
      rewrite <-INZ_add, <-H0, <-H1, <-H3; ring.
  Qed.

  Theorem pow_add_r : ∀ a b c, rings.unit a → a^(b+c) = a^b * a^c.
  Proof.
    intros a b c H.
    destruct (classic (0 ≤ b)) as [H0 | H0], (classic (0 ≤ c)) as [H1 | H1].
    - auto using pow_add_r_pos_pos.
    - apply pow_add_r_pos_neg; auto.
      apply le_not_gt.
      contradict H1.
      now left.
    - rewrite integers.A1, rings.M1.
      apply pow_add_r_pos_neg; auto.
      apply le_not_gt.
      contradict H0.
      now left.
    - replace b with (--b)%Z; replace c with (--c)%Z;
        replace (--b+--c)%Z with (-(-b+-c))%Z; try ring.
      rewrite ? (pow_neg a); auto.
      apply pow_add_r_pos_pos; apply le_neg_0, le_not_gt.
      + contradict H0; now left.
      + contradict H1; now left.
  Qed.

End Integer_powers.
