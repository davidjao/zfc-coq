Require Export rings.
Set Warnings "-notation-overridden,-uniform-inheritance".

Section Power_series_construction.

  Variable R : ring.

  Delimit Scope Ring_scope with ring.
  Bind Scope Ring_scope with R.
  Open Scope Ring_scope.
  Notation Rset := (set_R R).
  Notation Rring := (rings.R R).
  Infix "+" := (add R) : Ring_scope.
  Infix "*" := (mul R) : Ring_scope.
  Notation "0" := (zero R : Rring) : Ring_scope.
  Notation "1" := (one R : Rring) : Ring_scope.
  Notation "- a" := (neg R a) : Ring_scope.

  Add Ring generic_ring :
    (mk_rt 0 1 (add R) (mul R) (sub R) (neg R) eq (A3 R) (A1 R) (A2 R) (M3 R)
           (M1 R) (M2 R) (D1 R) (sub_is_neg R) (A4 R)).

  Definition power_series_set := {x in P (ω × Rset) | is_function x ω Rset}.

  Definition power_series := elts power_series_set.

  Definition coefficient : power_series → N → Rring.
  Proof.
    intros f n.
    pose proof proj2_sig f as H; simpl in H.
    apply Specify_classification in H as [H H0].
    set (F := mkFunc _ _ _ H0).
    assert (F (proj1_sig n) ∈ Rset) as H1
        by apply function_maps_domain_to_range, proj2_sig.
    exact (exist _ _ H1).
  Defined.

  Definition seriesify : (N → Rring) → power_series.
  Proof.
    intros f.
    pose proof func_hyp (functionify _ _ f) as [H _].
    pose proof func_hyp (functionify _ _ f) as H0.
    rewrite sets.functionify_domain, sets.functionify_range in H, H0.
    rewrite <-Powerset_classification in H.
    assert (graph (functionify ω Rset f) ∈
                  {x in P (ω × Rset) | is_function x ω Rset})
      as H1 by now apply Specify_classification.
    exact (exist _ _ H1).
  Defined.

  Theorem seriesify_coefficient : ∀ f, seriesify (coefficient f) = f.
  Proof.
    intros [f H].
    unfold seriesify.
    destruct func_hyp.
    apply set_proj_injective.
    simpl.
    unfold coefficient.
    destruct Specify_classification, a.
    simpl in *.
    clear s e a i.
    unfold functionify.
    destruct constructive_indefinite_description as [f'].
    simpl in *.
    replace f with
        (graph {| domain := ω; range := Rset; graph := f; func_hyp := i1 |})
      by auto.
    destruct a as [H0 [H1 H2]].
    f_equal.
    apply func_ext; simpl; auto.
    intros x H3.
    assert (x ∈ ω) as H4 by congruence.
    replace x with (proj1_sig (exist _ _ H4 : elts ω)) by auto.
    now rewrite H2.
  Qed.

  Theorem coefficient_seriesify : ∀ f, coefficient (seriesify f) = f.
  Proof.
    intros f.
    apply functional_extensionality.
    intros x.
    unfold seriesify.
    destruct func_hyp, Specify_classification.
    unfold coefficient.
    destruct Specify_classification, a; simpl in *.
    - apply Specify_classification.
      pose proof (func_hyp (functionify ω Rset f)) as H.
      pose proof (func_hyp (functionify ω Rset f)) as [H0 H1].
      now rewrite sets.functionify_domain, sets.functionify_range,
      <-Powerset_classification in *.
    - destruct a0.
      apply set_proj_injective.
      simpl.
      destruct (functionify_construction _ _ (λ x, f x)) as [f' [H1 [H2 H3]]].
      fold Rset in H2.
      rewrite <-H3.
      f_equal.
      apply function_record_injective; simpl; try congruence.
      f_equal.
      apply func_ext; rewrite ? sets.functionify_domain,
                      ? sets.functionify_range; try congruence.
      intros z H4.
      replace z with (proj1_sig (exist _ _ H4 : elts ω)) by auto.
      rewrite H3.
      simpl.
      unfold functionify.
      destruct constructive_indefinite_description as [f''].
      destruct a as [H5 [H6 H7]].
      now rewrite <-H7.
  Qed.

  Theorem power_series_extensionality :
    ∀ f g, (coefficient f = coefficient g) → f = g.
  Proof.
    intros f g H.
    apply set_proj_injective.
    simpl.
    unfold coefficient in H.
    repeat destruct Specify_classification.
    destruct a, a0.
    set (f' := {| func_hyp := i2 |}).
    set (g' := {| func_hyp := i4 |}).
    replace (proj1_sig f) with (graph (mkFunc _ _ _ i2)) by auto.
    replace (proj1_sig g) with (graph (mkFunc _ _ _ i4)) by auto.
    f_equal.
    fold f' g' Rset in H |-*.
    apply func_ext; simpl; auto.
    intros n H0.
    set (η := exist _ _ H0 : N).
    replace n with (proj1_sig η) by auto.
    set (f'' := (λ n : N, exist _ _ (function_maps_domain_to_range
                                       f' (proj1_sig n) (proj2_sig n))
                 : elts Rset)).
    set (g'' := (λ n : N, exist _ _ (function_maps_domain_to_range
                                       g' (proj1_sig n) (proj2_sig n))
                 : elts Rset)).
    fold f'' g'' in H.
    replace (f' (proj1_sig η)) with (proj1_sig (f'' η)) by auto.
    replace (g' (proj1_sig η)) with (proj1_sig (g'' η)) by auto.
    congruence.
  Qed.

  Definition add : power_series → power_series → power_series.
  Proof.
    intros a b.
    exact (seriesify (λ n, add _ (coefficient a n) (coefficient b n))).
  Defined.

  Delimit Scope Series_scope with series.
  Bind Scope Series_scope with power_series.
  Open Scope Series_scope.

  Infix "+" := add : Series_scope.

  Theorem add_comm : ∀ f g, f + g = g + f.
  Proof.
    intros f g.
    unfold add.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    ring.
  Qed.

  Theorem add_assoc : ∀ f g h, add f (add g h) = add (add f g) h.
  Proof.
    intros f g h.
    apply power_series_extensionality.
    unfold add.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    ring.
  Qed.

  Definition ISS (a : power_series) := proj1_sig a.
  Definition IRS a := seriesify (λ n, if (excluded_middle_informative (n = 0%N))
                                      then a else 0%ring).

  Definition zero := IRS 0.
  Definition one := IRS 1.

  Notation "0" := zero : Series_scope.
  Notation "1" := one : Series_scope.
  Coercion ISS : power_series >-> set.
  Coercion IRS : Rring >-> power_series.

  Theorem zero_series_const : 0 = seriesify (λ n, 0%ring).
  Proof.
    apply power_series_extensionality.
    unfold zero, IRS.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    now destruct excluded_middle_informative.
  Qed.

  Theorem add_0_l : ∀ f, 0 + f = f.
  Proof.
    intros f.
    rewrite zero_series_const.
    apply power_series_extensionality.
    unfold add, zero.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    ring.
  Qed.

  Definition neg f := seriesify (λ n, neg _ (coefficient f n)).

  Notation "- f" := (neg f) : Series_scope.

  Theorem add_opp_r : ∀ f, f + -f = 0.
  Proof.
    intros f.
    rewrite zero_series_const.
    apply power_series_extensionality.
    unfold add, neg, zero.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    ring.
  Qed.

  Definition mul : power_series → power_series → power_series.
  Proof.
    intros a b.
    exact
      (seriesify
         (λ n,
          sum R (λ k, mul _ (coefficient a k) (coefficient b (n-k))) 0 n)).
  Defined.

  Lemma mul_comm_coeff :
    ∀ n f g, (sum R (λ k, (f k) * (g (n-k))) 0 n) =
             (sum R (λ k, (g k) * (f (n-k))) 0 n).
  Proof.
    induction n using Induction.
    { intros f g.
      unfold sum.
      now rewrite ? iterate_0, sub_0_l, M1. }
    intros f g.
    rewrite sum_succ; auto using zero_le.
    replace (sum R (λ k : N, f k * g (S n - k)) 0 n)
      with (sum R (λ k : N, f k * g (n - k + 1)%N) 0 n).
    2: { unfold sum.
         replace n with (0+n)%N at 1 2 by ring.
         apply iterate_extensionality.
         intros k [H [c H0]].
         replace (n-k+1)%N with (S n - k); auto.
         rewrite naturals.add_0_l in H0.
         subst.
         now rewrite <-add_1_r, (naturals.add_comm _ 1%N),
         ? (naturals.add_comm k), naturals.add_assoc,
         ? sub_abba, naturals.add_comm. }
    rewrite (IHn f (λ k, g (k + 1)%N)).
    replace (S n) with (S 0+n)%N at 4.
    2: { now rewrite naturals.add_comm, add_1_r. }
    unfold sum at 2.
    rewrite iterate_lower, A1, M1, sub_diag, sub_0_r.
    2: { intros x y z.
         now ring_simplify. }
    f_equal.
    clear IHn.
    revert f g.
    induction n using Induction; intros f g; try tauto.
    { unfold sum.
      now rewrite add_0_r, ? iterate_0, ? sub_diag, add_1_r. }
    rewrite sum_succ; auto using zero_le.
    replace (sum R (λ k : N, g (k + 1)%N * f (S n - k)) 0 n)
      with (sum R (λ k : N, g (k + 1)%N * f (S n - (n - (n - k)))) 0 n).
    - rewrite (IHn (λ k, f (S n - (n - k)))), <-? add_1_r, ? naturals.add_0_l,
      ? (naturals.add_comm 1), ? add_1_r.
      fold (sum R (λ k : N, g k * f (S n - (n - (S n - k)))) 1 (S n))
           (sum R (λ k : N, g k * f (S (S n) - k)) 1 (S (S n))).
      rewrite ? sum_succ, ? sub_diag;
        try (exists n; now rewrite naturals.add_comm, add_1_r).
      2: { exists (n+1)%N.
           now rewrite naturals.add_comm, <-? add_1_r. }
      f_equal.
      rewrite sub_0_r, <-? add_1_r, ? (naturals.add_comm _ 1), ? sub_abba.
      f_equal.
      unfold sum.
      destruct (classic (n = 0%N)) as [H | H].
      { subst.
        unfold iterate_with_bounds.
        destruct excluded_middle_informative; auto.
        exfalso.
        apply le_not_gt in l.
        contradict l.
        now apply succ_lt. }
      apply succ_0 in H as [m H].
      subst.
      rewrite <-add_1_r, (naturals.add_comm m).
      apply iterate_extensionality.
      intros k [[c H] [d H0]].
      subst.
      rewrite <-naturals.add_assoc in H0.
      apply naturals.cancellation_add in H0.
      subst.
      replace (1+(1+(c+d)))%N with (d+1+(1+c))%N by ring.
      replace (1+(c+d))%N with (c+(d+1))%N by ring.
      replace (1+(d+1+(1+c)))%N with ((d+1+1)+(1+c))%N by ring.
      rewrite ? sub_abba.
      replace (d+1+(1+c))%N with ((d+1+1)+c)%N by ring.
      now rewrite ? sub_abba.
    - rewrite <-(naturals.add_0_l n) at 1 2.
      apply iterate_extensionality.
      intros k [[c H] [d H0]].
      rewrite ? naturals.add_0_l in *.
      subst.
      now rewrite <-? add_1_r, ? (naturals.add_comm k), sub_abba,
      (naturals.add_comm d), sub_abba.
  Qed.

  Infix "*" := mul : Series_scope.

  Theorem mul_comm : ∀ f g, f * g = g * f.
  Proof.
    intros f g.
    apply power_series_extensionality.
    unfold mul.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    apply mul_comm_coeff.
  Qed.

  Lemma mul_assoc_coeff : ∀ n a b c,
      sum R (λ k, (a k) *
                  sum R (λ j, (b j) * (c (n - k - j))) 0 (n-k))%ring 0 n =
      sum R (λ k, (sum R (λ j, (a j) *
                               (b (k - j))) 0 k) * (c (n - k)))%ring 0 n.
  Proof.
    intros.
    revert c.
    induction n using Induction; intros c.
    { unfold sum.
      now rewrite ? iterate_0, sub_0_r, iterate_0, sub_0_r, M2. }
    rewrite ? sum_succ, ? sub_diag; auto using zero_le.
    unfold sum at 3.
    rewrite iterate_0, sub_diag.
    destruct (classic (n = 0%N)) as [H | H].
    { subst.
      unfold sum.
      rewrite ? iterate_0, sub_0_r, iterate_succ, iterate_0, ? sub_diag,
      sub_0_r; auto using le_refl.
      ring. }
    apply succ_0 in H as [m H].
    subst.
    replace (sum R (λ k : N, a k * sum R (λ j : N, b j * c (S (S m) - k - j))
                                       0 (S (S m) - k)) 0 (S m))%ring with
        (sum R (λ k : N, a k * sum R (λ j : N, b j * c (S (S m) - k - j))
                                   0 (S ((S m) - k))) 0 (S m))%ring.
    2: { apply iterate_extensionality.
         intros k [H [d H0]].
         f_equal.
         replace (S (S m - k)) with (S (S m) - k); auto.
         now rewrite <-? H0, <-? add_1_r, (naturals.add_comm k), sub_abba,
         (naturals.add_comm _ 1), naturals.add_assoc, sub_abba,
         naturals.add_comm. }
    replace (sum R (λ k : N, a k * sum R (λ j : N, b j * c (S (S m) - k - j))
                                       0 (S ((S m) - k))) 0 (S m))%ring with
        ((sum R (λ k : N, a k * (sum R (λ j : N, b j * c (S (S m) - k - j))
                                     0 ((S m) - k))) 0 (S m))
         + (sum R (λ k : N, a k * b (S ((S m) - k)) * (c 0%N)) 0 (S m)))%ring.
    2: { rewrite <-sum_dist.
         apply iterate_extensionality.
         intros k [H [d H0]].
         rewrite <-M2, <-D1_l.
         f_equal.
         rewrite sum_succ; auto using zero_le.
         replace (S (S m) - k - S (S m - k)) with 0%N; auto.
         now rewrite <-? H0, <-? add_1_r, (naturals.add_comm k), sub_abba,
         (naturals.add_comm _ 1), naturals.add_assoc, sub_abba,
         naturals.add_comm, sub_diag. }
    pose proof (IHn (λ n, (c (n + 1)%N))) as Z.
    simpl in Z.
    replace (sum R (λ k : N, a k * sum R (λ j : N, b j * c (S (S m) - k - j))
                                       0 (S m - k)) 0 (S m))%ring with
        (sum R (λ k : N, (a k * sum R (λ j : N, b j * c (S m - k - j + 1)%N)
                                    0 (S m - k))%ring) 0 (S m)).
    2: { apply iterate_extensionality.
         intros k [H [d H0]].
         f_equal.
         apply iterate_extensionality.
         intros j [H1 [e H2]].
         do 2 f_equal.
         rewrite <-? H0, <-? add_1_r in *.
         rewrite (naturals.add_comm k), sub_abba in H2.
         subst.
         now rewrite <-naturals.add_assoc, ? (naturals.add_comm k), ? sub_abba,
         <-naturals.add_assoc, ? (naturals.add_comm j), ? sub_abba. }
    rewrite Z, <-A2.
    f_equal.
    - apply iterate_extensionality.
      intros k [H [d H0]].
      do 2 f_equal.
      now rewrite <-? H0, <-? add_1_r, <-naturals.add_assoc,
      ? (naturals.add_comm k), ? sub_abba.
    - rewrite D1, M2.
      f_equal.
      rewrite (M1 _ _ (c 0%N)), sum_mul.
      apply iterate_extensionality.
      intros k [H [d H0]].
      rewrite (M1 _ (c 0%N)), <-H0.
      repeat f_equal.
      now rewrite <-? add_1_r, <-naturals.add_assoc,
      ? (naturals.add_comm k), ? sub_abba.
  Qed.

  Theorem mul_assoc : ∀ a b c, a * (b * c) = (a * b) * c.
  Proof.
    intros a b c.
    apply power_series_extensionality.
    unfold mul.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    apply mul_assoc_coeff.
  Qed.

  Theorem mul_distr_l : ∀ a b c, a * (b + c) = a * b + a * c.
  Proof.
    intros a b c.
    unfold mul, add.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    rewrite <-sum_dist.
    apply iterate_extensionality.
    intros k H.
    now ring_simplify.
  Qed.

  Theorem mul_1_r : ∀ f, f * 1 = f.
  Proof.
    intros f.
    unfold mul, one, IRS.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    induction n using Induction.
    { unfold sum.
      rewrite iterate_0.
      destruct excluded_middle_informative.
      - now rewrite M1, M3.
      - contradict n.
        now rewrite sub_0_r. }
    rewrite sum_succ; auto using zero_le.
    destruct excluded_middle_informative.
    2: { contradict n0.
         now rewrite sub_diag. }
    rewrite M1, M3.
    rewrite <-(A3 _ (coefficient f (S n))) at 2.
    f_equal.
    clear IHn e.
    induction n using Induction.
    { unfold sum.
      rewrite iterate_0.
      destruct excluded_middle_informative.
      - rewrite sub_0_r in e.
        now contradiction (PA4 0).
      - now rewrite mul_0_r. }
    rewrite <-IHn at 1.
    rewrite sum_succ; auto using zero_le.
    destruct excluded_middle_informative.
    { rewrite <-add_1_r, naturals.add_comm, sub_abba in e.
      now contradiction (PA4 0). }
    rewrite mul_0_r, A1, A3.
    apply iterate_extensionality.
    intros k H.
    f_equal.
    repeat destruct excluded_middle_informative; auto.
    - apply sub_0_le in e.
      apply sub_ne_0_lt in n1.
      contradiction (lt_irrefl k).
      destruct e as [c H0].
      subst.
      eapply lt_trans; eauto.
      rewrite lt_def.
      exists (c+1)%N.
      split.
      + rewrite add_1_r.
        auto using PA4.
      + rewrite <-? add_1_r.
        ring.
    - destruct H as [H [c H0]].
      subst.
      rewrite <-add_1_r, <-naturals.add_assoc,
      (naturals.add_comm k), sub_abba, add_1_r in e.
      now contradiction (PA4 c).
  Qed.

  Theorem mul_1_l : ∀ f, 1 * f = f.
  Proof.
    intros f.
    now rewrite mul_comm, mul_1_r.
  Qed.

  Theorem mul_distr_r : ∀ a b c, (a + b) * c = a * c + b * c.
  Proof.
    intros a b c.
    now rewrite ? (mul_comm _ c), mul_distr_l.
  Qed.

  Definition power_series_ring :=
    mkRing _ zero one add mul neg add_0_l add_comm add_assoc mul_1_l mul_comm
           mul_assoc mul_distr_r add_opp_r.

  Theorem IRS_eq : ∀ a b, IRS a = IRS b → a = b.
  Proof.
    intros a b H.
    unfold IRS in H.
    set (A := (λ n : N, if excluded_middle_informative
                             (n = 0%N) then a else rings.zero R)).
    set (B := (λ n : N, if excluded_middle_informative
                             (n = 0%N) then b else rings.zero R)).
    assert (A = B).
    - unfold A, B.
      rewrite <-coefficient_seriesify.
      now rewrite <-coefficient_seriesify, H at 1.
    - replace a with (A 0%N); replace b with (B 0%N); try congruence;
        unfold A, B; destruct excluded_middle_informative; tauto.
  Qed.

  Theorem IRS_add : ∀ a b, IRS (a + b)%ring = IRS a + IRS b.
  Proof.
    intros a b.
    unfold IRS, add.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    destruct excluded_middle_informative; auto.
    ring.
  Qed.

  Theorem IRS_neg : ∀ a, IRS (-a)%ring = - IRS a.
  Proof.
    intros a.
    unfold IRS, neg.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    destruct excluded_middle_informative; auto.
    ring.
  Qed.

  Theorem IRS_mul : ∀ a b, IRS (a * b)%ring = IRS a * IRS b.
  Proof.
    intros a b.
    unfold IRS, mul.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    destruct excluded_middle_informative.
    - subst.
      unfold sum.
      rewrite iterate_0.
      repeat destruct excluded_middle_informative; try tauto.
      contradict n.
      now rewrite sub_0_r.
    - assert (0%ring = sum _ (λ k, 0%ring) 0 n).
      { clear n0.
        induction n using Induction.
        - unfold sum.
          now rewrite iterate_0.
        - rewrite sum_succ, <-IHn, A3; auto using zero_le. }
      rewrite H.
      apply iterate_extensionality.
      intros k H0.
      repeat destruct excluded_middle_informative;
        try now rewrite <-? H, ? mul_0_r, ? mul_0_l.
      contradict n0.
      subst.
      now rewrite sub_0_r in e0.
  Qed.

  Definition shift f :=
    seriesify (λ n, if (excluded_middle_informative (n = 0%N))
                    then 0%ring else (coefficient f (n - 1))).

  Definition x := shift 1.

  Theorem mul_x_shift : ∀ f, x * f = shift f.
  Proof.
    intros f.
    unfold x, one, IRS, shift, mul.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality.
    intros n.
    destruct excluded_middle_informative.
    - subst.
      unfold sum.
      rewrite iterate_0, sub_0_l.
      destruct excluded_middle_informative; try tauto.
      now rewrite mul_0_l.
    - assert (∀ z, (sum _ (λ k, if (excluded_middle_informative (k = 1%N))
                                then z else 0%ring) 0 n) = z) as H.
      { intros z.
        induction n using Induction.
        { unfold sum.
          rewrite iterate_0.
          destruct excluded_middle_informative; tauto. }
        destruct (classic (n = 0%N)) as [H | H].
        { subst.
          rewrite sum_succ; auto using zero_le.
          unfold sum.
          rewrite iterate_0.
          repeat destruct excluded_middle_informative;
            try (now contradiction (PA4 0)); ring. }
        apply IHn in H.
        rewrite sum_succ, H; auto using zero_le.
        destruct excluded_middle_informative; try ring.
        apply PA5 in e.
        subst.
        unfold sum in H.
        rewrite iterate_0 in H.
        destruct excluded_middle_informative; subst; try ring.
        contradiction (PA4 0). }
      rewrite <-H.
      apply iterate_extensionality.
      intros k H0.
      repeat destruct excluded_middle_informative; subst; try (now ring_simplify).
      + contradiction (PA4 0).
      + apply sub_0_le in e.
        apply succ_0 in n1 as [m H1].
        subst.
        contradict n2.
        apply le_antisymm; auto.
        exists m.
        now rewrite naturals.add_comm, add_1_r.
      + now rewrite sub_diag in n2.
  Qed.

  Theorem coefficient_add : ∀ n f g,
      coefficient (f + g) n = (coefficient f n + coefficient g n)%ring.
  Proof.
    intros n f g.
    unfold add.
    now rewrite coefficient_seriesify.
  Qed.

  Theorem coefficient_neg :
    ∀ n f, coefficient (-f) n = (- coefficient f n)%ring.
  Proof.
    intros n f.
    unfold neg.
    now rewrite coefficient_seriesify.
  Qed.

  Theorem coefficient_mul :
    ∀ n f g, coefficient (f * g) n =
             sum R (λ k, (coefficient f k * coefficient g (n-k))%ring) 0 n.
  Proof.
    intros n f g.
    unfold mul.
    now rewrite coefficient_seriesify.
  Qed.

  Lemma const_coeff_mul : ∀ (n : N) (c : Rring) f,
      coefficient ((IRS c) * f) n = (c * coefficient f n)%ring.
  Proof.
    intros n c f.
    unfold IRS, mul at 1.
    rewrite coefficient_seriesify.
    assert (∀ r : Rring, sum R (λ k, if (excluded_middle_informative (k = 0%N))
                                 then r else 0%ring) 0 n = r) as H.
    { intros r.
      induction n using Induction.
      - unfold sum.
        rewrite iterate_0.
        now destruct excluded_middle_informative.
      - rewrite sum_succ, IHn; auto using zero_le.
        destruct excluded_middle_informative.
        + now contradiction (PA4 n).
        + ring. }
    rewrite <-H.
    apply iterate_extensionality.
    intros k H0.
    rewrite coefficient_seriesify.
    repeat destruct excluded_middle_informative; try tauto.
    - subst.
      now rewrite sub_0_r.
    - now ring_simplify.
  Qed.

End Power_series_construction.
