Require Export power_series combinatorics.
Set Warnings "-notation-overridden,-uniform-inheritance".

Section Polynomials_construction.

  Variable R : ring.

  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Delimit Scope Series_scope with series.
  Bind Scope Series_scope with power_series.
  Open Scope R_scope.
  Notation Rring := (rings.R R).
  Infix "+" := (rings.add R) : R_scope.
  Infix "*" := (rings.mul R) : R_scope.
  Notation "- a" := (rings.neg R a) : R_scope.
  Infix "+" := (power_series.add R) : Series_scope.
  Infix "*" := (power_series.mul R) : Series_scope.
  Notation "0" := (rings.zero R) : R_scope.
  Notation "1" := (rings.one R) : R_scope.
  Notation "0" := (power_series.zero R) : Series_scope.
  Notation "1" := (power_series.one R) : Series_scope.
  Notation "- a" := (power_series.neg R a) : Series_scope.

  Add Ring generic_ring :
    (mk_rt 0 1 (rings.add R) (rings.mul R) (rings.sub R) (rings.neg R) eq
           (rings.A3 R) (rings.A1 R) (rings.A2 R) (rings.M3 R) (rings.M1 R)
           (rings.M2 R) (rings.D1 R) (rings.sub_is_neg R) (rings.A4 R)).

  Definition polynomial_set :=
    {f in power_series_set R |
      ∃ f' : power_series R,
       f = f' ∧ ∃ n : N, ∀ m, (n ≤ m)%N → coefficient _ f' m = 0}.

  Theorem polynomials_are_subset : polynomial_set ⊂ set_R (power_series_ring R).
  Proof.
    intros f H.
    apply Specify_classification in H as [H H0].
    exact H.
  Qed.

  Theorem polynomials_are_subring :
    is_subring (power_series_ring R) polynomial_set.
  Proof.
    repeat split.
    - intros [a A] [b B] H H0.
      apply Specify_classification in H as [H [[a' A'] [H1 [n H2]]]].
      apply Specify_classification in H0 as [H0 [[b' B'] [H3 [m H4]]]].
      unfold rings.IRS, ISS in *.
      simpl in *.
      subst.
      replace A with A' by now apply proof_irrelevance.
      replace B with B' by now apply proof_irrelevance.
      set (a := (exist (λ x : set, x ∈ power_series_set R) a' A')).
      set (b := (exist (λ x : set, x ∈ power_series_set R) b' B')).
      fold a b in H2, H4 |-*.
      apply Specify_classification.
      split; try now apply (proj2_sig (a + b)%series).
      exists (a + b)%series.
      split; auto.
      exists (naturals.max m n).
      intros x H1.
      unfold power_series.add.
      rewrite coefficient_seriesify, H2, H4, rings.A3; auto.
      + eapply naturals.le_trans; eauto using naturals.max_le_l.
      + eapply naturals.le_trans; eauto using naturals.max_le_r.
    - intros [a A] [b B] H H0.
      apply Specify_classification in H as [H [[a' A'] [H1 [n H2]]]].
      apply Specify_classification in H0 as [H0 [[b' B'] [H3 [m H4]]]].
      unfold rings.IRS, ISS in *.
      simpl in *.
      subst.
      replace A with A' by now apply proof_irrelevance.
      replace B with B' by now apply proof_irrelevance.
      set (a := (exist (λ x : set, x ∈ power_series_set R) a' A')).
      set (b := (exist (λ x : set, x ∈ power_series_set R) b' B')).
      fold a b in H2, H4 |-*.
      apply Specify_classification.
      split; try now apply (proj2_sig (a * b)%series).
      exists (a * b)%series.
      split; auto.
      exists (n + m)%N.
      intros x H1.
      unfold power_series.mul.
      rewrite coefficient_seriesify, <-(sum_of_0 _ x).
      apply iterate_extensionality.
      intros k H3.
      destruct (classic (n ≤ k)%N).
      + rewrite H2; auto; ring.
      + rewrite H4, mul_0_r; auto.
        apply NNPP.
        intros H6.
        rewrite <-naturals.lt_not_ge in H5, H6.
        eapply naturals.lt_cross_add in H5; eauto.
        rewrite naturals.add_comm, sub_abab, naturals.lt_not_ge,
        naturals.add_comm in H5; intuition.
    - intros [a A] H.
      apply Specify_classification in H as [H [[a' A'] [H0 [n H1]]]].
      unfold rings.IRS, ISS in *.
      simpl in *.
      subst.
      replace A with A' by now apply proof_irrelevance.
      set (a := (exist (λ x : set, x ∈ power_series_set R) a' A')).
      fold a in H1 |-*.
      apply Specify_classification.
      split; try now apply (proj2_sig (-a))%series.
      exists (-a)%series.
      split; auto.
      exists n.
      intros x H0.
      unfold power_series.neg.
      rewrite coefficient_seriesify, H1; auto.
      ring.
    - apply Specify_classification.
      split; try now apply (proj2_sig 1%series).
      exists (1%series).
      split; auto.
      exists 1%N.
      intros m H.
      unfold power_series.one, power_series.IRS.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative; subst; auto.
      apply naturals.le_not_gt in H.
      contradict H.
      apply naturals.succ_lt.
  Qed.

  Definition polynomial_ring :=
    subring _ polynomial_set polynomials_are_subset polynomials_are_subring.

  Notation poly := (rings.R polynomial_ring).

  Delimit Scope Poly_scope with poly.
  Bind Scope Poly_scope with poly.
  Open Scope Poly_scope.

  Infix "+" := (rings.add polynomial_ring) : Poly_scope.
  Infix "*" := (rings.mul polynomial_ring) : Poly_scope.
  Infix "-" := (rings.sub polynomial_ring) : Poly_scope.
  Notation "0" := (rings.zero polynomial_ring) : Poly_scope.
  Notation "1" := (rings.one polynomial_ring) : Poly_scope.
  Notation "- f" := (rings.neg polynomial_ring f) : Poly_scope.

  Theorem consts_are_polys :
    ∀ c : Rring, (power_series.IRS _ c) ∈ polynomial_set.
  Proof.
    intros c.
    apply Specify_classification.
    split; try now apply (proj2_sig (power_series.IRS _ c)).
    exists (power_series.IRS _ c).
    split; auto.
    exists 1%N.
    intros m H.
    unfold power_series.IRS, ISS.
    rewrite coefficient_seriesify.
    destruct excluded_middle_informative; auto.
    subst.
    apply naturals.le_not_gt in H.
    contradict H.
    apply naturals.succ_lt.
  Qed.

  Notation PS := (power_series R).

  Theorem x_is_poly : x R ∈ polynomial_set.
  Proof.
    apply Specify_classification.
    split; try apply (proj2_sig (x R)).
    exists (x R).
    split; auto.
    exists 2%N.
    intros m [c H].
    unfold x, shift, power_series.one, power_series.IRS.
    rewrite ? coefficient_seriesify.
    repeat destruct excluded_middle_informative; auto.
    apply sub_0_le in e as [d H0].
    subst.
    rewrite <-add_1_r, <-? naturals.add_assoc in H0.
    rewrite <-(add_0_r 1) in H0 at 3.
    apply naturals.cancellation_add in H0.
    rewrite naturals.add_comm, add_1_r in H0.
    now contradiction (PA4 (c+d)).
  Qed.

End Polynomials_construction.

Section Polynomial_theorems.

  Variable Ring : ring.
  Definition R := (rings.R Ring).
  Notation SR := (power_series_ring Ring).
  Notation PR := (polynomial_ring Ring).
  Notation series := (rings.R SR).
  Notation poly := (rings.R (polynomial_ring Ring)).
  Definition power_series := (rings.R SR).
  Definition polynomial := (rings.R (polynomial_ring Ring)).
  Add Ring base_ring : (ringify Ring).
  Add Ring series_ring : (ringify (power_series_ring Ring)).
  Add Ring poly_ring : (ringify (polynomial_ring Ring)).
  Definition IPS :=
    ISR (power_series_ring Ring) (polynomial_set Ring)
        (polynomials_are_subset Ring) : polynomial → power_series.
  Definition IRS := (power_series.IRS Ring) : R → power_series.
  Coercion IPS : polynomial >-> power_series.

  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Delimit Scope Series_scope with series.
  Bind Scope Series_scope with power_series.
  Delimit Scope Poly_scope with poly.
  Bind Scope Poly_scope with polynomial.

  Open Scope R_scope.
  Infix "+" := (rings.add Ring) : R_scope.
  Infix "*" := (rings.mul Ring) : R_scope.
  Infix "-" := (rings.sub Ring) : R_scope.
  Notation "- a" := (rings.neg Ring a) : R_scope.
  Infix "^" := (rings.pow Ring) : R_scope.
  Notation "0" := (rings.zero Ring) : R_scope.
  Notation "1" := (rings.one Ring) : R_scope.

  Open Scope Series_scope.
  Infix "+" := (rings.add SR) : Series_scope.
  Infix "*" := (rings.mul SR) : Series_scope.
  Infix "-" := (rings.sub SR) : Series_scope.
  Notation "- a" := (rings.neg SR a) : Series_scope.
  Infix "^" := (rings.pow SR) : Series_scope.
  Notation "0" := (rings.zero SR) : Series_scope.
  Notation "1" := (rings.one SR) : Series_scope.

  Open Scope Poly_scope.
  Infix "+" := (rings.add PR) : Poly_scope.
  Infix "*" := (rings.mul PR) : Poly_scope.
  Infix "-" := (rings.sub PR) : Poly_scope.
  Notation "- a" := (rings.neg PR a) : Poly_scope.
  Infix "^" := (rings.pow PR) : Poly_scope.
  Notation "0" := (rings.zero PR) : Poly_scope.
  Notation "1" := (rings.one PR) : Poly_scope.

  Definition IRP (c : R) := (exist _ _ (consts_are_polys _ c)) : polynomial.
  Coercion IRP : R >-> polynomial.

  Definition coefficient (f : polynomial) n :=
    power_series.coefficient _ (f : power_series) n : R.
  Definition x := (exist _ _ (x_is_poly _)) : polynomial.

  Theorem IPS_eq : ∀ f g : polynomial,
      (f : power_series) = (g : power_series) ↔ f = g.
  Proof.
    intros f g.
    split; intros H; try congruence.
    now apply ISR_eq in H.
  Qed.

  Theorem IPS_add : ∀ f g : polynomial,
      ((f + g : polynomial) : power_series) =
      ((f : power_series) + (g : power_series))%series.
  Proof.
    intros f g.
    now apply set_proj_injective.
  Qed.

  Theorem IPS_neg : ∀ f : polynomial,
      ((-f : polynomial) : power_series) = (-(f : power_series))%series.
  Proof.
    intros f.
    now apply set_proj_injective.
  Qed.

  Theorem IPS_mul : ∀ f g : polynomial,
      ((f * g : polynomial) : power_series) =
      ((f : power_series) * (g : power_series))%series.
  Proof.
    intros f g.
    now apply set_proj_injective.
  Qed.

  Theorem IRP_add : ∀ a b : R,
      (a : polynomial) + (b : polynomial) = (((a + b)%R : R) : polynomial).
  Proof.
    intros a b.
    unfold IRP; apply set_proj_injective; simpl.
    rewrite (IRS_add Ring).
    unfold ISR, rings.IRS, ISS.
    simpl.
    do 2 f_equal; now apply set_proj_injective.
  Qed.

  Theorem IRP_mul : ∀ a b : R,
      (a : polynomial) * (b : polynomial) = (((a * b)%R : R) : polynomial).
  Proof.
    intros a b.
    unfold IRP; apply set_proj_injective; simpl.
    rewrite (IRS_mul Ring).
    unfold ISR, rings.IRS, ISS.
    simpl.
    do 2 f_equal; now apply set_proj_injective.
  Qed.

  Theorem IRP_neg : ∀ a : R, -(a : polynomial) = (((-a)%R : R) : polynomial).
  Proof.
    intros a.
    unfold IRP; apply set_proj_injective; simpl.
    rewrite (IRS_neg Ring).
    unfold ISR, rings.IRS, ISS.
    simpl.
    do 2 f_equal; now apply set_proj_injective.
  Qed.

  Theorem nonzero_coefficients :
    ∀ f, f ≠ 0 ↔ ∃ m, coefficient f m ≠ 0%R.
  Proof.
    intros f.
    split; intros H.
    - apply NNPP.
      contradict H.
      apply IPS_eq, power_series_extensionality.
      unfold IPS.
      simpl in *.
      rewrite <-sub_zero_is_zero.
      extensionality n.
      simpl.
      unfold power_series.zero, IRS, power_series.IRS.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative.
      + apply NNPP.
        contradict H.
        exists 0%N.
        now subst.
      + apply NNPP.
        contradict H.
        now (exists n).
    - intros H0.
      subst.
      destruct H as [m H].
      contradict H.
      unfold coefficient, IPS.
      simpl.
      rewrite <-sub_zero_is_zero.
      simpl.
      unfold coefficient, power_series.zero, IRS, power_series.IRS.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative; tauto.
  Qed.

  Theorem degree_construction : ∀ f : polynomial,
      f ≠ 0 → ∃ m, coefficient f m ≠ 0%R ∧
                   ∀ n, (m < n)%N → coefficient f n = 0%R.
  Proof.
    intros [f F] H.
    apply nonzero_coefficients in H as [m H].
    pose proof F as H0.
    apply Specify_classification in H0 as [H0 [f' [H1 [n H2]]]].
    subst.
    set (f := exist _ _ F : poly) in *.
    assert (f' = IPS f) as H3 by now apply set_proj_injective.
    rewrite H3 in *.
    destruct (lub (λ x, coefficient f x ≠ 0%R)) as [s [H1 H4]];
      try now (exists m).
    { exists n.
      intros x H4.
      apply naturals.le_not_gt.
      contradict H4.
      apply H2.
      now destruct H4. }
    exists s.
    split; auto.
    intros x [H5 H6].
    apply NNPP.
    intros H7.
    eauto using naturals.le_antisymm.
  Qed.

  Definition degree : poly → N.
  Proof.
    intros f.
    destruct (excluded_middle_informative (f = 0)).
    - exact 0%N.
    - apply degree_construction in n.
      destruct (constructive_indefinite_description _ n) as [d].
      exact d.
  Defined.

  Theorem degree_spec : ∀ (f : polynomial) m,
      f ≠ 0 → degree f = m ↔ (coefficient f m ≠ 0%R ∧
                              ∀ n, (m < n)%N → coefficient f n = 0%R).
  Proof.
    intros f m H.
    split; intros H0; unfold degree in *;
      destruct excluded_middle_informative; try tauto;
        destruct constructive_indefinite_description as [y]; subst; auto.
    destruct H0 as [H0 H1], a as [H2 H3].
    destruct (lt_trichotomy y m) as [H4 | [H4 | H4]]; auto.
    - now apply H3 in H4.
    - now apply H1 in H4.
  Qed.

  Lemma coeffs_of_x : ∀ n : N, n ≠ 1%N → coefficient x n = 0%R.
  Proof.
    intros n H.
    unfold IPS, x, ISR, ISS.
    simpl in *.
    replace 0%R with (power_series.coefficient _ (power_series.x Ring) n).
    { unfold coefficient.
      f_equal.
      now apply set_proj_injective. }
    unfold power_series.x, shift, power_series.one, IRS, power_series.IRS.
    rewrite ? coefficient_seriesify.
    repeat destruct excluded_middle_informative; auto.
    contradict H.
    apply sub_0_le in e.
    apply naturals.le_antisymm; eauto.
    apply succ_0 in n0 as [c H].
    subst.
    exists c.
    now rewrite <-add_1_r, naturals.add_comm.
  Qed.

  Lemma x_coeff_of_x : coefficient x 1 = 1%R.
  Proof.
    unfold IPS, x, ISR, ISS.
    simpl in *.
    replace 1%R with (power_series.coefficient _ (power_series.x Ring) 1).
    { unfold coefficient.
      f_equal.
      now apply set_proj_injective. }
    unfold power_series.x, shift, power_series.one, IRS, power_series.IRS.
    rewrite ? coefficient_seriesify.
    repeat destruct excluded_middle_informative; auto.
    - now contradiction (PA4 0).
    - contradiction n0.
      now rewrite sub_diag.
  Qed.

  Lemma IPS_pow : ∀ (n : N) (f : polynomial),
      ((f : power_series)^n)%series = ((f^n : polynomial) : power_series).
  Proof.
    intros n f.
    induction n using Induction.
    - rewrite ? (rings.pow_0_r PR), ? (rings.pow_0_r SR).
      apply sub_one_is_one.
    - rewrite ? (pow_succ_r PR), ? (pow_succ_r SR), IPS_mul in *.
      ring [IHn].
  Qed.

  Lemma coeffs_of_x_ne_n : ∀ m n, m ≠ n → coefficient (x^n) m = 0%R.
  Proof.
    intros m n H.
    revert m H.
    induction n using Induction; intros m H; unfold coefficient in *.
    { rewrite rings.pow_0_r.
      unfold IPS; simpl.
      rewrite <-sub_one_is_one.
      simpl.
      unfold power_series.one, IRS, power_series.IRS, coefficient.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative; tauto. }
    rewrite pow_succ_r, IPS_mul, <-IPS_pow in *.
    simpl.
    unfold power_series.mul, coefficient.
    rewrite coefficient_seriesify, <-(sum_of_0 _ m).
    apply iterate_extensionality.
    intros k [H0 [c H1]].
    destruct (classic (n = k)).
    - subst.
      replace (power_series.coefficient _ (x : power_series) (k + c - k))
        with 0%R; try ring.
      symmetry.
      apply coeffs_of_x.
      contradict H.
      rewrite naturals.add_comm, sub_abba in H.
      subst.
      now rewrite add_1_r.
    - rewrite IHn, rings.mul_0_l; auto.
  Qed.

  Lemma degree_bound : ∀ n (f : polynomial),
      (∀ m : N, (n < m)%N → coefficient f m = 0%R) → (degree f ≤ n)%N.
  Proof.
    intros n f H.
    unfold degree.
    destruct excluded_middle_informative; auto using zero_le.
    destruct constructive_indefinite_description as [d [H1 H2]].
    apply naturals.le_not_gt.
    contradict H1.
    auto.
  Qed.

  Lemma coeffs_above_degree :
    ∀ n (f : polynomial), (degree f < n)%N → coefficient f n = 0%R.
  Proof.
    intros n f H.
    unfold degree in H.
    destruct excluded_middle_informative.
    - subst.
      unfold coefficient, IPS.
      simpl.
      rewrite <-sub_zero_is_zero.
      simpl.
      unfold power_series.zero, IRS, power_series.IRS.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative; tauto.
    - destruct constructive_indefinite_description as [d [H0 H1]].
      auto.
  Qed.

  Lemma IPS_IRP : ∀ c : R, IPS (IRP c) = IRS c.
  Proof.
    intros c.
    now apply set_proj_injective.
  Qed.

  Lemma const_coeff_mul : ∀ (n : N) (c : R) (f : polynomial),
      coefficient ((c : polynomial) * f) n = (c * coefficient f n)%R.
  Proof.
    intros n c f.
    unfold coefficient.
    now rewrite <-power_series.const_coeff_mul, IPS_mul, IPS_IRP.
  Qed.

  Lemma coeffs_of_x_to_n : ∀ n, coefficient (x^n) n = 1%R.
  Proof.
    intros n.
    induction n using Induction.
    { rewrite rings.pow_0_r.
      simpl.
      unfold coefficient, IPS; simpl.
      rewrite <-sub_one_is_one.
      simpl.
      unfold power_series.one, IRS, power_series.IRS, coefficient.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative; tauto. }
    rewrite pow_succ_r.
    simpl.
    unfold coefficient, IPS.
    rewrite <-ISR_mul; simpl in *.
    unfold power_series.mul, coefficient in *.
    rewrite coefficient_seriesify, <-(singleton_sum Ring n (S n) 1%R).
    2: { exists 1%N; now rewrite add_1_r. }
    apply iterate_extensionality.
    intros k [H0 [c H1]].
    destruct excluded_middle_informative.
    - subst.
      rewrite <-IHn, <-add_1_r, naturals.add_comm, sub_abba.
      fold IPS (coefficient x 1).
      rewrite x_coeff_of_x.
      ring.
    - fold IPS (coefficient (x^n) k).
      rewrite coeffs_of_x_ne_n; auto; ring.
  Qed.

  Theorem coefficient_add : ∀ n (f g : polynomial),
      coefficient (f + g) n = (coefficient f n + coefficient g n)%R.
  Proof.
    intros n f g.
    unfold coefficient.
    rewrite IPS_add.
    simpl.
    now rewrite power_series.coefficient_add.
  Qed.

  Theorem coefficient_neg :
    ∀ n (f : polynomial), coefficient (-f) n = (- coefficient f n)%R.
  Proof.
    intros n f.
    unfold coefficient.
    rewrite IPS_neg.
    simpl.
    now rewrite power_series.coefficient_neg.
  Qed.

  Theorem coefficient_mul : ∀ n (f g : polynomial),
      coefficient (f * g) n =
      sum Ring (λ k, (coefficient f k * coefficient g (n-k))%R) 0 n.
  Proof.
    intros n f g.
    unfold coefficient.
    rewrite IPS_mul.
    simpl.
    now rewrite power_series.coefficient_mul.
  Qed.

  Lemma minus_leading_term : ∀ f : polynomial,
      (1 ≤ degree f → degree (f - (IRP (coefficient f (degree f))) *
                                 x^(degree f))%poly ≤ degree f - 1)%N.
  Proof.
    intros f H.
    apply degree_bound.
    intros m H0.
    rewrite (sub_is_neg (polynomial_ring Ring)),
    coefficient_add, coefficient_neg, const_coeff_mul in *.
    destruct (classic (m = degree f)) as [H1 | H1]; subst.
    - rewrite coeffs_of_x_to_n; auto.
      now ring_simplify.
    - rewrite coeffs_of_x_ne_n; auto.
      ring_simplify.
      rewrite coeffs_above_degree; auto.
      destruct H0 as [[c H0] H2], H as [d H].
      rewrite <-H0, <-H, naturals.lt_def in *.
      exists (c-1)%N.
      rewrite (naturals.add_comm 1), <-naturals.add_assoc,
      sub_abab, sub_abba in *.
      + split; auto.
        contradict H1.
        symmetry in H1.
        apply sub_0_le in H1.
        f_equal.
        apply NNPP.
        intros H3.
        rewrite (lt_1_eq_0 c), add_0_r in H2; repeat split; auto.
      + apply naturals.le_not_gt.
        contradict H2.
        apply lt_1_eq_0 in H2.
        subst.
        ring.
  Qed.

  Lemma polynomial_sum_lemma : ∀ d : N, ∀ f : polynomial,
        (degree f ≤ d)%N →
        f = sum PR (λ n, (coefficient f n : polynomial) * x^n) 0 d.
  Proof.
    intros d.
    induction d using Induction.
    { intros f [c H].
      assert (degree f = 0%N) as H0.
      { apply naturals.cancellation_0_add in H; tauto. }
      unfold sum.
      rewrite iterate_0.
      apply IPS_eq, power_series_extensionality.
      extensionality n.
      fold (coefficient f n)
           (coefficient ((coefficient f 0 : polynomial) * x ^ 0) n).
      destruct (classic (n = 0%N)) as [H1 | H1].
      - subst.
        now rewrite const_coeff_mul, coeffs_of_x_to_n, rings.M1, rings.M3.
      - rewrite const_coeff_mul, coeffs_of_x_ne_n, coeffs_above_degree; auto.
        + ring.
        + rewrite H0, naturals.lt_def.
          exists n.
          rewrite naturals.add_0_l.
          split; auto. }
    intros f H.
    destruct (classic (degree f = S d)) as [H0 | H0].
    - rewrite sum_succ, <-(rings.A3 _ f), (rings.A1 _ 0),
      <-(rings.A4 _ ((coefficient f (S d) : polynomial) * x ^ S d)),
      (rings.A1 _ ((coefficient f (S d) : polynomial) * x ^ S d)),
      rings.A2 at 1; auto using zero_le.
      f_equal.
      rewrite <-sub_is_neg, (IHd (f - (IRP (coefficient f (S d)) * x ^ S d))).
      2: { replace d with (S d - 1)%N at 3.
           - rewrite <-H0.
             apply minus_leading_term.
             rewrite H0.
             exists d.
             now rewrite naturals.add_comm, add_1_r.
           - now rewrite <-add_1_r, sub_abba. }
      apply iterate_extensionality.
      intros k [H1 H2].
      rewrite sub_is_neg, coefficient_add, coefficient_neg.
      replace (coefficient ((coefficient f (S d) : polynomial) * x ^ S d) k)
        with 0%R.
      + replace (-0)%R with 0%R by ring.
        now rewrite rings.A1, rings.A3.
      + rewrite const_coeff_mul, coeffs_of_x_ne_n.
        * ring.
        * intros H3.
          rewrite H3, naturals.le_not_gt in H2.
          contradict H2.
          apply naturals.succ_lt.
    - rewrite <-(rings.A3 _ f), rings.A1, sum_succ at 1; auto using zero_le.
      f_equal.
      + apply IHd, naturals.le_not_gt.
        intros H1.
        eauto using squeeze_upper.
      + rewrite coeffs_above_degree; repeat split; auto.
        replace (IRP 0%R) with 0 by now apply set_proj_injective.
        ring.
  Qed.

  Theorem degree_of_sum : ∀ d (a : N → R),
      (degree (sum PR (λ n, (a n : polynomial) * x^n)%poly 0 d) ≤ d)%N.
  Proof.
    intros d a.
    apply degree_bound; auto.
    intros m H.
    induction d using Induction.
    - unfold sum.
      rewrite iterate_0, const_coeff_mul, coeffs_of_x_ne_n;
        try now ring_simplify.
      intros H0.
      subst.
      contradiction (naturals.lt_irrefl 0).
    - rewrite sum_succ, coefficient_add, IHd; auto using zero_le.
      + rewrite rings.A3, const_coeff_mul, coeffs_of_x_ne_n;
          try now ring_simplify.
        intros H0.
        subst.
        contradiction (naturals.lt_irrefl (S d)).
      + eauto using naturals.lt_trans, naturals.succ_lt.
  Qed.

  Theorem coefficient_sum_add : ∀ d a k,
      coefficient (sum _ (λ n, a n) 0 d) k =
      sum _ (λ n, (coefficient (a n) k)) 0 d.
  Proof.
    intros d a k.
    induction d using Induction.
    - unfold sum.
      now rewrite ? iterate_0.
    - rewrite ? sum_succ, <-IHd, coefficient_add; auto using zero_le.
  Qed.

  Theorem coefficient_extraction : ∀ d k (a : N → R),
      (k ≤ d)%N →
      coefficient (sum _ (λ n, (a n : polynomial) * x^n) 0 d) k = (a k).
  Proof.
    intros d k a H.
    rewrite coefficient_sum_add.
    rewrite <-(singleton_sum _ k d (a k)); auto.
    apply iterate_extensionality.
    intros z H0.
    destruct excluded_middle_informative.
    - subst.
      rewrite const_coeff_mul, coeffs_of_x_to_n.
      ring.
    - rewrite const_coeff_mul, coeffs_of_x_ne_n; auto; ring.
  Qed.

  Theorem coeff_of_x_mul : ∀ n k f,
      (k ≤ n)%N → coefficient (f * x^k) n = coefficient f (n-k).
  Proof.
    intros n k f H.
    revert n H.
    induction k using Induction; intros n H.
    { rewrite rings.pow_0_r, sub_0_r.
      f_equal.
      ring. }
    destruct (classic (k ≤ n)%N) as [H0 | H0].
    - unfold coefficient.
      rewrite pow_succ_r, rings.M2, rings.M1, IPS_mul.
      replace (IPS x) with (power_series.x Ring)
        by now apply set_proj_injective.
      simpl.
      rewrite mul_x_shift.
      unfold shift.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative.
      { subst.
        rewrite naturals.le_not_gt in H.
        contradict H.
        now apply naturals.lt_succ. }
      pose proof IHk (n-1)%N as H1.
      unfold coefficient in H1.
      simpl in H1.
      rewrite H1.
      + f_equal.
        apply succ_0 in n0 as [m H2].
        subst.
        destruct H as [c H].
        rewrite <-H, (naturals.add_comm _ c), <-add_1_r, naturals.add_assoc,
        ? sub_abba at 1.
        now apply sub_spec.
      + destruct H as [c H].
        exists c.
        subst.
        now rewrite ? (naturals.add_comm _ c), <-add_1_r,
        naturals.add_assoc, sub_abba.
    - contradict H0.
      eapply naturals.le_trans; eauto.
      exists 1%N.
      now rewrite add_1_r.
  Qed.

  Theorem add_degree :
    ∀ f g, (degree (f + g)%poly ≤ naturals.max (degree f) (degree g))%N.
  Proof.
    intros f g.
    unfold naturals.max.
    destruct excluded_middle_informative.
    - apply degree_bound.
      intros m H.
      rewrite coefficient_add, ? coeffs_above_degree, rings.A3;
        eauto using naturals.lt_trans.
    - apply naturals.le_not_gt in n.
      apply degree_bound.
      intros m H.
      rewrite coefficient_add, ? coeffs_above_degree, rings.A3;
        eauto using naturals.le_lt_trans.
  Qed.

  Theorem mul_degree : ∀ f g, (degree (f * g)%poly ≤ degree f + degree g)%N.
  Proof.
    intros f g.
    apply degree_bound; auto.
    intros m H0.
    rewrite coefficient_mul, <-(sum_of_0 _ m).
    apply iterate_extensionality.
    intros k H1.
    destruct (classic (degree f < k)%N) as [H2 | H2].
    - rewrite coeffs_above_degree; auto; ring.
    - rewrite (coeffs_above_degree _ g); try ring.
      apply naturals.lt_not_ge.
      contradict H2.
      rewrite naturals.lt_not_ge in *.
      contradict H0.
      replace m with (k + (m-k))%N; auto using naturals.le_cross_add.
      destruct H1 as [H1 [c H3]].
      subst.
      now rewrite ? (naturals.add_comm k), sub_abba.
  Qed.

  Theorem coeff_of_x_mul_overflow :
    ∀ n k f, (n < k)%N → coefficient (f * x^k) n = 0%R.
  Proof.
    intros n k f H.
    rewrite coefficient_mul, <-(sum_of_0 _ n).
    apply iterate_extensionality.
    intros z [H0 [c H1]].
    rewrite coeffs_of_x_ne_n; try ring.
    intros H2.
    subst.
    rewrite naturals.lt_not_ge in H.
    contradict H.
    rewrite (naturals.add_comm z), sub_abba.
    now (exists z).
  Qed.

  Definition eval f a := (sum _ (λ n, (coefficient f n) * a^n)%R 0 (degree f)).

  Coercion eval : polynomial >-> Funclass.

  Definition root (f : polynomial) r := (f r) = 0%R.

  Lemma sum_beyond_degree : ∀ f a m,
      (degree f ≤ m)%N →
      (sum _ (λ n, coefficient f n * a^n) 0 (degree f))%R =
      (sum _ (λ n, coefficient f n * a^n) 0 m)%R.
  Proof.
    intros f a m H.
    induction m using Induction.
    - replace (degree f) with 0%N; auto using naturals.le_antisymm, zero_le.
    - destruct (classic (degree f ≤ m)%N) as [H0 | H0].
      + rewrite sum_succ, IHm, coeffs_above_degree, mul_0_l,
        rings.A1, rings.A3; auto using zero_le.
        destruct H0 as [c H0].
        rewrite naturals.lt_def.
        exists (S c).
        split; auto using PA4.
        rewrite add_succ_r.
        congruence.
      + f_equal.
        apply naturals.le_antisymm; auto.
        rewrite naturals.le_not_gt, naturals.lt_def.
        contradict H0.
        destruct H0 as [c [H0 H1]].
        assert (c ≠ 0%N) as H2 by auto.
        apply succ_0 in H2 as [k H2].
        subst.
        exists k.
        rewrite add_succ_r in H1.
        now apply PA5.
  Qed.

  Theorem eval_add :
    ∀ (f g : polynomial) a, ((f + g : polynomial) a) = (f a + g a)%R.
  Proof.
    intros f g a.
    unfold eval.
    set (m := (naturals.max (degree f) (degree g))).
    rewrite (sum_beyond_degree (f+g) a m), (sum_beyond_degree f a m),
    (sum_beyond_degree g a m), <-sum_dist; unfold m;
      eauto using add_degree, naturals.max_le_l, naturals.max_le_r.
    f_equal.
    extensionality n.
    now rewrite coefficient_add, rings.D1.
  Qed.

  Theorem eval_bound : ∀ (f : polynomial) a n,
      (degree f ≤ n)%N → sum _ (λ n : N, (coefficient f n * a^n)%R) 0 n = (f a).
  Proof.
    intros f a n H.
    unfold eval.
    now rewrite (sum_beyond_degree f a n).
  Qed.

  Theorem degree_x_to_n : ∀ k, (1%R ≠ 0%R) → degree (x^k) = k.
  Proof.
    intros k H.
    unfold degree.
    destruct excluded_middle_informative.
    - contradict H.
      replace (1%R) with (coefficient (x^k) k); auto using coeffs_of_x_to_n.
      replace (0%R) with (coefficient 0 k); try congruence.
      unfold coefficient, IPS.
      simpl.
      rewrite <-sub_zero_is_zero.
      simpl.
      unfold power_series.zero, power_series.IRS.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative; auto.
    - destruct constructive_indefinite_description.
      destruct a as [H0 H1].
      apply NNPP.
      contradict H0.
      rewrite coeffs_of_x_ne_n; auto.
  Qed.

  Lemma degree_const : ∀ c : R, degree (c : polynomial) = 0%N.
  Proof.
    intros c.
    apply naturals.le_antisymm; auto using zero_le.
    apply degree_bound.
    intros m H.
    rewrite <-(rings.M3 _ (c : polynomial)), rings.M1, const_coeff_mul,
    <-(rings.pow_0_r _ x), coeffs_of_x_ne_n, mul_0_r; auto.
    intros H0.
    subst.
    contradiction (naturals.lt_irrefl 0).
  Qed.

  Lemma coeff_const : ∀ c : R, coefficient (c : polynomial) 0 = c.
  Proof.
    intros c.
    destruct (classic (c = 0%R)) as [H | H].
    { subst.
      rewrite <-(rings.M3 _ (IRP 0)), rings.M1, const_coeff_mul.
      now ring_simplify. }
    rewrite <-(rings.M3 _ (c : polynomial)), rings.M1, const_coeff_mul,
    <-(rings.pow_0_r _ x), coeffs_of_x_to_n.
    now ring_simplify.
  Qed.

  Lemma degree_lower_bound : ∀ n f, coefficient f n ≠ 0%R → (n ≤ degree f)%N.
  Proof.
    intros n f H.
    unfold degree.
    destruct excluded_middle_informative.
    - contradict H.
      subst.
      replace 0 with (IRP 0) by now apply set_proj_injective.
      destruct (classic (n = 0%N)) as [H | H].
      + now rewrite H, coeff_const.
      + rewrite coeffs_above_degree; auto.
        rewrite degree_const.
        apply succ_0 in H as [m H].
        subst.
        now apply naturals.lt_succ.
    - destruct constructive_indefinite_description as [d].
      destruct a as [H0 H1].
      apply naturals.le_not_gt.
      intros H2.
      now apply H1 in H2.
  Qed.

  Lemma eval_mul_const : ∀ (c α : R) f,
      ((c : polynomial) * f : polynomial) α = (c * (f : polynomial) α)%R.
  Proof.
    intros c α f.
    unfold eval.
    rewrite (sum_beyond_degree ((c : polynomial) * f) _ (degree f)).
    - rewrite sum_mul.
      f_equal.
      extensionality n.
      rewrite const_coeff_mul.
      ring.
    - eapply naturals.le_trans; auto using mul_degree.
      rewrite degree_const, add_0_l.
      auto using naturals.le_refl.
  Qed.

  Lemma eval_x : ∀ n α, ((x^n : polynomial) α) = (α^n)%R.
  Proof.
    intros n α.
    unfold eval.
    destruct (classic (1%R = 0%R)) as [| H]; auto using zero_ring_degeneracy.
    rewrite degree_x_to_n; auto.
    replace (α^n)%R with (sum _ (λ k, (if (excluded_middle_informative (k = n))
                                       then α^n else 0)%R) 0 n) at 1.
    - apply iterate_extensionality.
      intros k H0.
      destruct excluded_middle_informative.
      + subst.
        rewrite coeffs_of_x_to_n.
        ring.
      + rewrite coeffs_of_x_ne_n; auto; ring.
    - clear.
      destruct (classic (n = 0%N)).
      + subst.
        unfold sum.
        rewrite iterate_0, rings.pow_0_r.
        destruct excluded_middle_informative; tauto.
      + apply succ_0 in H as [m H].
        subst.
        rewrite sum_succ; auto using zero_le.
        destruct excluded_middle_informative; try tauto.
        rewrite <-(rings.A3 _ (α^(S m))%R) at 2.
        f_equal.
        rewrite <-(sum_of_0 _ m) at 1.
        apply iterate_extensionality.
        intros k [H H0].
        destruct excluded_middle_informative; auto.
        subst.
        apply naturals.le_not_gt in H0.
        contradict H0.
        auto using naturals.succ_lt.
  Qed.

  Lemma eval_mul_x_lemma : ∀ m (α : R) (f : N → R) n,
      (((sum _ (λ i, (f i : polynomial) * x^i) 0 m) * x^n : polynomial) α) =
      (((sum _ (λ i, (f i : polynomial) * x^i)%poly 0 m : polynomial) α) *
       α^n)%R.
  Proof.
    intros m.
    induction m using Induction.
    { intros α f n.
      unfold sum.
      rewrite iterate_0, rings.pow_0_r, (rings.M1 _ _ 1), rings.M3,
      eval_mul_const, eval_x.
      f_equal.
      unfold eval.
      rewrite degree_const.
      unfold sum.
      now rewrite iterate_0, rings.pow_0_r, coeff_const, rings.M1, rings.M3. }
    intros α f n.
    rewrite ? sum_succ, rings.D1, ? eval_add, rings.D1, IHm, <-rings.M2,
    ? eval_mul_const, <-rings.M2, <-rings.pow_add_r, ? eval_x, rings.pow_add_r;
      auto using zero_le.
  Qed.

  Lemma eval_mul_x_f : ∀ f a n,
      ((f * x^n : polynomial) a) =
      (((f : polynomial) a) * (((x^n)%poly : polynomial) a))%R.
  Proof.
    intros f a n.
    now rewrite (polynomial_sum_lemma (degree f) f), ? eval_mul_x_lemma, eval_x;
      auto using le_refl.
  Qed.

  Lemma eval_mul_lemma : ∀ n f (a : N → R) α,
      (((f * (sum PR (λ i, (a i : polynomial) * x^i)) 0%N n) : polynomial) α) =
      (((f : polynomial) α) * (sum _ (λ i, (a i) * α^i) 0 n))%R.
  Proof.
    intros n f a α.
    induction n using Induction.
    { unfold sum.
      now rewrite ? iterate_0, ? rings.M2,
      ? (rings.M1 _ _ (a 0%N : polynomial)), ? (rings.M1 _ _ (a 0%N)),
      <-? rings.M2, eval_mul_const, eval_mul_x_f, eval_x. }
    rewrite ? sum_succ, ? rings.D1_l, <-IHn, eval_add; auto using zero_le.
    f_equal.
    rewrite <-eval_x, rings.M1, <-rings.M2, eval_mul_const, (rings.M1 _ _ f),
    eval_mul_x_f.
    ring.
  Qed.

  Theorem eval_mul :
    ∀ (f g : polynomial) a, ((f * g : polynomial) a) = (f a * g a)%R.
  Proof.
    intros f g a.
    rewrite (polynomial_sum_lemma (degree g) g), eval_mul_lemma, eval_bound;
      auto using naturals.le_refl.
    do 2 f_equal; try extensionality n;
      rewrite <-polynomial_sum_lemma; auto using naturals.le_refl.
  Qed.

  Definition linear f := (degree f = 1%N).

  Theorem linear_classification : ∀ f, linear f ↔ ∃ a b : R,
          f = (a : polynomial) + (b : polynomial) * x ∧ b ≠ 0%R.
  Proof.
    intros f.
    split; intros H.
    - unfold linear in H.
      rewrite (polynomial_sum_lemma 1 f).
      2: { rewrite H.
           auto using le_refl. }
      exists (coefficient f 0), (coefficient f 1).
      split.
      + unfold naturals.one.
        rewrite sum_succ; auto using zero_le.
        unfold sum.
        rewrite iterate_0, rings.pow_0_r.
        f_equal; try now ring_simplify.
        fold naturals.one.
        now rewrite rings.pow_1_r.
      + intros H0.
        contradiction (PA4 0).
        fold naturals.one.
        rewrite <-H.
        symmetry.
        apply naturals.le_antisymm; auto using zero_le.
        apply degree_bound.
        intros m [H1 H2].
        assert (m ≠ 0%N) as H3 by auto.
        apply succ_0 in H3 as [k H3].
        subst.
        destruct (classic ((S k) = 1%N)) as [H3 | H3]; try congruence.
        rewrite coeffs_above_degree; auto.
        rewrite H, naturals.lt_def.
        exists k.
        rewrite naturals.add_comm, naturals.add_1_r.
        split; auto.
        contradict H3.
        now rewrite <-H3.
    - destruct H as [a [b [H H0]]].
      subst.
      unfold linear.
      apply naturals.le_antisymm.
      + apply degree_bound.
        intros m H.
        rewrite coefficient_add, const_coeff_mul, ? coeffs_above_degree;
          try now ring_simplify.
        * rewrite <-(rings.pow_1_r _ x), degree_x_to_n; auto.
          contradict H0.
          now apply zero_ring_degeneracy.
        * rewrite degree_const.
          eapply naturals.lt_trans; eauto using naturals.succ_lt.
      + apply degree_lower_bound.
        rewrite coefficient_add, coeffs_above_degree, const_coeff_mul,
        x_coeff_of_x.
        2: { rewrite degree_const; eauto using naturals.succ_lt. }
        contradict H0.
        ring_simplify in H0.
        now subst.
  Qed.

  Theorem IRP_1 : ((1%R : R) : polynomial) = 1.
  Proof.
    unfold IRP.
    apply set_proj_injective.
    simpl.
    unfold ISS, power_series.IRS, sub_one.
    destruct polynomials_are_subring.
    now repeat destruct a.
  Qed.

  Theorem degree_of_a_plus_x :
    1%R ≠ 0%R → ∀ α : R, degree ((α : polynomial) + x) = 1%N.
  Proof.
    intros H α.
    apply linear_classification.
    exists α, 1%R.
    rewrite IRP_1.
    split; auto; ring.
  Qed.

  Definition monic f := (coefficient f (degree f) = 1%R).

  Theorem leading_term_prod : ∀ f g,
      (coefficient f (degree f) * coefficient g (degree g))%R =
      coefficient (f * g) (degree f + degree g)%N.
  Proof.
    intros f g.
    rewrite coefficient_mul.
    replace (coefficient f (degree f) * coefficient g (degree g))%R
      with (sum _ (λ k, if (excluded_middle_informative (k = degree f)) then
                          (coefficient f (degree f) *
                           coefficient g (degree g))%R else 0%R)
                0 (degree f + degree g)%N).
    2: { rewrite singleton_sum; auto.
         now exists (degree g). }
    apply iterate_extensionality.
    intros k H.
    destruct (lt_trichotomy k (degree f)) as [H0 | [H0 | H0]].
    - destruct excluded_middle_informative.
      { subst; contradiction (naturals.lt_irrefl (degree f)). }
      rewrite (coeffs_above_degree _ g); try ring.
      destruct H0 as [[c H0] H2].
      rewrite <-H0, <-naturals.add_assoc, naturals.add_comm, sub_abba,
      naturals.add_comm, naturals.lt_def.
      exists c.
      split; auto.
      contradict H2.
      subst.
      ring [H0].
    - subst.
      destruct excluded_middle_informative; try tauto.
      now rewrite naturals.add_comm, sub_abba.
    - destruct excluded_middle_informative.
      { subst; contradiction (naturals.lt_irrefl (degree f)). }
      rewrite coeffs_above_degree; auto; ring.
  Qed.

  Theorem zero_ring_degree : 1%R = 0%R → ∀ f, degree f = 0%N.
  Proof.
    intros H f.
    apply naturals.le_antisymm; auto using zero_le.
    apply degree_bound.
    intros m H0.
    now apply zero_ring_degeneracy.
  Qed.

  Theorem zero_ring_monic : 1%R = 0%R → ∀ f, monic f.
  Proof.
    intros H f.
    unfold monic.
    now apply zero_ring_degeneracy.
  Qed.

  Theorem monic_prod_degree :
    ∀ f g, monic f → monic g → degree (f * g) = (degree f + degree g)%N.
  Proof.
    intros f g H H0.
    destruct (classic (1%R = 0%R)) as [H1 | H1].
    { rewrite ? zero_ring_degree; auto; ring. }
    apply naturals.le_antisymm; auto using mul_degree.
    apply degree_lower_bound.
    unfold monic in *.
    now rewrite <-leading_term_prod, H, H0, rings.M3.
  Qed.

  Theorem monic_prod : ∀ f g, monic f → monic g → monic (f * g).
  Proof.
    intros f g H H0.
    unfold monic in *.
    rewrite monic_prod_degree, <-leading_term_prod, H, H0, rings.M3; auto.
  Qed.

  Theorem monic_a_plus_x : ∀ α : R, monic ((α : polynomial) + x).
  Proof.
    intros α.
    destruct (classic (1%R = 0%R)) as [H | H]; auto using zero_ring_monic.
    unfold monic.
    rewrite degree_of_a_plus_x, coefficient_add, coeffs_above_degree,
    x_coeff_of_x; auto; try now ring_simplify.
    rewrite degree_const.
    apply naturals.lt_succ.
  Qed.

  Theorem monic_powers : ∀ n f, monic f → monic (f^n).
  Proof.
    intros n f H.
    induction n using Induction.
    - rewrite rings.pow_0_r.
      unfold monic.
      now rewrite <-IRP_1, degree_const, coeff_const.
    - rewrite pow_succ_r.
      now apply monic_prod.
  Qed.

  Theorem monic_pow_degree : ∀ n f, monic f → degree (f^n) = (n * degree f)%N.
  Proof.
    intros n f H.
    induction n using Induction.
    - rewrite rings.pow_0_r, <-IRP_1, degree_const.
      ring.
    - rewrite pow_succ_r, monic_prod_degree, IHn, <-add_1_r;
        auto using monic_powers; ring.
  Qed.

  Theorem degree_of_a_plus_x_to_n :
    1%R ≠ 0%R → ∀ n (α : R), degree (((α : polynomial) + x)^n) = n.
  Proof.
    intros H n α.
    rewrite monic_pow_degree, degree_of_a_plus_x;
      auto using monic_a_plus_x; ring.
  Qed.

  Definition INR := (INR Ring) : N → R.
  Coercion INR : N >-> R.

  Lemma binomial_theorem_zero : ∀ n (α : R),
      coefficient (((α : polynomial) + x)^n) 0 = ((binomial n 0 : R) * α^n)%R.
  Proof.
    induction n using Induction; intros α.
    - subst.
      rewrite ? rings.pow_0_r, <-(rings.pow_0_r _ x), coeffs_of_x_to_n,
      binomial_zero, rings.M1, rings.M3.
      unfold INR, rings.INR, sum.
      now rewrite iterate_0.
    - rewrite pow_succ_r, D1_l, coefficient_add, binomial_zero,
      (rings.M1 _ _ (α : polynomial)), const_coeff_mul, IHn.
      rewrite <-(rings.pow_1_r _ x) at 2.
      rewrite coeff_of_x_mul_overflow, binomial_zero, pow_succ_r;
        eauto using naturals.succ_lt.
      now ring_simplify.
  Qed.

  Lemma INR_0 : (0%R : R) = 0%N.
  Proof.
    unfold INR, rings.INR, sum, iterate_with_bounds.
    destruct excluded_middle_informative; auto.
    exfalso; apply naturals.le_not_gt in l.
    eauto using naturals.succ_lt.
  Qed.

  Theorem generalized_binomial_theorem : ∀ n k (α : R),
      coefficient (((α : polynomial) + x)^n) k =
      ((binomial n k : R) * α^(n-k))%R.
  Proof.
    intros n k.
    revert k.
    induction n using Induction; intros k α.
    { destruct (classic (k = 0%N)) as [H | H].
      - now subst; rewrite binomial_theorem_zero, sub_diag.
      - rewrite rings.pow_0_r, <-(rings.pow_0_r _ x),
        coeffs_of_x_ne_n, binomial_empty_set; auto.
        unfold INR, rings.INR, sum, iterate_with_bounds.
        destruct excluded_middle_informative; auto.
        + apply naturals.le_not_gt in l as H0.
          exfalso; eauto using naturals.succ_lt.
        + now rewrite mul_0_l. }
    destruct (classic (k = 0%N)) as [H | H].
    { now subst; rewrite binomial_theorem_zero, sub_0_r. }
    rewrite pow_succ_r, D1_l, rings.M1, coefficient_add, const_coeff_mul, IHn.
    rewrite <-(rings.pow_1_r _ x) at 2.
    apply succ_0 in H as [c H].
    rewrite coeff_of_x_mul, IHn, (rings.M1 _ α), <-rings.M2.
    2: { exists c; now rewrite H, <-add_1_r, naturals.add_comm. }
    rewrite <-(rings.pow_1_r _ α) at 2.
    rewrite <-rings.pow_add_r.
    subst.
    destruct (classic (n = 0%N)) as [H | H].
    { subst.
      rewrite binomial_empty_set, sub_0_l, <-INR_0, rings.mul_0_l, rings.A3.
      2: { intros H.
           symmetry in H.
           contradiction (PA4 c). }
      rewrite <-sub_succ, ? sub_0_l.
      f_equal.
      destruct (classic (c = 0%N)) as [H | H].
      - subst.
        fold naturals.one.
        now rewrite sub_diag, binomial_one, binomial_zero.
      - rewrite binomial_empty_set, binomial_overflow; auto.
        + rewrite naturals.lt_def.
          exists c.
          split; auto.
          now rewrite naturals.add_comm, add_succ_r, add_0_r.
        + contradict H.
          now rewrite <-add_1_r, sub_abba in H. }
    apply succ_0 in H as [m H].
    subst.
    rewrite <-? sub_succ, <-(add_1_r c), sub_abba.
    destruct (lt_trichotomy c (S m)) as [H | [H | H]].
    - apply le_lt_succ in H as [d H].
      subst.
      rewrite <-? add_1_r, <-(add_assoc c), ? (add_comm c), ? sub_abba,
      <-rings.D1, <-Pascal's_identity, (add_comm 1%N), sub_abba,
      <-rings.INR_add; auto.
      now exists c.
    - subst.
      rewrite sub_diag, ? rings.pow_0_r, ? (rings.M1 _ _ 1%R), ? rings.M3,
      ? add_1_r, binomial_overflow, ? binomial_n_n, <-INR_0, mul_0_l, rings.A3;
        auto using naturals.succ_lt.
    - rewrite ? binomial_overflow, <-INR_0; try now ring_simplify.
      + now rewrite add_1_r, <-S_lt.
      + rewrite add_1_r.
        eauto using naturals.lt_trans, naturals.succ_lt.
  Qed.

  Theorem binomial_theorem : ∀ n k, coefficient ((1 + x)^n) k = binomial n k.
  Proof.
    intros n k.
    rewrite <-IRP_1, (generalized_binomial_theorem n k 1%R), rings.pow_1_l.
    now ring_simplify.
  Qed.

  Theorem generalized_binomial_sum : ∀ n (α : R),
      ((α : polynomial) + x)^n =
      sum _ (λ k, ((((binomial n k : R) * α^(n-k))%R : R) : polynomial) * x^k)
          0 n.
  Proof.
    intros n α.
    rewrite (polynomial_sum_lemma n (((α : polynomial) + x)^n)).
    - apply iterate_extensionality.
      intros k H.
      now rewrite generalized_binomial_theorem.
    - destruct (classic (1%R = 0%R)).
      + rewrite zero_ring_degree; auto using zero_le.
      + rewrite degree_of_a_plus_x_to_n; auto using le_refl.
  Qed.

  Theorem binomial_sum : ∀ n,
      (1 + x)^n = sum _ (λ k, (binomial n k : polynomial) * x^k) 0 n.
  Proof.
    intros n.
    rewrite <-IRP_1, generalized_binomial_sum.
    f_equal.
    extensionality k.
    now rewrite rings.pow_1_l, (rings.M1 _ _ 1%R), rings.M3.
  Qed.

  Definition leading_coefficient f := coefficient f (degree f).

  Lemma leading_coefficient_nonzero : ∀ f, leading_coefficient f = 0%R → f = 0.
  Proof.
    intros f H.
    unfold leading_coefficient in H.
    apply NNPP.
    intros H0.
    pose proof (eq_refl (degree f)) as H1.
    eapply (degree_spec f) in H0.
    intuition.
  Qed.

  Lemma const_mul_monic : ∀ a f,
      a ≠ 0%R → monic f → degree (((a : R) : polynomial) * f) = degree f.
  Proof.
    intros a f H H0.
    apply naturals.le_antisymm.
    - apply degree_bound.
      intros m H1.
      rewrite const_coeff_mul, coeffs_above_degree; auto; now ring_simplify.
    - apply degree_lower_bound.
      unfold monic in *.
      now rewrite const_coeff_mul, H0, rings.M1, rings.M3.
  Qed.

  Lemma monic_division_algorithm_helper : ∀ a b n,
      monic b → (0 < degree b)%N → (degree a ≤ n)%N →
      ∃ q r, a = b * q + r ∧ (degree r < degree b)%N.
  Proof.
    destruct (classic (1%R = 0%R)) as [H | H]; intros a b n H0 H1 H2.
    { exists 0, 0.
      split; try apply zero_ring_degeneracy;
        replace 0 with ((0%R : R) : polynomial) by now apply set_proj_injective.
      - now rewrite <-IRP_1, H.
      - now rewrite degree_const. }
    revert n a H2.
    induction n using Induction; intros a H2.
    { exists 0, a.
      split; try ring.
      eauto using naturals.le_lt_trans. }
    destruct (classic (degree a ≤ n)%N) as [H3 | H3]; try now apply IHn in H3.
    destruct (classic (degree a < degree b)%N) as [H4 | H4].
    { exists 0, a.
      split; auto; ring. }
    apply naturals.le_not_gt in H4 as [c H4].
    assert (degree a = S n) as H5.
    { apply naturals.lt_not_ge in H3.
      now apply squeeze_upper. }
    assert (1 ≤ degree a)%N as H6.
    { exists n.
      now rewrite H5, <-add_1_r, naturals.add_comm. }
    destruct (IHn (a - (leading_coefficient a : polynomial) * x^c * b))
      as [q [r [H7 H8]]].
    2: { exists (q + (leading_coefficient a : polynomial) * x^c), r.
         split; auto.
         ring_simplify [H7].
         rewrite <-rings.A2, <-H7.
         ring. }
    apply degree_bound.
    intros m H7.
    rewrite rings.sub_is_neg, coefficient_add, coefficient_neg.
    destruct (classic (S n < m)%N) as [H8 | H8].
    - rewrite ? coeffs_above_degree; try now ring_simplify; try congruence.
      eapply naturals.le_lt_trans; eauto.
      rewrite <-H5, <-H4.
      eapply naturals.le_trans; eauto using mul_degree.
      exists 0%N.
      rewrite add_0_r, naturals.add_comm.
      f_equal.
      rewrite const_mul_monic; auto using degree_x_to_n.
      + intros H9.
        apply leading_coefficient_nonzero in H9.
        subst.
        unfold degree in H5.
        destruct excluded_middle_informative.
        * contradiction (PA4 n).
        * now contradiction n0.
      + unfold monic.
        rewrite degree_x_to_n, coeffs_of_x_to_n; auto.
    - apply naturals.le_not_gt in H8.
      replace m with (S n) by now apply eq_sym, squeeze_upper.
      unfold leading_coefficient, monic in *.
      rewrite <-H5, <-rings.M2, const_coeff_mul, (rings.M1 PR),
      coeff_of_x_mul, <-H4, sub_abba, H0.
      + now ring_simplify.
      + exists (degree b).
        now rewrite <-H4, naturals.add_comm.
  Qed.

  Theorem monic_division_algorithm : ∀ a b,
      monic b → (0 < degree b)%N → ∃ q r,
          a = b * q + r ∧ (degree r < degree b)%N.
  Proof.
    intros a b H H0.
    eapply monic_division_algorithm_helper; eauto using le_refl.
  Qed.

  Definition const f := degree f = 0%N.

  Theorem const_classification : ∀ f, const f ↔ ∃ c : R, f = (c : polynomial).
  Proof.
    split; unfold const; intros H.
    - exists (coefficient f 0).
      rewrite (polynomial_sum_lemma 0 f) at 1.
      unfold sum.
      rewrite iterate_0, rings.pow_0_r.
      ring.
      rewrite H.
      auto using le_refl.
    - destruct H as [c H].
      subst.
      now rewrite degree_const.
  Qed.

  Theorem eval_const : ∀ a b : R, ((a : polynomial) b) = a.
  Proof.
    intros a b.
    rewrite <-(rings.M3 _ (a : polynomial)), rings.M1, <-(rings.pow_0_r _ x),
    eval_mul_const, eval_x, rings.pow_0_r.
    ring.
  Qed.

  Theorem eval_neg :
    ∀ (f : polynomial) a, ((-f : polynomial) a) = (- (f a))%R.
  Proof.
    intros f a.
    rewrite <-rings.mul_neg_1_l, eval_mul, <-IRP_1, IRP_neg, eval_const.
    ring.
  Qed.

  Infix "｜" := (rings.divide PR).

  Theorem roots_classification :
    ∀ f (a : R), root f a ↔ (x - (a : polynomial))｜f.
  Proof.
    destruct (classic (1%R = 0%R)) as [H | H]; split; intros H0;
      try now apply zero_ring_degeneracy.
    { exists 1.
      apply zero_ring_degeneracy.
      replace 0 with ((0%R : R) : polynomial) by now apply set_proj_injective.
      now rewrite <-IRP_1, H. }
    - assert (linear (x - (a : polynomial))) as H1; try unfold linear in H1.
      { rewrite linear_classification.
        exists (-a)%R, 1%R.
        split; auto.
        rewrite IRP_1, <-IRP_neg.
        ring. }
      destruct (monic_division_algorithm f (x - (a : polynomial)))
        as [q [r [H2 H3]]]; try rewrite H1 in *; eauto using naturals.succ_lt.
      + replace (x - (a : polynomial)) with (((-a : R)%R : polynomial) + x);
          auto using monic_a_plus_x.
        rewrite sub_is_neg, IRP_neg.
        ring.
      + exists q.
        rewrite rings.M1, H2.
        replace r with 0; try ring.
        assert (const r) as H4.
        { unfold const.
          apply NNPP.
          intros H4.
          apply succ_0 in H4 as [c H4].
          rewrite H4, naturals.lt_not_ge, <-add_1_r, naturals.add_comm in H3.
          contradict H3.
          now (exists c). }
        apply const_classification in H4 as [c H4].
        subst.
        symmetry.
        unfold root in H0.
        replace 0 with ((0%R : R) : polynomial) by now apply set_proj_injective.
        now rewrite <-H0, eval_add, eval_mul, sub_is_neg, eval_add, eval_neg,
        <-(rings.pow_1_r _ x), eval_x, ? eval_const, rings.pow_1_r, rings.A4,
        mul_0_l, rings.A3.
    - destruct H0 as [q H0].
      subst.
      unfold root.
      rewrite eval_mul, sub_is_neg, eval_add, <-(rings.pow_1_r _ x), eval_neg,
      eval_x, ? eval_const, rings.pow_1_r.
      ring.
  Qed.

End Polynomial_theorems.
