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

  Add Ring proto_generic_ring :
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
      rewrite coefficient_seriesify.
      replace 0 with (sum R (λ k : N, 0) 0 x).
      + apply iterate_extensionality.
        intros k H3.
        destruct (classic (n ≤ k)%N).
        * rewrite H2; auto; ring.
        * rewrite H4, mul_0_r; auto.
          apply NNPP.
          intros H6.
          rewrite <-naturals.lt_not_ge in H5, H6.
          assert (k + (x - k) < n + m)%N as H7 by
                now apply naturals.lt_cross_add.
          rewrite sub_abab, naturals.lt_not_ge in H7; intuition.
      + clear.
        induction x using Induction.
        * unfold sum.
          now rewrite iterate_0.
        * rewrite sum_succ, IHx, rings.A3; auto using zero_le.
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

  Definition add := rings.add polynomial_ring : poly → poly → poly.
  Infix "+" := add : Poly_scope.
  Definition mul := rings.mul polynomial_ring : poly → poly → poly.
  Infix "*" := mul : Poly_scope.
  Definition sub := rings.sub polynomial_ring : poly → poly → poly.
  Infix "-" := sub : Poly_scope.
  Definition zero := rings.zero polynomial_ring : poly.
  Definition one := rings.one polynomial_ring : poly.
  Notation "0" := zero : Poly_scope.
  Notation "1" := one : Poly_scope.
  Definition neg := rings.neg polynomial_ring : poly → poly.
  Notation "- f" := (neg f) : Poly_scope.

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
  (*Coercion IRS : R >-> power_series.*)

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
      apply functional_extensionality.
      intros n.
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
    apply naturals.le_antisymm; split; eauto.
    apply succ_0 in n0 as [c H].
    subst.
    rewrite <-add_1_r.
    exists c.
    ring.
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
    rewrite coefficient_seriesify.
    replace 0%R with (sum Ring (λ k : N, 0%R) 0 m).
    - apply iterate_extensionality.
      intros k [H0 [c H1]].
      destruct (classic (n = k)).
      + subst.
        replace (power_series.coefficient _ (x : power_series) (k + c - k))
          with 0%R; try ring.
        symmetry.
        apply coeffs_of_x.
        contradict H.
        rewrite naturals.add_comm, sub_abba in H.
        subst.
        now rewrite add_1_r.
      + rewrite IHn, rings.mul_0_l; auto.
    - clear.
      induction m using Induction.
      * unfold sum.
        now rewrite iterate_0.
      * rewrite sum_succ, IHm, rings.A3; auto using zero_le.
  Qed.

  Lemma degree_bound : ∀ n (f : polynomial),
      f ≠ 0 → (∀ m : N, (n < m)%N → coefficient f m = 0%R) → (degree f ≤ n)%N.
  Proof.
    intros n f H H0.
    unfold degree.
    destruct excluded_middle_informative; try tauto.
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

  Lemma neg_coeff_mul : ∀ (n : N) (f : polynomial),
      coefficient (- f) n = (- coefficient f n)%R.
  Proof.
    intros n f.
    replace (-f)%poly with (((-(1) : R)%R : polynomial) * f) at 1.
    { rewrite const_coeff_mul.
      now ring_simplify. }
    apply IPS_eq.
    rewrite IPS_mul, IPS_IRP, IPS_neg.
    unfold IRS; rewrite IRS_neg; fold IRS.
    replace (power_series.neg Ring (IRS 1)) with ((-(1))%series) by auto.
    now ring_simplify.
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
    rewrite coefficient_seriesify.
    replace 1%R with
        (sum Ring (λ k : N, if (excluded_middle_informative (k = n))
                            then 1%R else 0%R) 0 (S n)).
    - apply iterate_extensionality.
      intros k [H0 [c H1]].
      destruct excluded_middle_informative.
      + subst.
        rewrite <-IHn, <-add_1_r, naturals.add_comm, sub_abba.
        fold IPS (coefficient x 1).
        rewrite x_coeff_of_x.
        ring.
      + fold IPS (coefficient (x^n) k).
        rewrite coeffs_of_x_ne_n; auto; ring.
    - clear IHn.
      induction n using Induction.
      + unfold sum.
        rewrite iterate_succ, iterate_0; auto using le_refl.
        repeat destruct excluded_middle_informative; try tauto.
        * now contradiction (PA4 0).
        * ring.
      + rewrite sum_succ; auto using zero_le.
        destruct excluded_middle_informative;
          try now contradiction (neq_succ (S n)).
        ring_simplify.
        rewrite <-IHn, ? sum_succ, rings.A1 at 1; auto using zero_le.
        repeat destruct excluded_middle_informative; try tauto;
          try now contradiction (neq_succ n).
        assert (∀ m, sum Ring (λ k, if excluded_middle_informative (k = S m)
                                 then 1%R else 0%R) 0 m = 0%R) as H.
        { clear.
          intros m.
          replace 0%R with (sum _ (λ k, 0%R) 0 m) at 1.
          - apply iterate_extensionality.
            intros k [H H0].
            destruct excluded_middle_informative; auto.
            subst.
            rewrite naturals.le_not_gt in H0.
            contradict H0.
            apply naturals.succ_lt.
          - induction m using Induction.
            + unfold sum.
              now rewrite iterate_0.
            + rewrite sum_succ, IHm, rings.A3; auto using zero_le. }
        f_equal; auto.
        destruct (classic (n = 0%N)) as [H0 | H0]; subst.
        * unfold sum.
          rewrite iterate_0.
          destruct excluded_middle_informative; tauto.
        * apply succ_0 in H0 as [m H0].
          subst.
          rewrite sum_succ, H, rings.A3; auto using zero_le.
          destruct excluded_middle_informative; tauto.
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
    destruct (classic (f - IRP (coefficient f (degree f)) *
                           x ^ degree f = 0)) as [H0 | H0].
    { rewrite H0.
      unfold degree at 1.
      destruct excluded_middle_informative; try now contradict n.
      destruct H as [c H].
      rewrite <-H, naturals.add_comm, sub_abba.
      apply naturals.zero_le. }
    apply degree_bound; auto.
    intros m H1.
    rewrite (sub_is_neg (polynomial_ring Ring)),
    coefficient_add, coefficient_neg, const_coeff_mul in *.
    destruct (classic (m = degree f)); subst.
    - rewrite coeffs_of_x_to_n; auto.
      now ring_simplify.
    - rewrite coeffs_of_x_ne_n; auto.
      ring_simplify.
      rewrite coeffs_above_degree; auto.
      destruct H1 as [[c H1] H3], H as [d H].
      rewrite <-H1, <-H, naturals.lt_def in *.
      exists (c-1)%N.
      rewrite (naturals.add_comm 1), <-naturals.add_assoc,
      sub_abab, sub_abba in *.
      + split; auto.
        contradict H2.
        symmetry in H2.
        apply sub_0_le in H2.
        f_equal.
        apply NNPP.
        intros H4.
        rewrite (lt_1_eq_0 c), add_0_r in H3; repeat split; auto.
      + apply naturals.le_not_gt.
        contradict H3.
        apply lt_1_eq_0 in H3.
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
      apply IPS_eq, power_series_extensionality, functional_extensionality.
      intros n.
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
        * now replace (coefficient f (S d) * 0)%R with 0%R by ring.
        * intros H3.
          rewrite H3, naturals.le_not_gt in H2.
          contradict H2.
          apply naturals.succ_lt.
    - rewrite <-(rings.A3 _ f), rings.A1, sum_succ at 1; auto using zero_le.
      f_equal.
      + apply IHd.
        destruct H as [c H].
        assert (c ≠ 0%N) as H1.
        { contradict H0.
          subst.
          now rewrite naturals.add_0_r in H. }
        apply succ_0 in H1 as [k H1].
        subst.
        exists k.
        apply PA5.
        now rewrite <-add_succ_r.
      + rewrite coeffs_above_degree; repeat split; auto.
        replace (IRP 0%R) with 0 by now apply set_proj_injective.
        ring.
  Qed.

  Theorem degree_of_sum : ∀ d (a : N → R),
      (degree (sum PR (λ n, (a n : polynomial) * x^n)%poly 0 d) ≤ d)%N.
  Proof.
    intros d a.
    destruct (classic (sum _ (λ n : N, (a n : polynomial) * x ^ n) 0 d = 0))
      as [H | H].
    - rewrite H.
      unfold degree.
      destruct excluded_middle_informative;
        auto using naturals.zero_le; now contradict n.
    - apply degree_bound; auto.
      intros m H0.
      clear H.
      induction d using Induction.
      + unfold sum.
        rewrite iterate_0, const_coeff_mul, coeffs_of_x_ne_n;
          try now ring_simplify.
        intros H.
        subst.
        contradiction (naturals.lt_irrefl 0).
      + rewrite sum_succ, coefficient_add, IHd; auto using zero_le.
        * rewrite rings.A3, const_coeff_mul, coeffs_of_x_ne_n;
            try now ring_simplify.
          intros H.
          rewrite H in H0.
          contradiction (naturals.lt_irrefl (S d)).
        * eauto using naturals.lt_trans, naturals.succ_lt.
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
    replace (a k) with (sum _ (λ n, (if (excluded_middle_informative (n = k))
                                     then (a k) else 0%R)) 0 d).
    - apply iterate_extensionality.
      intros z H0.
      destruct excluded_middle_informative.
      + subst.
        rewrite const_coeff_mul, coeffs_of_x_to_n.
        ring.
      + rewrite const_coeff_mul, coeffs_of_x_ne_n; auto; ring.
    - induction d using Induction.
      + unfold sum.
        rewrite iterate_0.
        destruct excluded_middle_informative; auto.
        contradict n.
        apply naturals.le_antisymm.
        split; auto using zero_le.
      + destruct (classic (k ≤ d)%N) as [H0 | H0].
        * rewrite sum_succ, IHd; auto using zero_le.
          destruct excluded_middle_informative; try ring.
          subst.
          rewrite naturals.le_not_gt in H0.
          contradict H0.
          auto using naturals.succ_lt.
        * apply naturals.lt_not_ge in H0 as [[c1 H0] H1].
          destruct H as [c2 H].
          rewrite <-H0, <-add_1_r, <-naturals.add_assoc in H.
          pose proof H as H2.
          apply naturals.cancellation_add, cancellation_1_add in H2
            as [H2 | H2]; subst.
          -- contradict H1.
             ring.
          -- apply naturals.cancellation_add in H.
             ring_simplify in H.
             subst.
             rewrite sum_succ; auto using zero_le.
             rewrite <-(rings.A3 _ (a (d + 1)%N)) at 1.
             f_equal.
             ++ rewrite <-(sum_of_0 _ d) at 1.
                apply iterate_extensionality.
                intros k H.
                destruct excluded_middle_informative; auto.
                subst.
                destruct H as [H H0].
                rewrite naturals.le_not_gt, add_1_r in H0.
                contradict H0.
                apply naturals.succ_lt.
             ++ destruct excluded_middle_informative; auto.
                contradict n.
                now rewrite add_1_r.
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

  Theorem mul_degree : ∀ f g, (degree (f * g)%poly ≤ degree f + degree g)%N.
  Proof.
    intros f g.
    destruct (classic (f * g = 0)) as [H | H].
    { rewrite H.
      unfold degree at 1.
      destruct excluded_middle_informative; try now intuition.
      apply zero_le. }
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

  Theorem binomial_theorem_zero :
    ∀ n, coefficient ((1 + x)^n) 0 = (INR _ (binomial n 0)).
  Proof.
    intros n.
    induction n using Induction.
    - subst.
      rewrite rings.pow_0_r, <-(rings.pow_0_r _ x), coeffs_of_x_to_n,
      binomial_zero.
      unfold INR, sum.
      now rewrite iterate_0.
    - rewrite pow_succ_r, D1_l, coefficient_add, rings.M1, rings.M3, IHn.
      rewrite <-(rings.pow_1_r _ x) at 2.
      rewrite coeff_of_x_mul_overflow, ? binomial_zero;
          eauto using naturals.succ_lt.
      now ring_simplify.
  Qed.

  Theorem binomial_theorem :
    ∀ n k, coefficient ((1 + x)^n) k = (INR _ (binomial n k)).
  Proof.
    intros n k.
    revert k.
    induction n using Induction; intros k.
    { destruct (classic (k = 0%N)) as [H | H].
      - subst.
        apply binomial_theorem_zero.
      - rewrite rings.pow_0_r, <-(rings.pow_0_r _ x),
        coeffs_of_x_ne_n, binomial_empty_set; auto.
        unfold INR, sum, iterate_with_bounds.
        destruct excluded_middle_informative; auto.
        exfalso.
        apply naturals.le_not_gt in l.
        eauto using naturals.succ_lt. }
    destruct (classic (k = 0%N)).
    { subst.
      apply binomial_theorem_zero. }
    assert (1 ≤ k)%N as H0.
    { apply succ_0 in H as [m H].
      exists m.
      now rewrite naturals.add_comm, add_1_r. }
    rewrite pow_succ_r, D1_l, rings.M1, rings.M3, coefficient_add, IHn;
      auto using zero_le, naturals.succ_lt.
    rewrite <-(rings.pow_1_r _ x) at 2.
    rewrite coeff_of_x_mul, IHn, <-add_1_r, <-INR_add, Pascal's_identity; auto.
  Qed.

  Theorem binomial_sum : ∀ n,
      (1 + x)^n =
      sum _ (λ k, ((INR _ (binomial n k) : R) : polynomial) * x^k) 0 n.
  Proof.
    intros n.
    destruct (classic (1%R = 0%R)) as [H | H].
    { assert (∀ f, f = 0) as H0; try now rewrite H0.
      intros f.
      replace f with (IRP (1%R) * f).
      - rewrite H.
        replace (IRP (0%R)) with 0 by now apply set_proj_injective.
        ring.
      - replace (IRP 1%R) with 1; try ring.
        apply set_proj_injective.
        simpl.
        unfold sub_one.
        destruct (polynomials_are_subring Ring).
        repeat destruct a.
        now simpl. }
    rewrite (polynomial_sum_lemma n ((1+x)^n)).
    { apply iterate_extensionality.
      intros k H0.
      f_equal.
      now rewrite binomial_theorem. }
    induction n using Induction.
    - rewrite rings.pow_0_r.
      apply degree_bound.
      + intros H0.
        assert (coefficient 1 0 = coefficient 0 0) as H1 by congruence.
        unfold IRP, coefficient, IPS in H1.
        simpl in H1.
        rewrite <-sub_one_is_one, <-sub_zero_is_zero in H1.
        simpl in H1.
        unfold power_series.zero, power_series.one, power_series.IRS in H1.
        rewrite ? coefficient_seriesify in H1.
        repeat destruct excluded_middle_informative; auto.
      + intros m H0.
        rewrite <-(rings.pow_0_r _ x), coeffs_of_x_ne_n; auto.
        intros H1.
        subst.
        contradiction (naturals.lt_irrefl 0).
    - rewrite pow_succ_r, <-add_1_r.
      pose proof mul_degree ((1+x)^n) (1+x) as H0.
      eapply naturals.le_trans; eauto.
      apply naturals.le_cross_add; auto.
      apply degree_bound.
      + contradict H.
        assert (coefficient (1+x) 0 = coefficient 0 0) as H1 by congruence.
        rewrite coefficient_add, <-(rings.pow_1_r _ x),
        coeffs_of_x_ne_n in H1; auto using (neq_succ 0).
        ring_simplify in H1.
        unfold IRP, coefficient, IPS in H1.
        simpl in H1.
        rewrite <-sub_one_is_one, <-sub_zero_is_zero in H1.
        simpl in H1.
        unfold power_series.zero, power_series.one, power_series.IRS in H1.
        rewrite ? coefficient_seriesify in H1.
        now repeat destruct excluded_middle_informative; auto.
      + intros m H1.
        rewrite coefficient_add, <-(rings.pow_1_r _ x),
        <-(rings.pow_0_r _ x), ? coeffs_of_x_ne_n; try (now ring_simplify);
          intros H2; subst.
        * contradiction (naturals.lt_irrefl 1).
        * apply naturals.lt_not_ge in H1.
          contradict H1.
          apply zero_le.
  Qed.

End Polynomial_theorems.
