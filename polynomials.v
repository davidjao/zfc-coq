Set Warnings "-notation-overridden,-uniform-inheritance,-ambiguous-paths".
Require Export sets power_series combinatorics.

Section Polynomials_construction.

  Variable ring : rings.ring.

  Declare Scope R_scope.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with ring.
  Declare Scope Series_scope.
  Delimit Scope Series_scope with series.
  Bind Scope Series_scope with power_series.
  Open Scope R_scope.
  Notation R := (elts (Rset ring)).
  Infix "+" := (rings.add ring) : R_scope.
  Infix "*" := (rings.mul ring) : R_scope.
  Notation "- a" := (rings.neg ring a) : R_scope.
  Infix "+" := (power_series.add ring) : Series_scope.
  Infix "*" := (power_series.mul ring) : Series_scope.
  Notation "0" := (rings.zero ring) : R_scope.
  Notation "1" := (rings.one ring) : R_scope.
  Notation "0" := (power_series.zero ring) : Series_scope.
  Notation "1" := (power_series.one ring) : Series_scope.
  Notation "- a" := (power_series.neg ring a) : Series_scope.

  Add Ring generic_ring : (ringify ring).

  Definition polynomial_set :=
    {f of type power_series_set ring |
      ∃ n : N, ∀ m, (n ≤ m)%N → coefficient _ f m = 0}.

  Theorem polynomials_are_subset :
    polynomial_set ⊂ Rset (power_series_ring ring).
  Proof.
    intros f H.
    now apply Specify_classification in H as [H H0].
  Qed.

  Theorem polynomials_are_subring :
    is_subring (power_series_ring ring) polynomial_set.
  Proof.
    repeat split.
    - intros [a A] [b B] H H0.
      apply Specify_classification in H as [_ H].
      apply Specify_classification in H0 as [_ H0].
      apply Specify_classification.
      rewrite <-specify_action in *; destruct H as [n H], H0 as [m H0].
      simpl in *.
      split; eauto using elts_in_set.
      exists (naturals.max m n).
      intros x H1; rewrite coefficient_add, H, H0;
        eauto using rings.A3, naturals.le_trans,
        naturals.max_le_l, naturals.max_le_r.
    - intros [a A] [b B] H H0.
      apply Specify_classification in H as [_ H].
      apply Specify_classification in H0 as [_ H0].
      apply Specify_classification.
      rewrite <-specify_action in *; destruct H as [n H], H0 as [m H0].
      simpl in *.
      split; eauto using elts_in_set.
      exists (n + m)%N.
      intros x H1.
      rewrite coefficient_mul, <-(sum_of_0 _ x).
      apply iterate_extensionality.
      intros k H3.
      destruct (classic (n ≤ k)%N).
      + rewrite H; auto; now ring_simplify.
      + rewrite H0, mul_0_r; auto.
        apply NNPP.
        intros H4.
        rewrite <-naturals.lt_not_ge in H2, H4.
        eapply naturals.lt_cross_add in H2; eauto.
        rewrite naturals.add_comm, sub_abab, naturals.lt_not_ge,
        naturals.add_comm in H2; intuition.
    - intros [a A] H.
      apply Specify_classification in H as [_ H].
      apply Specify_classification.
      rewrite <-specify_action in *; destruct H as [n H].
      simpl in *.
      split; eauto using elts_in_set.
      exists n.
      intros x H0.
      rewrite coefficient_neg, H; auto; ring.
    - apply Specify_classification.
      split; eauto using elts_in_set.
      rewrite <-specify_action.
      exists 1%N.
      intros m H.
      simpl.
      unfold power_series.one, power_series.IRS.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative; subst; auto.
      apply naturals.le_not_gt in H.
      contradict H.
      apply naturals.succ_lt.
  Qed.

  Definition polynomial_ring :=
    subring _ polynomial_set polynomials_are_subset polynomials_are_subring.

  Notation poly := (elts (Rset polynomial_ring)).

  Declare Scope Poly_scope.
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
    ∀ c : R, (power_series.IRS _ c) ∈ polynomial_set.
  Proof.
    intros c.
    apply Specify_classification.
    split; eauto using elts_in_set.
    unfold ISS, power_series.IRS.
    rewrite <-specify_action.
    exists 1%N.
    intros m H.
    rewrite coefficient_seriesify.
    destruct excluded_middle_informative; auto.
    subst.
    apply naturals.le_not_gt in H.
    contradict H.
    apply naturals.succ_lt.
  Qed.

  Notation PS := (power_series ring).

  Theorem x_is_poly : x ring ∈ polynomial_set.
  Proof.
    apply Specify_classification.
    split; eauto using elts_in_set.
    unfold ISS, x, shift, power_series.one, power_series.IRS.
    rewrite <-specify_action.
    exists 2%N.
    intros m [c H].
    rewrite ? coefficient_seriesify.
    repeat destruct excluded_middle_informative; auto.
    apply sub_0_le in e as [d H0].
    subst.
    rewrite <-(add_0_r 1), <-add_1_r, <-? naturals.add_assoc in H0.
    apply naturals.cancellation_add in H0.
    rewrite add_0_l, naturals.add_comm, add_1_r in H0.
    now contradiction (PA4 (c+d)).
  Qed.

End Polynomials_construction.

Section Polynomial_theorems.

  Variable ring : rings.ring.
  Definition R := elts (Rset ring).
  Notation SR := (power_series_ring ring).
  Notation PR := (polynomial_ring ring).
  Definition series := elts (Rset SR).
  Definition poly := elts (Rset PR).
  Definition IPS :=
    ISR (power_series_ring _) (polynomial_set _)
        (polynomials_are_subset _) : poly → series.
  Definition IRS := (power_series.IRS _) : R → series.
  Definition IRs := rings.IRS ring : R → set.
  Coercion IPS : poly >-> series.
  Coercion IRs : R >-> set.

  Declare Scope R_scope.
  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Declare Scope Series_scope.
  Delimit Scope Series_scope with series.
  Bind Scope Series_scope with series.
  Declare Scope Poly_scope.
  Delimit Scope Poly_scope with poly.
  Bind Scope Poly_scope with poly.

  Open Scope R_scope.
  Infix "+" := (rings.add ring) : R_scope.
  Notation "a + b" := (rings.add _ (a : R) (b : R) : R) : R_scope.
  Infix "*" := (rings.mul ring) : R_scope.
  Notation "a * b" := (rings.mul _ (a : R) (b : R) : R) : R_scope.
  Infix "-" := (rings.sub ring) : R_scope.
  Notation "a - b" := (rings.sub _ (a : R) (b : R) : R) : R_scope.
  Notation "- a" := (rings.neg ring a) : R_scope.
  Notation "- a" := (rings.neg _ (a : R) : R) : R_scope.
  Infix "^" := (rings.pow ring) : R_scope.
  Notation "a ^ b" := (rings.pow _ (a : R) (b : N) : R) : R_scope.
  Notation "0" := (rings.zero ring) : R_scope.
  Notation "0" := (rings.zero _ : R) : R_scope.
  Notation "1" := (rings.one ring) : R_scope.
  Notation "1" := (rings.one _ : R) : R_scope.
  Add Ring base_ring : (ringify _ : ring_theory 0 _ _ _ _ _ eq).
  Add Ring base_ring_raw : (ringify ring).

  Open Scope Series_scope.
  Infix "+" := (rings.add SR) : Series_scope.
  Notation "a + b" := (rings.add _ (a:series) (b:series):series) : Series_scope.
  Infix "*" := (rings.mul SR) : Series_scope.
  Notation "a * b" := (rings.mul _ (a:series) (b:series):series) : Series_scope.
  Infix "-" := (rings.sub SR) : Series_scope.
  Notation "a - b" := (rings.sub _ (a:series) (b:series):series) : Series_scope.
  Notation "- a" := (rings.neg SR a) : Series_scope.
  Notation "- a" := (rings.neg _ (a:series) : series) : Series_scope.
  Infix "^" := (rings.pow SR) : Series_scope.
  Notation "a ^ b" := (rings.pow _ (a:series) (b : N) : series) : Series_scope.
  Notation "0" := (rings.zero SR) : Series_scope.
  Notation "0" := (rings.zero _ : series) : Series_scope.
  Notation "1" := (rings.one SR) : Series_scope.
  Notation "1" := (rings.one _ : series) : Series_scope.
  Add Ring series_ring : (ringify _ : ring_theory 0 _ _ _ _ _ eq).
  Add Ring series_ring_raw : (ringify SR).

  Open Scope Poly_scope.
  Infix "+" := (rings.add PR) : Poly_scope.
  Notation "a + b" := (rings.add _ (a : poly) (b : poly) : poly) : Poly_scope.
  Infix "*" := (rings.mul PR) : Poly_scope.
  Notation "a * b" := (rings.mul _ (a : poly) (b : poly) : poly) : Poly_scope.
  Infix "-" := (rings.sub PR) : Poly_scope.
  Notation "a - b" := (rings.sub _ (a : poly) (b : poly) : poly) : Poly_scope.
  Notation "- a" := (rings.neg PR a) : Poly_scope.
  Notation "- a" := (rings.neg _ (a : poly) : poly) : Poly_scope.
  Infix "^" := (rings.pow PR) : Poly_scope.
  Notation "a ^ b" := (rings.pow _ (a : poly) (b : N) : poly) : Poly_scope.
  Notation "0" := (rings.zero PR) : Poly_scope.
  Notation "0" := (rings.zero _ : poly) : Poly_scope.
  Notation "1" := (rings.one PR) : Poly_scope.
  Notation "1" := (rings.one _ : poly) : Poly_scope.
  Add Ring poly_ring : (ringify _ : ring_theory 0 _ _ _ _ _ eq).
  Add Ring poly_ring_raw : (ringify PR).

  Definition IRP (c : R) := (exist _ _ (consts_are_polys _ c)) : poly.
  Coercion IRP : R >-> poly.

  Definition coefficient (f : poly) n := coefficient _ (f : series) n : R.
  Definition x := (exist _ _ (x_is_poly _)) : poly.

  Theorem IPS_eq : ∀ f g : poly, (f : series) = (g : series) ↔ f = g.
  Proof.
    intros f g.
    split; intros H; try congruence.
    now apply ISR_eq in H.
  Qed.

  Theorem IPS_add : ∀ f g : poly, ((f : series) + (g : series))%series = f + g.
  Proof.
    intros f g.
    now apply set_proj_injective.
  Qed.

  Theorem IPS_neg : ∀ f : poly, (-f : series)%series = -f.
  Proof.
    intros f.
    now apply set_proj_injective.
  Qed.

  Theorem IPS_mul : ∀ f g : poly, ((f : series) * (g : series))%series = f * g.
  Proof.
    intros f g.
    now apply set_proj_injective.
  Qed.

  Theorem IRP_eq : ∀ a b : R, (a : poly) = (b : poly) ↔ a = b.
  Proof.
    intros a b.
    split; intros H; try congruence.
    inversion H.
    apply set_proj_injective in H1.
    now apply IRS_eq.
  Qed.

  Theorem IRP_add : ∀ a b : R, (a : poly) + (b : poly) = (a + b)%R.
  Proof.
    intros a b.
    unfold IRP; apply set_proj_injective; simpl.
    rewrite (IRS_add _).
    unfold ISR, rings.IRS, ISS.
    simpl.
    do 2 f_equal; now apply set_proj_injective.
  Qed.

  Theorem IRP_mul : ∀ a b : R, (a : poly) * (b : poly) = (a * b)%R.
  Proof.
    intros a b.
    unfold IRP; apply set_proj_injective; simpl.
    rewrite (IRS_mul _).
    unfold ISR, rings.IRS, ISS.
    simpl.
    do 2 f_equal; now apply set_proj_injective.
  Qed.

  Theorem IRP_neg : ∀ a : R, (-a : poly) = (-a)%R.
  Proof.
    intros a.
    unfold IRP; apply set_proj_injective; simpl.
    rewrite (IRS_neg _).
    unfold ISR, rings.IRS, ISS.
    simpl.
    do 2 f_equal; now apply set_proj_injective.
  Qed.

  Theorem IRP_1 : 1 = 1%R.
  Proof.
    apply set_proj_injective.
    simpl.
    now destruct polynomials_are_subring, a.
  Qed.

  Theorem IRP_pow : ∀ (n : N) (a : R), (a : poly)^n = (a^n)%R.
  Proof.
    induction n using Induction; intros a;
      now rewrite ? rings.pow_0_r, ? IRP_1,
      ? rings.pow_succ_r, ? IHn, ? IRP_mul.
  Qed.

  Theorem nonzero_coefficients : ∀ f, f ≠ 0 ↔ ∃ m, coefficient f m ≠ 0%R.
  Proof.
    intros f.
    split; intros H.
    - apply NNPP.
      contradict H.
      apply IPS_eq, power_series_extensionality.
      simpl in *.
      unfold IPS.
      rewrite <-sub_zero_is_zero.
      extensionality n.
      simpl.
      unfold power_series.zero, IRS, power_series.IRS.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative; apply NNPP; contradict H; eauto.
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

  Theorem degree_construction :
    ∀ f, f ≠ 0 →
         ∃ m, coefficient f m ≠ 0%R ∧ ∀ n, (m < n)%N → coefficient f n = 0%R.
  Proof.
    intros f H.
    apply nonzero_coefficients in H as [m H].
    pose proof (elts_in_set _ f) as H0; simpl in *.
    apply Specify_classification in H0 as [H0 H1].
    rewrite <-(setify_action _ _ H0), <-specify_action in *.
    destruct H1 as [n H1].
    destruct (lub (λ x, coefficient f x ≠ 0%R)) as [s [H2 H3]];
      try now (exists m).
    { exists n.
      intros x H3.
      apply naturals.le_not_gt.
      contradict H3.
      unfold coefficient.
      rewrite <-(H1 x); try (f_equal; now apply set_proj_injective).
      now destruct H3. }
    exists s.
    split; auto.
    intros x [H4 H5].
    apply NNPP.
    contradict H5.
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

  Theorem degree_zero : degree 0 = 0%N.
  Proof.
    unfold degree.
    destruct excluded_middle_informative; auto; exfalso; auto.
  Qed.

  Theorem degree_spec : ∀ f m,
      f ≠ 0 → degree f = m ↔ (coefficient f m ≠ 0%R ∧
                              ∀ n, (m < n)%N → coefficient f n = 0%R).
  Proof.
    intros f m H.
    split; intros H0; unfold degree in *;
      destruct excluded_middle_informative; try tauto;
        destruct constructive_indefinite_description as [y]; subst; auto.
    destruct H0 as [H0 H1], a as [H2 H3], (lt_trichotomy y m)
          as [H4 | [H4 | H4]]; auto; exfalso; auto.
  Qed.

  Lemma coeffs_of_x : ∀ n : N, n ≠ 1%N → coefficient x n = 0%R.
  Proof.
    intros n H.
    unfold IPS, x, ISR, ISS.
    simpl in *.
    replace 0%R with (power_series.coefficient _ (power_series.x ring) n).
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
    replace 1%R with (power_series.coefficient _ (power_series.x ring) 1).
    { unfold coefficient.
      f_equal.
      now apply set_proj_injective. }
    unfold power_series.x, shift, power_series.one, IRS, power_series.IRS.
    rewrite ? coefficient_seriesify.
    repeat destruct excluded_middle_informative; auto.
    - now contradiction (PA4 0).
    - now rewrite sub_diag in n0.
  Qed.

  Lemma IPS_pow : ∀ n (f : poly), ((f : series)^n)%series = f^n.
  Proof.
    induction n using Induction; intros f.
    - rewrite ? (rings.pow_0_r PR), ? (rings.pow_0_r SR).
      apply sub_one_is_one.
    - now rewrite ? (pow_succ_r PR), ? (pow_succ_r SR), <-IPS_mul, IHn in *.
  Qed.

  Lemma coeffs_of_x_ne_n : ∀ m n, m ≠ n → coefficient (x^n) m = 0%R.
  Proof.
    intros m n H.
    revert m H.
    induction n using Induction; intros m H.
    { rewrite rings.pow_0_r.
      unfold coefficient, IPS; simpl.
      rewrite <-sub_one_is_one.
      simpl.
      unfold power_series.one, IRS, power_series.IRS, coefficient.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative; tauto. }
    unfold coefficient in *.
    rewrite pow_succ_r, <-IPS_mul, <-IPS_pow in *.
    simpl.
    unfold power_series.mul.
    rewrite coefficient_seriesify, <-(sum_of_0 _ m).
    apply iterate_extensionality.
    intros k [H0 [c H1]].
    destruct (classic (n = k)).
    - subst.
      fold (coefficient x (k+c-k)).
      rewrite coeffs_of_x; try now ring_simplify.
      contradict H.
      rewrite naturals.add_comm, sub_abba, <-add_1_r in *.
      ring [H].
    - rewrite IHn; auto; now ring_simplify.
  Qed.

  Lemma degree_bound : ∀ n f,
      ((∀ m : N, n < m → coefficient f m = 0%R) → degree f ≤ n)%N.
  Proof.
    intros n f H.
    unfold degree.
    destruct excluded_middle_informative; auto using zero_le.
    destruct constructive_indefinite_description as [d [H1 H2]].
    apply naturals.le_not_gt.
    contradict H1.
    auto.
  Qed.

  Lemma coeffs_above_degree : ∀ n f, (degree f < n)%N → coefficient f n = 0%R.
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

  Lemma IPS_IRP : ∀ c : R, (c : series) = IRS c.
  Proof.
    intros c.
    now apply set_proj_injective.
  Qed.

  Lemma const_coeff_mul :
    ∀ n f (c : R), coefficient (c * f) n = (c * coefficient f n)%R.
  Proof.
    intros n f c.
    unfold coefficient.
    now rewrite <-power_series.const_coeff_mul, <-IPS_mul, IPS_IRP.
  Qed.

  Lemma coeffs_of_x_to_n : ∀ n, coefficient (x^n) n = 1%R.
  Proof.
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
    rewrite coefficient_seriesify, <-(singleton_sum _ n (S n) 1%R);
      auto using le_succ.
    apply iterate_extensionality.
    intros k [H0 [c H1]].
    destruct excluded_middle_informative.
    - subst.
      rewrite <-IHn, <-add_1_r, naturals.add_comm, sub_abba.
      fold IPS (coefficient x 1).
      now rewrite x_coeff_of_x; ring_simplify.
    - fold IPS (coefficient (x^n) k).
      rewrite coeffs_of_x_ne_n; auto; now ring_simplify.
  Qed.

  Theorem coefficient_add : ∀ n f g,
      coefficient (f + g) n = (coefficient f n + coefficient g n)%R.
  Proof.
    intros n f g.
    unfold coefficient.
    now rewrite <-IPS_add, <-power_series.coefficient_add.
  Qed.

  Theorem coefficient_neg : ∀ n f, coefficient (-f) n = (- coefficient f n)%R.
  Proof.
    intros n f.
    unfold coefficient.
    now rewrite <-IPS_neg, <-power_series.coefficient_neg.
  Qed.

  Theorem coefficient_mul : ∀ n f g,
      coefficient (f * g) n =
      sum _ (λ k, (coefficient f k * coefficient g (n-k))%R) 0 n.
  Proof.
    intros n f g.
    unfold coefficient.
    now rewrite <-IPS_mul, <-power_series.coefficient_mul.
  Qed.

  Lemma minus_leading_term : ∀ f,
      (1 ≤ degree f → degree (f - (coefficient f (degree f)) *
                                  x^(degree f))%poly ≤ degree f - 1)%N.
  Proof.
    intros f H.
    apply degree_bound.
    intros m H0.
    rewrite (sub_is_neg (polynomial_ring _)),
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
        apply eq_sym, sub_0_le in H1.
        apply f_equal, NNPP.
        contradict H2.
        rewrite (lt_1_eq_0 c), add_0_r; repeat split; auto.
      + apply naturals.le_not_gt.
        contradict H2.
        rewrite (lt_1_eq_0 c); auto; ring.
  Qed.

  Lemma polynomial_sum_lemma : ∀ d : N, ∀ f,
        (degree f ≤ d)%N → f = sum PR (λ n, coefficient f n * x^n) 0 d.
  Proof.
    intros d.
    induction d using Induction.
    { intros f [c H].
      assert (degree f = 0%N) as H0.
      { apply naturals.cancellation_0_add in H; tauto. }
      rewrite sum_0.
      apply IPS_eq, power_series_extensionality.
      extensionality n.
      fold (coefficient f n) (coefficient (coefficient f 0 * x ^ 0) n).
      destruct (classic (n = 0%N)) as [H1 | H1].
      - subst.
        now rewrite const_coeff_mul, coeffs_of_x_to_n; ring_simplify.
      - rewrite const_coeff_mul, coeffs_of_x_ne_n, coeffs_above_degree;
          auto; try ring.
        rewrite H0, naturals.lt_def.
        eauto using naturals.add_0_l. }
    intros f H.
    destruct (classic (degree f = S d)) as [H0 | H0].
    - rewrite sum_succ, <-(rings.A3 _ f), (rings.A1 _ 0),
      <-(rings.A4 _ (coefficient f (S d) * x ^ S d)),
      (rings.A1 _ (coefficient f (S d) * x ^ S d)),
      rings.A2 at 1; auto using zero_le.
      f_equal.
      rewrite <-sub_is_neg, (IHd (f - (coefficient f (S d) * x ^ S d))).
      2: { replace d with (S d - 1)%N at 3.
           - rewrite <-H0.
             apply minus_leading_term.
             rewrite H0.
             apply (succ_le _ d), zero_le.
           - now rewrite <-add_1_r, sub_abba. }
      apply iterate_extensionality.
      intros k [H1 H2].
      rewrite sub_is_neg, coefficient_add, coefficient_neg.
      replace (coefficient (coefficient f (S d) * x ^ S d) k) with 0%R.
      + now rewrite <-neg_0, rings.A1, rings.A3.
      + rewrite const_coeff_mul, coeffs_of_x_ne_n, mul_0_r; auto.
        intros H3.
        rewrite H3, naturals.le_not_gt in H2.
        contradict H2.
        apply naturals.succ_lt.
    - rewrite <-(rings.A3 _ f), rings.A1, sum_succ at 1; auto using zero_le.
      f_equal.
      + apply IHd, naturals.le_not_gt.
        contradict H0.
        eauto using squeeze_upper.
      + rewrite coeffs_above_degree; repeat split; auto.
        replace (0%R : poly) with 0 by now apply set_proj_injective.
        ring.
  Qed.

  Theorem degree_of_sum : ∀ d (a : N → R),
      (degree (sum PR (λ n, a n * x^n)%poly 0 d) ≤ d)%N.
  Proof.
    intros d a.
    apply degree_bound; auto.
    intros m H.
    induction d using Induction.
    - rewrite sum_0, const_coeff_mul, coeffs_of_x_ne_n;
        try now ring_simplify.
      intros H0.
      subst.
      contradiction (naturals.lt_irrefl 0).
    - rewrite sum_succ, coefficient_add, IHd, rings.A3, const_coeff_mul,
      coeffs_of_x_ne_n; eauto using zero_le, naturals.lt_trans,
                        naturals.succ_lt; try now ring_simplify.
      intros H0.
      subst.
      contradiction (naturals.lt_irrefl (S d)).
  Qed.

  Theorem coefficient_sum_add : ∀ d a k,
      coefficient (sum _ (λ n, a n) 0 d) k =
      sum _ (λ n, (coefficient (a n) k)) 0 d.
  Proof.
    intros d a k.
    induction d using Induction.
    - now rewrite ? sum_0.
    - rewrite ? sum_succ, <-IHd, coefficient_add; auto using zero_le.
  Qed.

  Theorem coefficient_extraction : ∀ d k (a : N → R),
      (k ≤ d)%N → coefficient (sum _ (λ n, a n * x^n) 0 d) k = (a k).
  Proof.
    intros d k a H.
    rewrite coefficient_sum_add, <-(singleton_sum _ k d (a k)); auto.
    apply iterate_extensionality.
    intros z H0.
    destruct excluded_middle_informative.
    - rewrite e, const_coeff_mul, coeffs_of_x_to_n.
      now ring_simplify.
    - rewrite const_coeff_mul, coeffs_of_x_ne_n; auto; now ring_simplify.
  Qed.

  Theorem coeff_of_x_mul : ∀ n k f,
      (k ≤ n)%N → coefficient (f * x^k) n = coefficient f (n-k).
  Proof.
    intros n k f H.
    revert n H.
    induction k using Induction; intros n [c H]; subst;
      try now rewrite rings.pow_0_r, sub_0_r, M3_r.
    destruct (classic (k ≤ (S k + c))%N) as [H0 | H0].
    - unfold coefficient.
      rewrite pow_succ_r, rings.M2, rings.M1, <-IPS_mul.
      replace (x : series) with (power_series.x ring)
        by now apply set_proj_injective.
      simpl.
      rewrite mul_x_shift.
      unfold shift.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative.
      { rewrite naturals.add_comm, add_succ_r in e.
        now contradiction (PA4 (c+k)). }
      pose proof IHk (S k + c - 1)%N as H1.
      unfold coefficient in H1.
      simpl in H1.
      rewrite H1.
      + rewrite (naturals.add_comm _ c), <-add_1_r, naturals.add_assoc,
        ? sub_abba at 1.
        now apply f_equal, sub_spec.
      + exists c.
        apply sub_spec.
        rewrite <-add_1_r; ring.
    - contradict H0.
      exists (1+c)%N.
      rewrite <-add_1_r; ring.
  Qed.

  Theorem add_degree :
    ∀ f g, (degree (f + g)%poly ≤ naturals.max (degree f) (degree g))%N.
  Proof.
    intros f g.
    unfold naturals.max.
    destruct excluded_middle_informative; apply degree_bound; intros m H;
      try apply naturals.le_not_gt in n;
      rewrite coefficient_add, ? coeffs_above_degree, rings.A3;
      eauto using naturals.lt_trans, naturals.le_lt_trans.
  Qed.

  Theorem mul_degree : ∀ f g, (degree (f * g)%poly ≤ degree f + degree g)%N.
  Proof.
    intros f g.
    apply degree_bound; auto.
    intros m H0.
    rewrite coefficient_mul, <-(sum_of_0 _ m).
    apply iterate_extensionality.
    intros k [H1 H2].
    destruct (classic (degree f < k)%N) as [H3 | H3].
    - rewrite coeffs_above_degree; auto; now ring_simplify.
    - rewrite (coeffs_above_degree _ g); try now ring_simplify.
      apply naturals.lt_not_ge.
      contradict H3.
      rewrite naturals.lt_not_ge in *.
      contradict H0.
      rewrite <-(sub_abab k m); auto using naturals.le_cross_add.
  Qed.

  Theorem coeff_of_x_mul_overflow :
    ∀ n k f, (n < k)%N → coefficient (f * x^k) n = 0%R.
  Proof.
    intros n k f H.
    rewrite coefficient_mul, <-(sum_of_0 _ n).
    apply iterate_extensionality.
    intros z [H0 [c H1]].
    rewrite coeffs_of_x_ne_n; try now ring_simplify.
    intros H2.
    subst.
    rewrite naturals.lt_not_ge in H.
    contradict H.
    rewrite (naturals.add_comm z), sub_abba.
    now (exists z).
  Qed.

  Definition eval f a := (sum _ (λ n, (coefficient f n) * a^n)%R 0 (degree f)).

  Coercion eval : poly >-> Funclass.

  Definition roots (f : poly) := {r of type (Rset ring) | f r = 0%R}.

  Theorem roots_in_R : ∀ f a, a ∈ roots f → a ∈ (Rset ring).
  Proof.
    intros f a H.
    apply Specify_classification in H; tauto.
  Qed.

  Theorem roots_action : ∀ f (a : R), a ∈ roots f ↔ f a = 0%R.
  Proof.
    split; assert (a ∈ (Rset ring)) as H
        by eauto using elts_in_set; intros H0;
      [ apply Specify_classification in H0 as [H0 H1] |
        apply Specify_classification ];
      rewrite <-(setify_action _ _ H), <-specify_action, <-? H0, <-? H1 in *;
      eauto using f_equal, set_proj_injective, elts_in_set.
  Qed.

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

  Theorem eval_add : ∀ f g a, (f + g) a = (f a + g a)%R.
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

  Theorem eval_bound : ∀ f a n,
      (degree f ≤ n)%N → sum _ (λ n : N, (coefficient f n * a^n)%R) 0 n = f a.
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
      replace 0 with (0%R * x^0) in e.
      + rewrite <-(coeffs_of_x_to_n k), e, const_coeff_mul.
        now ring_simplify.
      + replace (0%R : poly) with 0 by now apply set_proj_injective.
        now rewrite mul_0_l.
    - destruct constructive_indefinite_description as [d], a as [H0 H1].
      apply NNPP.
      contradict H0.
      rewrite coeffs_of_x_ne_n; auto.
  Qed.

  Lemma degree_const : ∀ c : R, degree c = 0%N.
  Proof.
    intros c.
    apply naturals.le_antisymm; auto using zero_le.
    apply degree_bound.
    intros m H.
    rewrite <-(rings.M3 _ (c : poly)), rings.M1, const_coeff_mul,
    <-(rings.pow_0_r _ x), coeffs_of_x_ne_n, mul_0_r; auto.
    contradict H.
    subst.
    auto using naturals.lt_irrefl.
  Qed.

  Lemma coeff_const : ∀ c : R, coefficient c 0 = c.
  Proof.
    intros c.
    destruct (classic (c = 0%R)) as [H | H]; subst.
    - rewrite <-(rings.M3 _ (IRP 0)), rings.M1, const_coeff_mul.
      now ring_simplify.
    - rewrite <-(rings.M3 _ (c : poly)), rings.M1, const_coeff_mul,
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
        rewrite degree_const, naturals.lt_def.
        eauto using add_0_l.
    - destruct constructive_indefinite_description as [d], a as [H0 H1].
      apply naturals.le_not_gt.
      contradict H; auto.
  Qed.

  Lemma eval_mul_const : ∀ (c α : R) f, (c * f) α = (c * f α)%R.
  Proof.
    intros c α f.
    unfold eval.
    rewrite (sum_beyond_degree (c * f) _ (degree f)).
    - rewrite sum_mul.
      f_equal.
      extensionality n.
      rewrite const_coeff_mul.
      ring.
    - eapply naturals.le_trans; auto using mul_degree.
      rewrite degree_const, add_0_l.
      auto using naturals.le_refl.
  Qed.

  Lemma eval_x_to_n : ∀ n α, ((x^n) α) = (α^n)%R.
  Proof.
    intros n α.
    unfold eval.
    destruct (classic (1%R = 0%R)) as [| H]; auto using zero_ring_degeneracy.
    rewrite degree_x_to_n, <-(singleton_sum _ n n (α^n)%R);
      auto using naturals.le_refl.
    apply iterate_extensionality.
    intros k H0.
    destruct excluded_middle_informative.
    - subst.
      rewrite coeffs_of_x_to_n.
      now ring_simplify.
    - rewrite coeffs_of_x_ne_n; auto; now ring_simplify.
  Qed.

  Lemma eval_x : ∀ α, x α = α.
  Proof.
    intros α.
    now rewrite <-(rings.pow_1_r PR x), eval_x_to_n, rings.pow_1_r.
  Qed.

  Lemma eval_mul_x_lemma : ∀ m (α : R) (f : N → R) n,
      ((sum _ (λ i, f i * x^i) 0 m) * x^n) α =
      ((sum _ (λ i, f i * x^i)%poly 0 m : poly) α * α^n)%R.
  Proof.
    induction m using Induction; intros α f n.
    - rewrite sum_0, rings.pow_0_r, (rings.M1 _ _ 1), rings.M3,
      eval_mul_const, eval_x_to_n.
      f_equal.
      unfold eval.
      now rewrite degree_const, sum_0, rings.pow_0_r, coeff_const,
      rings.M1, rings.M3.
    - rewrite ? sum_succ, rings.D1, ? eval_add, rings.D1, IHm, <-rings.M2,
      ? eval_mul_const, <-rings.M2, <-rings.pow_add_r, ? eval_x_to_n,
      rings.pow_add_r; auto using zero_le.
  Qed.

  Lemma eval_mul_x_f : ∀ f a n, (f * x^n) a = (f a * (x^n)%poly a)%R.
  Proof.
    intros f a n.
    now rewrite (polynomial_sum_lemma (degree f) f), ? eval_mul_x_lemma,
    eval_x_to_n; auto using naturals.le_refl.
  Qed.

  Lemma eval_mul_lemma : ∀ n f (a : N → R) α,
      (f * (sum PR (λ i, (a i) * x^i) 0%N n)) α =
      (f α * sum _ (λ i, (a i) * α^i) 0 n)%R.
  Proof.
    intros n f a α.
    induction n using Induction.
    { now rewrite ? sum_0, ? rings.M2, ? (rings.M1 _ _ (a 0%N : poly)),
      ? (rings.M1 _ _ (a 0%N)), <-? rings.M2, eval_mul_const,
      eval_mul_x_f, eval_x_to_n. }
    rewrite ? sum_succ, ? rings.D1_l, <-IHn, eval_add; auto using zero_le.
    f_equal.
    rewrite <-eval_x_to_n, rings.M1, <-rings.M2, eval_mul_const,
    (rings.M1 _ _ f), eval_mul_x_f.
    ring.
  Qed.

  Theorem eval_mul : ∀ f g a, (f * g) a = (f a * g a)%R.
  Proof.
    intros f g a.
    rewrite (polynomial_sum_lemma (degree g) g), eval_mul_lemma, eval_bound;
      auto using naturals.le_refl.
    do 2 f_equal; try extensionality n;
      rewrite <-polynomial_sum_lemma; auto using naturals.le_refl.
  Qed.

  Definition linear f := degree f = 1%N.

  Theorem linear_classification :
    ∀ f, linear f ↔ ∃ a b : R, f = a + b * x ∧ b ≠ 0%R.
  Proof.
    intros f.
    split; intros H.
    - unfold linear in H.
      rewrite (polynomial_sum_lemma 1 f).
      2: { rewrite H.
           auto using naturals.le_refl. }
      exists (coefficient f 0), (coefficient f 1).
      split.
      + unfold naturals.one.
        rewrite sum_succ, sum_0, rings.pow_0_r; auto using zero_le.
        f_equal; try ring.
        now rewrite rings.pow_1_r.
      + intros H0.
        contradiction (PA4 0).
        fold naturals.one.
        rewrite <-H.
        symmetry.
        apply naturals.le_antisymm; auto using zero_le.
        apply degree_bound.
        intros m [H1 H2].
        apply neq_sym, succ_0 in H2 as [k H2].
        subst.
        destruct (classic ((S k) = 1%N)) as [H2 | H2]; try congruence.
        rewrite coeffs_above_degree; auto.
        rewrite H, naturals.lt_def.
        exists k.
        rewrite naturals.add_comm, naturals.add_1_r.
        split; auto.
        contradict H2.
        now rewrite <-H2.
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
        now ring_simplify in H0.
  Qed.

  Theorem degree_of_a_plus_x :
    1%R ≠ 0%R → ∀ α : R, degree (α + x) = 1%N.
  Proof.
    intros H α.
    apply linear_classification.
    exists α, 1%R.
    rewrite <-IRP_1.
    split; auto; now ring_simplify.
  Qed.

  Definition monic f := (coefficient f (degree f) = 1%R).

  Theorem leading_term_prod : ∀ f g,
      (coefficient f (degree f) * coefficient g (degree g))%R =
      coefficient (f * g) (degree f + degree g)%N.
  Proof.
    intros f g.
    rewrite coefficient_mul,
    <-(singleton_sum _ (degree f) (degree f + degree g)%N
                     (coefficient f (degree f) * coefficient g (degree g))%R);
      try now (exists (degree g)).
    apply iterate_extensionality.
    intros k H.
    destruct (lt_trichotomy k (degree f)) as [H0 | [H0 | H0]];
      destruct excluded_middle_informative; try tauto; subst;
        (try now contradiction (naturals.lt_irrefl (degree f))).
    - rewrite (coeffs_above_degree _ g); try now rewrite mul_0_r.
      destruct H0 as [[c H0] H2].
      rewrite <-H0, <-naturals.add_assoc, naturals.add_comm, sub_abba,
      naturals.add_comm, naturals.lt_def.
      exists c.
      split; auto.
      contradict H2.
      subst.
      ring [H0].
    - now rewrite naturals.add_comm, sub_abba.
    - rewrite coeffs_above_degree; auto; now rewrite mul_0_l.
  Qed.

  Theorem zero_ring_degree : 1%R = 0%R → ∀ f, degree f = 0%N.
  Proof.
    eauto using naturals.le_antisymm, zero_le,
    degree_bound, zero_ring_degeneracy.
  Qed.

  Theorem zero_ring_monic : 1%R = 0%R → ∀ f, monic f.
  Proof.
    intros H f.
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
    now rewrite <-leading_term_prod, H, H0, rings.M3.
  Qed.

  Theorem monic_prod : ∀ f g, monic f → monic g → monic (f * g).
  Proof.
    intros f g H H0.
    unfold monic in *.
    rewrite monic_prod_degree, <-leading_term_prod, H, H0, rings.M3; auto.
  Qed.

  Theorem monic_a_plus_x : ∀ α : R, monic (α + x).
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
    induction n using Induction; intros f H.
    - rewrite rings.pow_0_r.
      unfold monic.
      now rewrite IRP_1, degree_const, coeff_const.
    - rewrite pow_succ_r.
      apply monic_prod; auto.
  Qed.

  Theorem monic_pow_degree : ∀ n f, monic f → degree (f^n) = (n * degree f)%N.
  Proof.
    induction n using Induction; intros f H.
    - now rewrite rings.pow_0_r, IRP_1, degree_const, naturals.mul_0_l.
    - rewrite pow_succ_r, monic_prod_degree, IHn, <-add_1_r;
        auto using monic_powers; ring.
  Qed.

  Theorem degree_of_a_plus_x_to_n :
    1%R ≠ 0%R → ∀ n (α : R), degree ((α + x)^n) = n.
  Proof.
    intros H n α.
    rewrite monic_pow_degree, degree_of_a_plus_x;
      auto using monic_a_plus_x; ring.
  Qed.

  Definition INR := (INR _) : N → R.
  Coercion INR : N >-> R.

  Lemma binomial_theorem_zero :
    ∀ n (α : R), coefficient ((α + x)^n) 0 = (binomial n 0 * α^n)%R.
  Proof.
    induction n using Induction; intros α.
    - subst.
      rewrite ? rings.pow_0_r, <-(rings.pow_0_r _ x), coeffs_of_x_to_n,
      binomial_zero, rings.M1, rings.M3.
      apply eq_sym, sum_0.
    - rewrite pow_succ_r, D1_l, coefficient_add, binomial_zero,
      (rings.M1 _ _ (α : poly)), const_coeff_mul, IHn, <-(rings.pow_1_r _ x),
      coeff_of_x_mul_overflow, binomial_zero, pow_succ_r;
        eauto using naturals.succ_lt.
      now ring_simplify.
  Qed.

  Lemma INR_0 : (0%R : R) = 0%N.
  Proof.
    unfold INR, rings.INR.
    rewrite sum_neg; eauto using naturals.succ_lt.
  Qed.

  Theorem generalized_binomial_theorem :
    ∀ n k (α : R), coefficient ((α + x)^n) k = (binomial n k * α^(n-k))%R.
  Proof.
    induction n using Induction; intros k α.
    { destruct (classic (k = 0%N)) as [H | H].
      - now subst; rewrite binomial_theorem_zero, sub_diag.
      - rewrite rings.pow_0_r, <-(rings.pow_0_r _ x),
        coeffs_of_x_ne_n, binomial_empty_set; auto.
        unfold INR, rings.INR.
        rewrite sum_neg, mul_0_l; eauto using naturals.succ_lt. }
    destruct (classic (k = 0%N)) as [H | H].
    { now subst; rewrite binomial_theorem_zero, sub_0_r. }
    apply succ_0 in H as [c H].
    rewrite pow_succ_r, D1_l, rings.M1, coefficient_add, const_coeff_mul,
    IHn, <-(rings.pow_1_r _ x), coeff_of_x_mul, rings.pow_1_r, IHn,
    (rings.M1 _ α), <-rings.M2.
    2: { exists c; now rewrite H, <-add_1_r, naturals.add_comm. }
    rewrite <-(rings.pow_1_r _ α) at 2.
    rewrite <-rings.pow_add_r.
    subst.
    destruct (classic (n = 0%N)) as [H | H];
      try apply succ_0 in H as [m H]; subst.
    { rewrite binomial_empty_set, sub_0_l, <-INR_0, rings.mul_0_l, rings.A3.
      2: { apply neq_sym, PA4. }
      rewrite sub_succ, ? sub_0_l.
      f_equal.
      destruct (classic (c = 0%N)) as [H | H];
        try apply succ_0 in H as [m H]; subst.
      - fold naturals.one.
        now rewrite sub_diag, binomial_one, binomial_zero.
      - rewrite binomial_empty_set, binomial_overflow; auto.
        + rewrite <-S_lt.
          apply naturals.lt_succ.
        + rewrite <-add_1_r, sub_abba.
          apply neq_sym, PA4. }
    rewrite ? sub_succ, <-(add_1_r c), sub_abba.
    destruct (lt_trichotomy c (S m)) as [H | [H | H]].
    - apply le_lt_succ in H as [d H].
      subst.
      rewrite <-? add_1_r, <-(add_assoc c), ? (add_comm c), ? sub_abba,
      <-rings.D1, <-Pascal's_identity, (add_comm 1%N), sub_abba,
      rings.INR_add; auto.
      now exists c.
    - subst.
      rewrite sub_diag, ? rings.pow_0_r, ? (rings.M1 _ _ 1%R), ? rings.M3,
      ? add_1_r, binomial_overflow, ? binomial_n_n, <-INR_0, mul_0_l, rings.A3;
        auto using naturals.succ_lt.
    - rewrite ? binomial_overflow, <-INR_0; try (now ring_simplify);
        rewrite add_1_r, <-? S_lt;
        eauto using naturals.lt_trans, naturals.succ_lt.
  Qed.

  Theorem binomial_theorem : ∀ n k, coefficient ((1 + x)^n) k = binomial n k.
  Proof.
    intros n k.
    rewrite IRP_1, (generalized_binomial_theorem n k 1%R), rings.pow_1_l.
    now ring_simplify.
  Qed.

  Theorem generalized_binomial_sum : ∀ n (α : R),
      (α + x)^n = sum _ (λ k, binomial n k * α^(n-k) * x^k) 0 n.
  Proof.
    intros n α.
    rewrite (polynomial_sum_lemma n ((α + x)^n)).
    - apply iterate_extensionality.
      intros k H.
      now rewrite IRP_pow, IRP_mul, generalized_binomial_theorem.
    - destruct (classic (1%R = 0%R)).
      + rewrite zero_ring_degree; auto using zero_le.
      + rewrite degree_of_a_plus_x_to_n; auto using naturals.le_refl.
  Qed.

  Theorem binomial_sum : ∀ n, (1 + x)^n = sum _ (λ k, binomial n k * x^k) 0 n.
  Proof.
    intros n.
    rewrite IRP_1, generalized_binomial_sum.
    f_equal.
    extensionality k.
    now rewrite IRP_pow, rings.pow_1_l, <-IRP_1, <-rings.M2, rings.M3.
  Qed.

  Definition leading_coefficient f := coefficient f (degree f).

  Lemma leading_coefficient_zero : leading_coefficient 0 = 0%R.
  Proof.
    unfold leading_coefficient, degree.
    destruct excluded_middle_informative; try now (exfalso; eauto).
    replace 0 with (0%R : poly) by now apply set_proj_injective.
    now rewrite coeff_const.
  Qed.

  Lemma leading_coefficient_nonzero : ∀ f, leading_coefficient f = 0%R → f = 0.
  Proof.
    intros f H.
    apply NNPP.
    intros H0.
    eapply (degree_spec f) in H0.
    intuition.
  Qed.

  Lemma const_mul_monic : ∀ a f, a ≠ 0%R → monic f → degree (a * f) = degree f.
  Proof.
    intros a f H H0.
    apply naturals.le_antisymm.
    - apply degree_bound.
      intros m H1.
      rewrite const_coeff_mul, coeffs_above_degree; auto; now ring_simplify.
    - apply degree_lower_bound.
      now rewrite const_coeff_mul, H0, rings.M1, rings.M3.
  Qed.

  Lemma monic_division_algorithm_helper : ∀ a b n,
      monic b → (0 < degree b)%N → (degree a ≤ n)%N →
      ∃ q r, a = b * q + r ∧ (degree r < degree b)%N.
  Proof.
    destruct (classic (1%R = 0%R)) as [H | H]; intros a b n H0 H1 H2.
    { exists 0, 0.
      split; try apply zero_ring_degeneracy;
        replace 0 with (0%R : poly) by now apply set_proj_injective.
      - now rewrite IRP_1, H.
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
    destruct (IHn (a - (leading_coefficient a) * x^c * b)) as [q [r [H7 H8]]].
    2: { exists (q + (leading_coefficient a) * x^c), r.
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
      rewrite add_0_r, naturals.add_comm, const_mul_monic, degree_x_to_n;
        auto using degree_x_to_n.
      + intros H9.
        apply leading_coefficient_nonzero in H9.
        subst.
        unfold degree in H5.
        destruct excluded_middle_informative; intuition.
        contradiction (PA4 n).
      + unfold monic.
        rewrite degree_x_to_n, coeffs_of_x_to_n; auto.
    - apply naturals.le_not_gt in H8.
      replace m with (S n) by now apply eq_sym, squeeze_upper.
      unfold leading_coefficient, monic in *.
      rewrite <-H5, <-rings.M2, const_coeff_mul, (rings.M1 PR),
      coeff_of_x_mul, <-H4, sub_abba, H0; try now ring_simplify.
      exists (degree b).
      now ring_simplify [H4].
  Qed.

  Theorem monic_division_algorithm : ∀ a b,
      monic b → (0 < degree b)%N → ∃ q r,
          a = b * q + r ∧ (degree r < degree b)%N.
  Proof.
    eauto using monic_division_algorithm_helper, naturals.le_refl.
  Qed.

  Definition const f := degree f = 0%N.

  Theorem const_classification : ∀ f, const f ↔ ∃ c : R, f = c.
  Proof.
    split; unfold const; intros H.
    - exists (coefficient f 0).
      rewrite (polynomial_sum_lemma 0 f) at 1.
      + rewrite sum_0, rings.pow_0_r.
        now ring_simplify.
      + rewrite H.
        auto using naturals.le_refl.
    - destruct H as [c H].
      now rewrite H, degree_const.
  Qed.

  Theorem eval_const : ∀ a b : R, a b = a.
  Proof.
    intros a b.
    rewrite <-(rings.M3 _ (a : poly)), rings.M1, <-(rings.pow_0_r _ x),
    eval_mul_const, eval_x_to_n, rings.pow_0_r.
    ring.
  Qed.

  Theorem eval_neg : ∀ f a, (-f) a = (- (f a))%R.
  Proof.
    intros f a.
    rewrite <-rings.mul_neg_1_l, eval_mul, IRP_1, IRP_neg, eval_const.
    ring.
  Qed.

  Infix "｜" := (rings.divide PR).

  Theorem root_classification : ∀ f (a : R), a ∈ roots f ↔ x - a｜f.
  Proof.
    destruct (classic (1%R = 0%R)) as [H | H]; split; intros H0;
      rewrite roots_action in *; try now apply zero_ring_degeneracy.
    { exists 1.
      apply zero_ring_degeneracy.
      rewrite IRP_1, H.
      now apply set_proj_injective. }
    - assert (linear (x - a)) as H1; try unfold linear in H1.
      { rewrite linear_classification.
        exists (-a)%R, 1%R.
        split; auto.
        rewrite <-IRP_1, <-IRP_neg.
        now ring_simplify. }
      destruct (monic_division_algorithm f (x - a)) as [q [r [H2 H3]]];
        try rewrite H1 in *; eauto using naturals.succ_lt.
      + replace (x - a) with ((-a)%R + x); auto using monic_a_plus_x.
        rewrite sub_is_neg, IRP_neg.
        now ring_simplify.
      + exists q.
        rewrite rings.M1, H2.
        replace r with 0; try ring.
        assert (const r) as H4 by now apply lt_1_eq_0 in H3.
        apply const_classification in H4 as [c H4].
        subst.
        replace 0 with (0%R : poly) by now apply set_proj_injective.
        now rewrite <-H0, eval_add, eval_mul, sub_is_neg, eval_add, eval_neg,
        eval_x, ? eval_const, rings.A4, mul_0_l, rings.A3.
    - destruct H0 as [q H0].
      subst.
      rewrite eval_mul, sub_is_neg, eval_add, eval_neg, eval_x, ? eval_const.
      ring.
  Qed.

  Theorem coeffs_of_0 : ∀ n, coefficient 0 n = 0%R.
  Proof.
    intros n.
    destruct (classic (n = 0%N)).
    - replace 0 with (0%R : poly) by now apply set_proj_injective.
      subst; now rewrite coeff_const.
    - apply coeffs_above_degree.
      unfold degree.
      destruct excluded_middle_informative; try (now exfalso; eauto).
      apply succ_0 in H as [m H].
      subst; auto using naturals.lt_succ.
  Qed.

  Section Integral_domain_theorems.

    Hypothesis is_ID : is_integral_domain ring.

    Theorem poly_is_ID : is_integral_domain PR.
    Proof.
      destruct is_ID as [C N].
      split.
      - intros a b H.
        destruct (classic (a = 0))
          as [H0 | H0], (classic (b = 0)) as [H1 | H1]; intuition.
        assert (leading_coefficient a ≠ 0%R) as H2 by
            eauto using leading_coefficient_nonzero.
        assert (leading_coefficient b ≠ 0%R) as H3 by
            eauto using leading_coefficient_nonzero.
        unfold leading_coefficient in *.
        assert (coefficient (a * b) (degree a + degree b) ≠ 0%R) as H4.
        { rewrite <-leading_term_prod.
          intros H4.
          apply C in H4; tauto. }
        now rewrite H, coeffs_of_0 in H4.
      - intros H.
        contradiction N.
        rewrite IRP_1 in H.
        replace 0 with (0%R : poly) in H by now apply set_proj_injective.
        now apply IRP_eq.
    Qed.

    Theorem monic_nonzero : ∀ f, monic f → f ≠ 0.
    Proof.
      intros f H H0.
      unfold monic in *.
      subst.
      rewrite coeffs_of_0 in H.
      destruct is_ID as [C N].
      now contradiction N.
    Qed.

    Theorem prod_root : ∀ f g, roots (f * g) = (roots f) ∪ (roots g).
    Proof.
      intros f g.
      destruct is_ID as [C N].
      apply Extensionality.
      split; intros H.
      - apply Pairwise_union_classification.
        apply roots_in_R in H as H0.
        rewrite <-(setify_action _ _ H0), ? roots_action, eval_mul in *.
        apply C in H; tauto.
      - apply Pairwise_union_classification in H as [H | H];
          apply roots_in_R in H as H0;
          rewrite <-(setify_action _ _ H0), ? roots_action, eval_mul, H in *;
          ring.
    Qed.

    Theorem monic_linear_root : ∀ (a : R), roots (x - a) = {a, a}.
    Proof.
      intros a.
      apply Extensionality.
      split; intros H; rewrite Singleton_classification in *; subst.
      - apply roots_in_R in H as H0.
        set (ζ := exist _ _ H0 : R).
        rewrite <-(setify_action _ _ H0) in *; fold ζ in H |-*.
        apply roots_action in H.
        unfold rings.sub, IRs, rings.IRS in *.
        rewrite <-(rings.A3 _ a), <-H, eval_add, eval_x, eval_neg, eval_const.
        f_equal.
        ring.
      - rewrite roots_action.
        unfold rings.sub.
        rewrite eval_add, eval_x, eval_neg, eval_const.
        ring.
    Qed.

    Theorem nonzero_prod_degree :
      ∀ f g, f ≠ 0 → g ≠ 0 → degree (f * g) = (degree f + degree g)%N.
    Proof.
      intros f g H H0.
      apply naturals.le_antisymm; auto using mul_degree.
      apply degree_lower_bound.
      rewrite <-leading_term_prod.
      intros H1.
      destruct is_ID as [C N].
      apply C in H1 as [H1 | H1]; now apply leading_coefficient_nonzero in H1.
    Qed.

    Theorem monic_linear_degree : ∀ (a : R), degree (x - a) = 1%N.
    Proof.
      intros a.
      destruct is_ID as [C N].
      rewrite <-(degree_of_a_plus_x N (-a)), <-IRP_neg.
      now replace (x - a) with (-a + x) by now ring_simplify.
    Qed.

    Theorem finite_roots : ∀ f, f ≠ 0 → finite (roots f).
    Proof.
      intros f H.
      remember (degree f) as d.
      revert f H Heqd.
      induction d using Strong_Induction.
      intros f H0 Heqd.
      destruct (classic (roots f = ∅)) as [H1 | H1].
      { rewrite H1.
        now exists 0%N. }
      apply Nonempty_classification in H1 as [a H1].
      apply roots_in_R in H1 as H2.
      set (α := exist _ _ H2 : R).
      rewrite <-(setify_action _ _ H2) in *; fold α in H1.
      apply root_classification in H1 as [g H1].
      subst.
      rewrite prod_root.
      apply cancellation_ne0 in H0 as [H0 H1].
      apply finite_unions_are_finite.
      - eapply H; eauto.
        rewrite nonzero_prod_degree, monic_linear_degree, add_1_r; auto.
        apply naturals.succ_lt.
      - rewrite monic_linear_root.
        apply singletons_are_finite.
    Qed.

    Theorem root_degree_bound : ∀ f, f ≠ 0 → (# roots f ≤ degree f)%N.
    Proof.
      intros f H.
      destruct is_ID as [C N].
      remember (degree f) as d.
      revert f H Heqd.
      induction d using Strong_Induction.
      intros f H0 Heqd.
      destruct (classic (roots f = ∅)) as [H1 | H1].
      { rewrite H1, card_empty.
        apply zero_le. }
      apply Nonempty_classification in H1 as [a H1].
      apply roots_in_R in H1 as H2.
      set (α := exist _ _ H2 : R).
      rewrite <-(setify_action _ _ H2) in *; fold α in H1.
      apply root_classification in H1 as [g H1].
      subst.
      rewrite prod_root.
      apply cancellation_ne0 in H0 as [H0 H1].
      rewrite nonzero_prod_degree, monic_linear_degree in *; auto.
      eapply naturals.le_trans; eauto using finite_union_card_bound.
      apply naturals.le_cross_add.
      - apply H; auto.
        rewrite add_1_r.
        apply naturals.succ_lt.
      - rewrite monic_linear_root, singleton_card.
        apply naturals.le_refl.
    Qed.

  End Integral_domain_theorems.

End Polynomial_theorems.
