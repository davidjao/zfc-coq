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
  Notation R := (elts ring).
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

  Theorem polynomials_are_subset : polynomial_set ⊂ power_series_ring ring.
  Proof.
    eauto using Specify_subset.
  Qed.

  Theorem polynomials_are_subring :
    is_subring (power_series_ring ring) polynomial_set.
  Proof.
    ((repeat split) =>
     [[a A] [b B] /Specify_classification [_] /[swap]
            /Specify_classification [_] |
      [a A] [b B] /Specify_classification [_] /[swap]
            /Specify_classification [_] | [a A] /Specify_classification [_] | ];
     rewrite /polynomial_set Specify_classification ? despecify) =>
    [[m H] [n H0] | [m H] [n H0] | [n H] | ]; split; eauto using elts_in_set.
    - exists (naturals.max m n) => x H1.
      rewrite coefficient_add H ? H0; eauto using rings.A3, naturals.le_trans,
                                      naturals.max_le_l, naturals.max_le_r.
    - exists (n + m)%N => x H1.
      rewrite coefficient_mul -(sum_of_0 _ x).
      apply iterate_extensionality => k [H2 H3].
      case (classic (n ≤ k)%N) => [H4 | H4].
      + rewrite H0 ? mul_0_l //.
      + rewrite H ? mul_0_r; auto.
        apply NNPP => H5.
        move: H5 H4 H1 => /naturals.lt_not_ge /[swap] /naturals.lt_not_ge
                           /naturals.lt_cross_add /[apply].
        rewrite sub_abab // naturals.le_not_gt //.
    - exists n => x H0.
      rewrite coefficient_neg H; auto; ring.
    - exists 1%N => m.
      rewrite /power_series.one /power_series.IRS coefficient_seriesify.
      case excluded_middle_informative => // -> /not_succ_le //.
  Qed.

  Definition polynomial_ring :=
    subring _ polynomial_set polynomials_are_subset polynomials_are_subring.

  Notation poly := (elts polynomial_ring).

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
    move=> c.
    apply Specify_classification, conj; eauto using elts_in_set.
    rewrite /ISS /power_series.IRS despecify coefficient_seriesify.
    exists 1%N => m.
    case excluded_middle_informative; auto => -> /not_succ_le //.
  Qed.

  Notation PS := (power_series ring).

  Theorem x_is_poly : x ring ∈ polynomial_set.
  Proof.
    apply Specify_classification, conj; eauto using elts_in_set.
    rewrite /ISS /x /shift /power_series.one /power_series.IRS
            despecify ? coefficient_seriesify.
    exists 2%N => m [c].
    (repeat case excluded_middle_informative; auto) =>
    /sub_0_le /[swap] /succ_0 [n ->] /naturals.le_antisymm
     /(_ (one_le_succ n)) ->.
    rewrite add_comm add_succ_r add_1_r => /(@eq_sym N) /PA5 /PA4 //.
  Qed.

End Polynomials_construction.

Section Polynomial_theorems.

  Variable ring : rings.ring.
  Definition R := elts ring.
  Notation SR := (power_series_ring ring).
  Notation PR := (polynomial_ring ring).
  Definition series := elts SR.
  Definition poly := elts PR.
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

  Definition IRP (c : R) := (mkSet (consts_are_polys _ c)) : poly.
  Coercion IRP : R >-> poly.

  Definition coefficient (f : poly) n := coefficient _ (f : series) n : R.
  Definition x := (mkSet (x_is_poly _)) : poly.

  Theorem IPS_eq : ∀ f g : poly, (f : series) = (g : series) ↔ f = g.
  Proof.
    split => [/ISR_eq | ->] //.
  Qed.

  Theorem IPS_add : ∀ f g : poly, ((f : series) + (g : series))%series = f + g.
  Proof.
    move=> f g.
      by apply set_proj_injective.
  Qed.

  Theorem IPS_neg : ∀ f : poly, (-f : series)%series = -f.
  Proof.
    move=> f.
      by apply set_proj_injective.
  Qed.

  Theorem IPS_mul : ∀ f g : poly, ((f : series) * (g : series))%series = f * g.
  Proof.
    move=> f g.
      by apply set_proj_injective.
  Qed.

  Theorem IRP_eq : ∀ a b : R, (a : poly) = (b : poly) ↔ a = b.
  Proof.
    split => [H | ->] //.
    inversion H as [H0].
    move: H0 => /set_proj_injective /IRS_eq //.
  Qed.

  Theorem IRP_add : ∀ a b : R, (a : poly) + (b : poly) = (a + b)%R.
  Proof.
    rewrite /IRP => a b.
    apply set_proj_injective => /=.
    rewrite (IRS_add _) /ISR /rings.IRS /ISS /=.
    do 2 f_equal; apply set_proj_injective => //.
  Qed.

  Theorem IRP_mul : ∀ a b : R, (a : poly) * (b : poly) = (a * b)%R.
  Proof.
    rewrite /IRP => a b.
    apply set_proj_injective => /=.
    rewrite (IRS_mul _) /ISR /rings.IRS /ISS /=.
    do 2 f_equal; apply set_proj_injective => //.
  Qed.

  Theorem IRP_neg : ∀ a : R, (-a : poly) = (-a)%R.
  Proof.
    rewrite /IRP => a.
    apply set_proj_injective => /=.
    rewrite (IRS_neg _) /ISR /rings.IRS /ISS /=.
    do 2 f_equal; apply set_proj_injective => //.
  Qed.

  Theorem IRP_1 : 1 = 1%R.
  Proof.
    apply set_proj_injective => /=.
    case polynomials_are_subring => [? [? []]] //.
  Qed.

  Theorem IRP_0 : 0 = 0%R.
  Proof.
    apply set_proj_injective => //.
  Qed.

  Theorem IRP_pow : ∀ (n : N) (a : R), (a : poly)^n = (a^n)%R.
  Proof.
    induction n using Induction =>
    a; rewrite ? rings.pow_0_r ? IRP_1 ? rings.pow_succ_r ? IHn ? IRP_mul //.
  Qed.

  Theorem nonzero_coefficients : ∀ f, f ≠ 0 ↔ ∃ m, coefficient f m ≠ 0%R.
  Proof.
    split => [H | /[swap] -> [m []]].
    - apply NNPP.
      move: H => /[swap] H /IPS_eq [].
      apply power_series_extensionality => /=.
      rewrite /IPS -sub_zero_is_zero.
      extensionality n => /=.
      rewrite /power_series.zero /IRS /power_series.IRS coefficient_seriesify.
      case excluded_middle_informative; apply NNPP; contradict H; eauto.
    - rewrite /coefficient /IPS /=
      -sub_zero_is_zero /= /coefficient /power_series.zero /IRS
                        /power_series.IRS coefficient_seriesify.
      case excluded_middle_informative; tauto.
  Qed.

  Theorem degree_construction :
    ∀ f, f ≠ 0 →
         ∃ m, coefficient f m ≠ 0%R ∧ ∀ n, (m < n)%N → coefficient f n = 0%R.
  Proof.
    move=> f /nonzero_coefficients [m H].
    move: (elts_in_set f) => /Specify_classification [H0].
    rewrite (reify H0) despecify => [[n H1]].
    elim (lub (λ x, coefficient f x ≠ 0%R)) =>
    [s [H2 H3] | | ]; try now (exists m).
    - exists s.
      split; auto => x [/naturals.le_antisymm H4 H5].
      apply NNPP => /H3 /H4 //.
    - exists n => x H3.
      apply naturals.le_not_gt.
      move: H3 => /[swap] [[d H3]].
      (rewrite /coefficient -(H1 x) //) => [[]].
      f_equal.
      apply set_proj_injective => //.
  Qed.

  Definition degree : poly → N.
  Proof.
    move=> f.
    case (excluded_middle_informative (f = 0)) =>
    [H | /degree_construction /constructive_indefinite_description [d H]].
    - exact 0%N.
    - exact d.
  Defined.

  Theorem degree_zero : degree 0 = 0%N.
  Proof.
    rewrite /degree.
    case excluded_middle_informative => *; auto; exfalso; auto.
  Qed.

  Theorem degree_spec : ∀ f m,
      f ≠ 0 → degree f = m ↔ (coefficient f m ≠ 0%R ∧
                              ∀ n, (m < n)%N → coefficient f n = 0%R).
  Proof.
    ((split; rewrite /degree; case excluded_middle_informative; try tauto) =>
     {}H; elim constructive_indefinite_description) =>
    [y /[swap] -> [H0 H1] | y [H0 H1] [H2 H3]] //.
    (apply naturals.le_antisymm; rewrite naturals.le_not_gt) => [/H3 | /H1] //.
  Qed.

  Lemma coeffs_of_x : ∀ n : N, n ≠ 1%N → coefficient x n = 0%R.
  Proof.
    rewrite /IPS /x /ISR /ISS => /= n H.
    have -> : 0%R = power_series.coefficient _ (power_series.x ring) n.
    - rewrite /power_series.x /shift /power_series.one /IRS /power_series.IRS
              ? coefficient_seriesify sub_1_r.
      (repeat case excluded_middle_informative; auto) => /[swap] /succ_0 [m H0].
      move: H0 H pred_succ -> => /[swap] -> /[swap] -> //.
    - rewrite /coefficient.
      f_equal.
      now apply set_proj_injective.
  Qed.

  Lemma x_coeff_of_x : coefficient x 1 = 1%R.
  Proof.
    rewrite /IPS /x /ISR /ISS /=.
    have -> : 1%R = power_series.coefficient _ (power_series.x ring) 1.
    - rewrite /power_series.x /shift /power_series.one /IRS /power_series.IRS
              ? coefficient_seriesify sub_diag.
      repeat case excluded_middle_informative; auto => // /(@eq_sym N) /PA4 //.
    - rewrite /coefficient.
      f_equal.
      now apply set_proj_injective.
  Qed.

  Lemma IPS_pow : ∀ n (f : poly), ((f : series)^n)%series = f^n.
  Proof.
    induction n using Induction => f.
    - rewrite ? (rings.pow_0_r PR) ? (rings.pow_0_r SR).
      apply sub_one_is_one.
    - rewrite ? (pow_succ_r PR) ? (pow_succ_r SR) -IPS_mul IHn //.
  Qed.

  Lemma coeffs_of_x_ne_n : ∀ m n, m ≠ n → coefficient (x^n) m = 0%R.
  Proof.
    move /[swap].
    elim/Induction => [n H | n].
    { rewrite rings.pow_0_r /coefficient /IPS /=
      -sub_one_is_one /= /power_series.one /IRS /power_series.IRS
                      /coefficient coefficient_seriesify.
      case excluded_middle_informative; tauto. }
    rewrite /coefficient pow_succ_r -IPS_mul -IPS_pow /= => IH m H.
    rewrite /power_series.mul coefficient_seriesify -(sum_of_0 _ m).
    apply iterate_extensionality => k [H0 [c H1]].
    move: H1 H <-.
    case (classic (n = k)) => [-> H | H H1].
    - rewrite -/(coefficient x (k+c-k)) coeffs_of_x; try ring.
      move: H => /[swap].
      rewrite {1}naturals.add_comm sub_abba -add_1_r => -> //.
    - rewrite IH; auto; ring.
  Qed.

  Lemma degree_bound : ∀ n f,
      ((∀ m : N, n < m → coefficient f m = 0%R) → degree f ≤ n)%N.
  Proof.
    rewrite /degree => n f H.
    case excluded_middle_informative; auto using zero_le => H0.
    elim constructive_indefinite_description => [d [H1 H2]].
    apply naturals.le_not_gt.
    move: H1 => /[swap] /H //.
  Qed.

  Lemma coeffs_above_degree : ∀ n f, (degree f < n)%N → coefficient f n = 0%R.
  Proof.
    rewrite /degree => n f.
    case excluded_middle_informative => [-> | H].
    - rewrite /coefficient /IPS /=
      -sub_zero_is_zero /= /power_series.zero /IRS /power_series.IRS
                        coefficient_seriesify.
      case excluded_middle_informative; tauto.
    - elim constructive_indefinite_description => [d [H0 H1]] /H1 //.
  Qed.

  Lemma IPS_IRP : ∀ c : R, (c : series) = IRS c.
  Proof.
    move=> c.
      by apply set_proj_injective.
  Qed.

  Lemma const_coeff_mul :
    ∀ n f (c : R), coefficient (c * f) n = (c * coefficient f n)%R.
  Proof.
    rewrite /coefficient => n f c.
    rewrite -power_series.const_coeff_mul -IPS_mul IPS_IRP //.
  Qed.

  Lemma coeffs_of_x_to_n : ∀ n, coefficient (x^n) n = 1%R.
  Proof.
    induction n using Induction.
    - rewrite rings.pow_0_r /= /coefficient /IPS /=
      -sub_one_is_one /= /power_series.one /IRS /power_series.IRS /coefficient
                      coefficient_seriesify.
      case excluded_middle_informative; tauto.
    - rewrite pow_succ_r /= /coefficient /IPS
      -ISR_mul /= /power_series.mul /coefficient coefficient_seriesify
      -(singleton_sum _ n (S n) 1%R); auto using le_succ.
      apply iterate_extensionality => k.
      case excluded_middle_informative => [-> | H].
      + rewrite -IHn -add_1_r naturals.add_comm sub_abba -/(coefficient x 1)
                              x_coeff_of_x M3_r /coefficient //.
      + rewrite -/IPS -/(coefficient (x^n) k) coeffs_of_x_ne_n // mul_0_l //.
  Qed.

  Theorem coefficient_add : ∀ n f g,
      coefficient (f + g) n = (coefficient f n + coefficient g n)%R.
  Proof.
    rewrite /coefficient => n f g.
    rewrite -IPS_add -power_series.coefficient_add //.
  Qed.

  Theorem coefficient_neg : ∀ n f, coefficient (-f) n = (- coefficient f n)%R.
  Proof.
    rewrite /coefficient => n f.
    rewrite -IPS_neg -power_series.coefficient_neg //.
  Qed.

  Theorem coefficient_mul : ∀ n f g,
      coefficient (f * g) n =
      sum _ (λ k, (coefficient f k * coefficient g (n-k))%R) 0 n.
  Proof.
    rewrite /coefficient => n f g.
    rewrite -IPS_mul -power_series.coefficient_mul //.
  Qed.

  Lemma minus_leading_term : ∀ f,
      (1 ≤ degree f → degree (f - (coefficient f (degree f)) *
                                  x^(degree f))%poly ≤ degree f - 1)%N.
  Proof.
    move=> f H.
    apply degree_bound => m.
    rewrite (sub_is_neg (polynomial_ring _)) coefficient_add
            coefficient_neg const_coeff_mul.
    case (classic (m = degree f)) =>
    [-> H0 | H0 /S_lt]; first by rewrite coeffs_of_x_to_n M3_r rings.A4 //.
    rewrite sub_1_r -naturals.le_lt_succ => H1.
    rewrite coeffs_of_x_ne_n // mul_0_r -neg_0 A3_r coeffs_above_degree //.
    split; auto.
    move: H H1 pred_succ => /naturals.lt_0_le_1 /nonzero_lt /succ_0 =>
    [[k]] -> /[swap] -> //.
  Qed.

  Lemma polynomial_sum_lemma : ∀ d : N, ∀ f,
        (degree f ≤ d)%N → f = sum PR (λ n, coefficient f n * x^n) 0 d.
  Proof.
    induction d using Induction => [f [c /naturals.cancellation_0_add [H H0]] |
                                    f /le_lt_or_eq [/[dup] H [H0 H1] | H]].
    - rewrite sum_0 -IPS_eq.
      apply power_series_extensionality, functional_extensionality => n.
      rewrite -/(coefficient f n) -/(coefficient (coefficient f 0 * x ^ 0%N) n).
      case (classic (n = 0%N)) => [-> | H1].
      + rewrite const_coeff_mul coeffs_of_x_to_n M3_r //.
      + rewrite const_coeff_mul coeffs_of_x_ne_n // coeffs_above_degree
                ? mul_0_r // H -nonzero_lt //.
    - rewrite -{1}(rings.A3 _ f) rings.A1 sum_succ; auto using zero_le.
      f_equal.
      * apply IHd, le_lt_succ => //.
      * rewrite coeffs_above_degree -? IRP_0 ? mul_0_l; repeat split; auto.
    - rewrite sum_succ -1 ? {1}(rings.A3 _ f) ? (rings.A1 _ 0)
                          -? (rings.A4 _ (coefficient f (S d) * x ^ S d))
                          ? (rings.A1 _ (coefficient f (S d) * x ^ S d))
                          ? rings.A2; auto using zero_le.
      f_equal.
      rewrite -sub_is_neg (IHd (f - (coefficient f (S d) * x ^ S d))).
      + rewrite -{3}(pred_succ d) -sub_1_r -H.
        apply minus_leading_term.
        rewrite H.
        apply one_le_succ.
      + apply iterate_extensionality => k [H1 H2].
        rewrite sub_is_neg coefficient_add coefficient_neg.
        suff -> : coefficient (coefficient f (S d) * x ^ S d) k
                  = 0%R by rewrite -neg_0 rings.A1 rings.A3 //.
        rewrite const_coeff_mul coeffs_of_x_ne_n ? mul_0_r //.
        move: H2 => /[swap] -> /not_succ_le //.
  Qed.

  Theorem degree_of_sum : ∀ d (a : N → R),
      (degree (sum PR (λ n, a n * x^n)%poly 0 d) ≤ d)%N.
  Proof.
    move=> d a.
    apply degree_bound; auto => m H.
    induction d using Induction.
    - rewrite sum_0 const_coeff_mul coeffs_of_x_ne_n ? mul_0_r ? nonzero_lt //.
    - rewrite sum_succ ? coefficient_add ? IHd ? rings.A3 ? const_coeff_mul
              ? coeffs_of_x_ne_n ? mul_0_r;
        eauto using zero_le, naturals.lt_trans, naturals.succ_lt.
      move: H => /[swap] -> /naturals.lt_irrefl //.
  Qed.

  Theorem coefficient_sum_add : ∀ d a k,
      coefficient (sum _ (λ n, a n) 0 d) k =
      sum _ (λ n, (coefficient (a n) k)) 0 d.
  Proof.
    induction d using Induction
    => a k; rewrite ? sum_0 // ? sum_succ -? IHd ? coefficient_add;
         auto using zero_le.
  Qed.

  Theorem coefficient_extraction : ∀ d k (a : N → R),
      (k ≤ d)%N → coefficient (sum _ (λ n, a n * x^n) 0 d) k = (a k).
  Proof.
    move=> d k a H.
    rewrite coefficient_sum_add -(singleton_sum _ k d (a k)); auto.
    apply iterate_extensionality => z H0.
    case excluded_middle_informative => [-> | H1].
    - rewrite const_coeff_mul coeffs_of_x_to_n M3_r //.
    - rewrite const_coeff_mul coeffs_of_x_ne_n ? mul_0_r; auto.
  Qed.

  Theorem coeff_of_x_mul : ∀ n k f,
      (k ≤ n)%N → coefficient (f * x^k) n = coefficient f (n-k).
  Proof.
    move=> /[swap] k /[swap] f.
    induction k using Induction =>
    n [c <-]; first by rewrite rings.pow_0_r sub_0_r M3_r.
    rewrite /coefficient pow_succ_r rings.M2 rings.M1 -IPS_mul.
    have -> : (x : series) = power_series.x ring by apply set_proj_injective.
    rewrite /= mul_x_shift /shift coefficient_seriesify.
    (case excluded_middle_informative;
     first by rewrite add_succ_l => /(@eq_sym N) /PA4 //) => _.
    move: (IHk (S k + c - 1)%N).
    rewrite /coefficient /= add_succ_l sub_1_r pred_succ sub_succ =>
    /(_ (naturals.le_add k c)) -> //.
  Qed.

  Theorem add_degree :
    ∀ f g, (degree (f + g)%poly ≤ naturals.max (degree f) (degree g))%N.
  Proof.
    rewrite /naturals.max /sumbool_rect => f g.
    case excluded_middle_informative =>
    [H | /naturals.le_not_gt H]; apply degree_bound =>
    m H0; rewrite coefficient_add ? coeffs_above_degree ? rings.A3 //;
                  eauto using naturals.lt_trans, naturals.le_lt_trans.
  Qed.

  Theorem mul_degree : ∀ f g, (degree (f * g)%poly ≤ degree f + degree g)%N.
  Proof.
    move=> f g.
    apply degree_bound; auto => m /naturals.lt_not_ge => H.
    rewrite coefficient_mul -(sum_of_0 _ m).
    apply iterate_extensionality => k [H0 H1].
    case (classic (degree f < k)%N) => [H2 | /naturals.le_not_gt H2].
    - rewrite coeffs_above_degree ? mul_0_l //.
    - rewrite (coeffs_above_degree _ g) ? mul_0_r // naturals.lt_not_ge.
      contradict H.
      rewrite -(sub_abab k m); auto using naturals.le_cross_add.
  Qed.

  Theorem coeff_of_x_mul_overflow :
    ∀ n k f, (n < k)%N → coefficient (f * x^k) n = 0%R.
  Proof.
    move=> n k f H.
    rewrite coefficient_mul -(sum_of_0 _ n).
    apply iterate_extensionality => z [H0 [c H1]].
    move: H1 H <- => H1.
    rewrite coeffs_of_x_ne_n ? mul_0_r // add_comm sub_abba.
    move: H1 => /[swap] <- /naturals.lt_not_ge /(_ (le_add_l c z)) //.
  Qed.

  Definition eval f a := (sum _ (λ n, (coefficient f n) * a^n)%R 0 (degree f)).

  Coercion eval : poly >-> Funclass.

  Definition roots (f : poly) := {r of type ring | f r = 0%R}.

  Theorem roots_in_R : ∀ f a, a ∈ roots f → a ∈ ring.
  Proof.
    move=> f a /Specify_classification [] //.
  Qed.

  Theorem roots_action : ∀ f (a : R), a ∈ roots f ↔ f a = 0%R.
  Proof.
    ((split; have H: a ∈ ring by eauto using elts_in_set);
     rewrite /roots Specify_classification (reify H) despecify) =>
    [[H0 <-] | <-] //; eauto using f_equal, set_proj_injective, elts_in_set.
  Qed.

  Lemma sum_beyond_degree : ∀ f a m,
      (degree f ≤ m)%N →
      (sum _ (λ n, coefficient f n * a^n) 0 (degree f))%R =
      (sum _ (λ n, coefficient f n * a^n) 0 m)%R.
  Proof.
    move=> f a m H.
    induction m using Induction;
      first have -> : degree f = 0%N; auto using naturals.le_antisymm, zero_le.
    case (classic (degree f ≤ m)%N) => [/[dup] H0 /le_lt_succ H1 | H0].
    - rewrite sum_succ ? IHm // ? coeffs_above_degree // ? mul_0_l
              1 ? rings.A1 ? rings.A3; auto using zero_le.
    - apply f_equal, naturals.le_antisymm; auto.
      rewrite naturals.le_not_gt -le_lt_succ //.
  Qed.

  Theorem eval_add : ∀ f g a, (f + g) a = (f a + g a)%R.
  Proof.
    rewrite /eval => f g a.
    set (m := (naturals.max (degree f) (degree g))).
    rewrite (sum_beyond_degree (f+g) a m) ? (sum_beyond_degree f a m)
            ? (sum_beyond_degree g a m) -? sum_dist /m;
      eauto using add_degree, naturals.max_le_l, naturals.max_le_r.
    f_equal.
    extensionality n.
    rewrite coefficient_add rings.D1 //.
  Qed.

  Theorem eval_bound : ∀ f a n,
      (degree f ≤ n)%N → sum _ (λ n : N, (coefficient f n * a^n)%R) 0 n = f a.
  Proof.
    rewrite /eval => f a n H.
    rewrite (sum_beyond_degree f a n) //.
  Qed.

  Theorem degree_x_to_n : ∀ k, (1%R ≠ 0%R) → degree (x^k) = k.
  Proof.
    rewrite /degree => k.
    case excluded_middle_informative => [ | H].
    - rewrite -(mul_0_l PR (x^0%N)) IRP_0 -(coeffs_of_x_to_n k) => ->.
      rewrite const_coeff_mul mul_0_l //.
    - elim constructive_indefinite_description => [d [H0 _] _].
      apply NNPP => /coeffs_of_x_ne_n //.
  Qed.

  Lemma degree_const : ∀ c : R, degree c = 0%N.
  Proof.
    move=> c.
    apply naturals.le_antisymm; auto using zero_le.
    apply degree_bound => m H.
    rewrite -(rings.M3 _ (c : poly)) rings.M1 const_coeff_mul
    -(rings.pow_0_r _ x) coeffs_of_x_ne_n ? mul_0_r // nonzero_lt //.
  Qed.

  Lemma coeff_const : ∀ c : R, coefficient c 0 = c.
  Proof.
    move: classic => /[swap] c /(_ (c = 0%R)) => [[-> | H]].
    - rewrite -(rings.M3 _ (IRP 0)) rings.M1 const_coeff_mul mul_0_l //.
    - rewrite -(rings.M3 _ (c : poly)) rings.M1 const_coeff_mul
      -(rings.pow_0_r _ x) coeffs_of_x_to_n M3_r //.
  Qed.

  Lemma degree_lower_bound : ∀ n f, coefficient f n ≠ 0%R → (n ≤ degree f)%N.
  Proof.
    rewrite /degree => n f H.
    case excluded_middle_informative => [ | H0].
    - move: H => /[swap] -> [].
      rewrite IRP_0 -(rings.M3 _ (IRP 0)) rings.M1 const_coeff_mul mul_0_l //.
    - elim constructive_indefinite_description => [d [H1 H2]].
      rewrite naturals.le_not_gt => /H2 //.
  Qed.

  Lemma eval_mul_const : ∀ (c α : R) f, (c * f) α = (c * f α)%R.
  Proof.
    rewrite /eval => c α f.
    rewrite (sum_beyond_degree (c * f) _ (degree f)).
    - eapply naturals.le_trans; auto using mul_degree.
      rewrite degree_const add_0_l.
      auto using naturals.le_refl.
    - rewrite sum_mul.
      f_equal.
      extensionality n.
      rewrite const_coeff_mul rings.M2 //.
  Qed.

  Lemma eval_x_to_n : ∀ n α, ((x^n) α) = (α^n)%R.
  Proof.
    rewrite /eval => n α.
    elim (classic (1%R = 0%R)) => [ | H]; auto using zero_ring_degeneracy.
    rewrite degree_x_to_n -1 ? (singleton_sum _ n n (α^n)%R);
      auto using naturals.le_refl.
    apply iterate_extensionality => k H0.
    case excluded_middle_informative => [-> | H1].
    - rewrite coeffs_of_x_to_n rings.M3 //.
    - rewrite coeffs_of_x_ne_n ? mul_0_l //.
  Qed.

  Lemma eval_x : ∀ α, x α = α.
  Proof.
    move=> α.
    rewrite -(rings.pow_1_r PR x) eval_x_to_n rings.pow_1_r //.
  Qed.

  Lemma eval_mul_x_lemma : ∀ m (α : R) (f : N → R) n,
      ((sum _ (λ i, f i * x^i) 0 m) * x^n) α =
      ((sum _ (λ i, f i * x^i)%poly 0 m : poly) α * α^n)%R.
  Proof.
    induction m using Induction => α f n.
    - rewrite sum_0 rings.pow_0_r (rings.M1 _ _ 1) rings.M3 eval_mul_const
              eval_x_to_n /eval degree_const sum_0 rings.pow_0_r
              coeff_const M3_r //.
    - rewrite ? sum_succ ? rings.D1 ? eval_add ? rings.D1 ? IHm
              -? rings.M2 ? eval_mul_const -? rings.M2 -? rings.pow_add_r
              ? eval_x_to_n ? rings.pow_add_r; auto using zero_le.
  Qed.

  Lemma eval_mul_x_f : ∀ f a n, (f * x^n) a = (f a * (x^n)%poly a)%R.
  Proof.
    move=> f a n.
    rewrite (polynomial_sum_lemma (degree f) f) ? eval_mul_x_lemma
            ? eval_x_to_n; auto using naturals.le_refl.
  Qed.

  Lemma eval_mul_lemma : ∀ n f (a : N → R) α,
      (f * (sum PR (λ i, (a i) * x^i) 0%N n)) α =
      (f α * sum _ (λ i, (a i) * α^i) 0 n)%R.
  Proof.
    induction n using Induction => f a α.
    - rewrite ? sum_0 ? rings.M2 ? (rings.M1 _ _ (a 0%N : poly))
              ? (rings.M1 _ _ (a 0%N)) -? rings.M2 eval_mul_const
              eval_mul_x_f eval_x_to_n //.
    - rewrite ? sum_succ ? rings.D1_l -? IHn ? eval_add; auto using zero_le.
      rewrite -eval_x_to_n rings.A1 (rings.M1 _ f)
      -rings.M2 eval_mul_const (rings.M1 _ _ f) eval_mul_x_f ? rings.M2
                (rings.M1 _ (f α)) rings.A1 //.
  Qed.

  Theorem eval_mul : ∀ f g a, (f * g) a = (f a * g a)%R.
  Proof.
    move=> f g a.
    rewrite (polynomial_sum_lemma (degree g) g) ? eval_mul_lemma ? eval_bound;
      try do 2 f_equal; try extensionality n; rewrite -? polynomial_sum_lemma;
        auto using naturals.le_refl.
  Qed.

  Definition linear f := degree f = 1%N.

  Theorem linear_classification :
    ∀ f, linear f ↔ ∃ a b : R, f = a + b * x ∧ b ≠ 0%R.
  Proof.
    split => [ | [a [b [-> H0]]]].
    - rewrite /linear => /[dup] H /[dup] => /or_intror =>
      /(_ (degree f < 1)%N) /le_lt_or_eq H1.
      rewrite (polynomial_sum_lemma 1 f) //.
      exists (coefficient f 0), (coefficient f 1).
      split => [ | ].
      + rewrite /naturals.one sum_succ ? sum_0 ? rings.pow_0_r
                -/naturals.one ? rings.pow_1_r ? M3_r; auto using zero_le.
      + move: H.
        case (classic (f = 0)) => [-> | ].
        * rewrite degree_zero => /PA4 //.
        * move /degree_spec /[apply] => [[]] //.
    - apply naturals.le_antisymm.
      + eapply naturals.le_trans; eauto using add_degree.
        rewrite degree_const max_0_l.
        eapply naturals.le_trans; eauto using mul_degree.
        rewrite degree_const add_0_l -(rings.pow_1_r _ x) degree_x_to_n;
          auto using naturals.le_refl => /zero_ring_degeneracy /(_ b 0%R) //.
      + apply degree_lower_bound.
        rewrite coefficient_add coeffs_above_degree ? const_coeff_mul
                ? x_coeff_of_x ? degree_const ? rings.A3 ? M3_r;
          eauto using naturals.succ_lt.
  Qed.

  Theorem degree_of_a_plus_x :
    1%R ≠ 0%R → ∀ α : R, degree (α + x) = 1%N.
  Proof.
    move=> H α.
    apply linear_classification.
    exists α, 1%R.
    rewrite -IRP_1 rings.M3 //.
  Qed.

  Definition monic f := (coefficient f (degree f) = 1%R).

  Theorem leading_term_prod : ∀ f g,
      (coefficient f (degree f) * coefficient g (degree g))%R =
      coefficient (f * g) (degree f + degree g)%N.
  Proof.
    move=> f g.
    rewrite coefficient_mul
    -(singleton_sum _ (degree f) (degree f + degree g)%N
                    (coefficient f (degree f) * coefficient g (degree g))%R);
      first by (exists (degree g)).
    apply iterate_extensionality => k H.
    case excluded_middle_informative => [-> | H0].
    - rewrite add_comm sub_abba //.
    - case (lt_trichotomy k (degree f)) => [[[c <-] H2] | [H1 | H1]]; try tauto.
      + rewrite (coeffs_above_degree _ g) ? mul_0_r //
        -add_assoc add_comm sub_abba add_comm naturals.lt_def.
        repeat esplit; eauto.
        contradict H2.
        rewrite -H2 add_0_r //.
      + rewrite coeffs_above_degree // mul_0_l //.
  Qed.

  Theorem zero_ring_degree : 1%R = 0%R → ∀ f, degree f = 0%N.
  Proof.
    eauto using naturals.le_antisymm, zero_le,
    degree_bound, zero_ring_degeneracy.
  Qed.

  Theorem zero_ring_monic : 1%R = 0%R → ∀ f, monic f.
  Proof.
    move=> /zero_ring_degeneracy //.
  Qed.

  Theorem monic_prod_degree :
    ∀ f g, monic f → monic g → degree (f * g) = (degree f + degree g)%N.
  Proof.
    move=> f g H H0.
    case (classic (1%R = 0%R)) => [H1 | H1].
    - rewrite ? zero_ring_degree // add_0_r //.
    - apply naturals.le_antisymm, degree_lower_bound; auto using mul_degree.
      rewrite -leading_term_prod H H0 rings.M3 //.
  Qed.

  Theorem monic_prod : ∀ f g, monic f → monic g → monic (f * g).
  Proof.
    rewrite /monic => f g H H0.
    rewrite monic_prod_degree // -leading_term_prod H H0 rings.M3 //.
  Qed.

  Theorem monic_a_plus_x : ∀ α : R, monic (α + x).
  Proof.
    move=> α.
    case (classic (1%R = 0%R)) => [H | H]; auto using zero_ring_monic.
    rewrite /monic degree_of_a_plus_x // coefficient_add coeffs_above_degree
            ? degree_const ? x_coeff_of_x ? rings.A3 //;
            eauto using naturals.lt_succ.
  Qed.

  Theorem monic_powers : ∀ n f, monic f → monic (f^n).
  Proof.
    induction n using Induction => f H.
    - rewrite rings.pow_0_r /monic IRP_1 degree_const coeff_const //.
    - rewrite pow_succ_r.
      auto using monic_prod.
  Qed.

  Theorem monic_pow_degree : ∀ n f, monic f → degree (f^n) = (n * degree f)%N.
  Proof.
    induction n using Induction => f H.
    - rewrite rings.pow_0_r IRP_1 degree_const naturals.mul_0_l //.
    - rewrite pow_succ_r monic_prod_degree ? IHn -? add_1_r ? mul_distr_r
              ? mul_1_l; auto using monic_powers.
  Qed.

  Theorem degree_of_a_plus_x_to_n :
    1%R ≠ 0%R → ∀ n (α : R), degree ((α + x)^n) = n.
  Proof.
    move=> H n α.
    rewrite monic_pow_degree ? degree_of_a_plus_x ? mul_1_r;
      auto using monic_a_plus_x.
  Qed.

  Local Definition INR := (INR _) : N → R.
  Local Coercion INR : N >-> R.

  Lemma INR_0 : (0%R : R) = 0%N.
  Proof.
    rewrite /INR /rings.INR sum_neg; eauto using naturals.succ_lt.
  Qed.

  Lemma INR_1 : (1%R : R) = 1%N.
  Proof.
    rewrite /INR /rings.INR sum_0 //.
  Qed.

  Lemma binomial_theorem_zero :
    ∀ n (α : R), coefficient ((α + x)^n) 0 = (binomial n 0 * α^n)%R.
  Proof.
    induction n using Induction => α.
    - rewrite ? rings.pow_0_r binomial_zero /INR /rings.INR
              sum_0 // IRP_1 coeff_const rings.M3 //.
    - rewrite pow_succ_r D1_l coefficient_add binomial_zero
              (rings.M1 _ _ (α : poly)) const_coeff_mul IHn
      -1 ? (rings.pow_1_r _ x) coeff_of_x_mul_overflow ? binomial_zero
         ? pow_succ_r ? A3_r 1 ? rings.M1 ? rings.M2;
        eauto using naturals.succ_lt.
  Qed.

  Theorem generalized_binomial_theorem :
    ∀ n k (α : R), coefficient ((α + x)^n) k = (binomial n k * α^(n-k)%N)%R.
  Proof.
    (induction n using Induction => k α; case (classic (k = 0%N))) =>
    [-> | H | -> | /succ_0 [c -> {k}]];
      try rewrite binomial_theorem_zero sub_0_r //; first by
        rewrite rings.pow_0_r binomial_empty_set //
        -INR_0 mul_0_l -(rings.pow_0_r _ x) coeffs_of_x_ne_n //.
    rewrite pow_succ_r D1_l rings.M1 coefficient_add const_coeff_mul
            IHn -(rings.pow_1_r _ x) coeff_of_x_mul ? rings.pow_1_r ? IHn
                                     ? (rings.M1 _ α) -? rings.M2
    -1 ? {2} (rings.pow_1_r _ α) -? rings.pow_add_r; auto using one_le_succ.
    rewrite /naturals.one ? sub_succ ? sub_0_r ? sub_succ_r.
    case (classic (n - c = 0)%N) =>
    [/[dup] /sub_0_le /le_lt_or_eq [/[dup] H /S_lt H0 | ->] -> | /succ_0 [m H]].
    - rewrite ? binomial_overflow -? INR_0 ? mul_0_l ? rings.A3 //;
              eauto using naturals.lt_trans, naturals.succ_lt.
    - rewrite ? binomial_full pred_0 add_0_l rings.pow_0_r M3_r
              ? binomial_overflow -? INR_0 ? mul_0_l ? rings.A3 //;
              auto using naturals.succ_lt.
    - rewrite -{3}(sub_0_r c)
      -(sub_succ c 0) -/naturals.one {1}H pred_succ add_succ_r add_0_r -H
      -rings.D1 INR_add Pascal's_identity ? add_1_r //; auto using one_le_succ.
  Qed.

  Theorem binomial_theorem : ∀ n k, coefficient ((1 + x)^n) k = binomial n k.
  Proof.
    move=> n k.
    rewrite IRP_1 (generalized_binomial_theorem n k 1%R) rings.pow_1_l M3_r //.
  Qed.

  Theorem generalized_binomial_sum : ∀ n (α : R),
      (α + x)^n = sum _ (λ k, binomial n k * α^(n-k)%N * x^k) 0 n.
  Proof.
    move=> n α.
    rewrite (polynomial_sum_lemma n ((α + x)^n)).
    - case (classic (1%R = 0%R)) => [H | H].
      + rewrite zero_ring_degree; auto using zero_le.
      + rewrite degree_of_a_plus_x_to_n; auto using naturals.le_refl.
    - apply iterate_extensionality => k H.
      rewrite IRP_pow IRP_mul generalized_binomial_theorem //.
  Qed.

  Theorem binomial_sum : ∀ n, (1 + x)^n = sum _ (λ k, binomial n k * x^k) 0 n.
  Proof.
    move=> n.
    rewrite IRP_1 generalized_binomial_sum.
    f_equal.
    extensionality k.
    rewrite IRP_pow rings.pow_1_l -IRP_1 -rings.M2 rings.M3 //.
  Qed.

  Definition leading_coefficient f := coefficient f (degree f).

  Lemma leading_coefficient_zero : leading_coefficient 0 = 0%R.
  Proof.
    rewrite /leading_coefficient /degree.
    case excluded_middle_informative => [H | []] //.
    rewrite IRP_0 coeff_const //.
  Qed.

  Lemma leading_coefficient_nonzero : ∀ f, leading_coefficient f = 0%R → f = 0.
  Proof.
    move=> f H.
    apply NNPP => /degree_spec => /(_ (degree f)).
    intuition.
  Qed.

  Lemma const_mul_monic : ∀ a f, a ≠ 0%R → monic f → degree (a * f) = degree f.
  Proof.
    move=> a f H H0.
    apply naturals.le_antisymm, degree_lower_bound.
    - apply degree_bound => m H1.
      rewrite const_coeff_mul coeffs_above_degree // mul_0_r //.
    - rewrite const_coeff_mul H0 rings.M1 rings.M3 //.
  Qed.

  Lemma monic_division_algorithm_helper : ∀ a b n,
      monic b → (0 < degree b)%N → (degree a ≤ n)%N →
      ∃ q r, a = b * q + r ∧ (degree r < degree b)%N.
  Proof.
    case (classic (1%R = 0%R)) => [H | H a b n H0 H1 H2].
    { exists 0, 0.
      split; try apply zero_ring_degeneracy;
        rewrite ? IRP_1 ? IRP_0 ? H ? degree_const //. }
    elim/Induction: n a H2 => [a /naturals.le_lt_trans /(_ H1) |
                               n IHn a /le_lt_or_eq [/le_lt_succ /IHn // | H2]].
    { exists 0, a.
      split; rewrite ? mul_0_r ? rings.A3 //. }
    case (classic (degree a < degree b)%N) => [H3 | /naturals.le_not_gt [c H3]].
    { exists 0, a.
      split; auto; ring. }
    have H4 : (1 ≤ degree a)%N by rewrite H2; apply one_le_succ.
    elim (IHn (a - (leading_coefficient a) * x^c * b)) => [q [r [H5 H6]] | ].
    - exists (q + (leading_coefficient a) * x^c), r.
      split; auto.
      ring_simplify [H5]; rewrite -rings.A2 -H5; ring.
    - apply degree_bound => m /lt_le_succ /le_lt_or_eq.
      rewrite rings.sub_is_neg coefficient_add coefficient_neg => [[H5 | H5]].
      + rewrite ? coeffs_above_degree ? rings.A4 ? H2 //.
        eapply naturals.le_lt_trans; eauto.
        rewrite -H2 -H3 add_comm.
        eapply naturals.le_trans, O1_le, naturals.le_trans;
          eauto using mul_degree.
        rewrite degree_const degree_x_to_n ? add_0_l;
          auto using naturals.le_refl.
      + rewrite -H5 /leading_coefficient /monic -H2
        -rings.M2 const_coeff_mul (rings.M1 PR) coeff_of_x_mul
        -H3 ? sub_abba ? H0 ? M3_r ? rings.A4 //; auto using le_add_l.
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
    (split; rewrite /const) => [H | [c ->]]; last by auto using degree_const.
    exists (coefficient f 0).
    rewrite {1}(polynomial_sum_lemma 0 f) ? H ? sum_0 ? rings.pow_0_r ? M3_r //;
            auto using naturals.le_refl.
  Qed.

  Theorem eval_const : ∀ a b : R, a b = a.
  Proof.
    move=> a b.
    rewrite -(rings.M3 _ (a : poly)) rings.M1
    -(rings.pow_0_r _ x) eval_mul_const eval_x_to_n rings.pow_0_r M3_r //.
  Qed.

  Theorem eval_neg : ∀ f a, (-f) a = (- (f a))%R.
  Proof.
    move=> f a.
    rewrite -rings.mul_neg_1_l eval_mul IRP_1 IRP_neg eval_const mul_neg_1_l //.
  Qed.

  Infix "｜" := (rings.divide PR).

  Theorem root_classification : ∀ f (a : R), a ∈ roots f ↔ x - a｜f.
  Proof.
    ((case (classic (1%R = 0%R)) => H f a; split; rewrite roots_action);
     auto using zero_ring_degeneracy) => [H0 | H0 | [q ->]].
    - exists 1.
      apply zero_ring_degeneracy.
      rewrite IRP_1 IRP_0 H //.
    - have H1: degree (x - a) = 1%N.
      { apply linear_classification.
        exists (-a)%R, 1%R.
        rewrite -IRP_1 -IRP_neg rings.M3 rings.A1 //. }
      elim (monic_division_algorithm f (x - a)) => [q [r [H2]] | | ] //.
      + move: H1 => -> /lt_1_eq_0 /const_classification [c H1].
        exists q.
        rewrite rings.M1 H2.
        suff -> : r = 0 by rewrite A3_r.
        move: H2 H1 H0 IRP_0 -> => -> /[swap] -> <-.
        rewrite eval_add eval_mul eval_add eval_neg eval_x
                ? eval_const rings.A4 mul_0_l rings.A3 //.
      + rewrite /monic sub_is_neg rings.A1 IRP_neg monic_a_plus_x //.
      + rewrite H1.
        eauto using naturals.succ_lt.
    - rewrite eval_mul eval_add eval_neg eval_x
              ? eval_const rings.A4 mul_0_r //.
  Qed.

  Theorem coeffs_of_0 : ∀ n, coefficient 0 n = 0%R.
  Proof.
    (move: classic => /[swap] n /(_ (n = 0%N)) => [[-> | /succ_0 [m ->]]]);
      rewrite ? IRP_0 ? coeff_const ? coeffs_above_degree /degree //.
    (case excluded_middle_informative => [_ | []] //; try apply eq_sym);
      eauto using naturals.lt_succ, IRP_0.
  Qed.

  Section Integral_domain_theorems.

    Hypothesis is_ID : is_integral_domain ring.

    Theorem poly_is_ID : is_integral_domain PR.
    Proof.
      move: is_ID => [C N].
      split => [a b H | ].
      - case (classic (a = 0)), (classic (b = 0)); try tauto.
        have: leading_coefficient a ≠ 0%R; have: leading_coefficient b ≠ 0%R;
          eauto using leading_coefficient_nonzero.
        rewrite /leading_coefficient => H2 H3.
        have: coefficient (a * b) (degree a + degree b) ≠ 0%R
          by rewrite -leading_term_prod => /C [ | ] //.
        rewrite H coeffs_of_0 //.
      - rewrite /is_nontrivial IRP_1 IRP_0 IRP_eq //.
    Qed.

    Theorem monic_nonzero : ∀ f, monic f → f ≠ 0.
    Proof.
      move: is_ID => [_].
      rewrite /monic /is_nontrivial => N f /[swap] ->.
      rewrite coeffs_of_0 // => /(@eq_sym (elts ring)) //.
    Qed.

    Theorem prod_root : ∀ f g, roots (f * g) = (roots f) ∪ (roots g).
    Proof.
      move: is_ID => [C N] f g.
      apply Extensionality => z.
      split => [/[dup] /roots_in_R H | /Pairwise_union_classification].
      - rewrite Pairwise_union_classification (reify H)
                ? (roots_action _ (mkSet H)) eval_mul => /C //.
      - move=> [/[dup] /roots_in_R H | /[dup] /roots_in_R H];
                 rewrite (reify H) ? (roots_action _ (mkSet H)) eval_mul =>
        ->; rewrite ? mul_0_l ? mul_0_r //.
    Qed.

    Theorem monic_linear_root : ∀ (a : R), roots (x - a) = {a, a}.
    Proof.
      move=> a.
      apply Extensionality => z.
      (split; rewrite ? Singleton_classification) =>
      [/[dup] /roots_in_R H | ->].
      - rewrite (reify H) => /roots_action.
        rewrite eval_add eval_x eval_neg eval_const -{2}(rings.A3 _ a) => <-.
        rewrite -rings.A2 A4_l A3_r //.
      - rewrite roots_action eval_add eval_x eval_neg eval_const rings.A4 //.
    Qed.

    Theorem nonzero_prod_degree :
      ∀ f g, f ≠ 0 → g ≠ 0 → degree (f * g) = (degree f + degree g)%N.
    Proof.
      move: is_ID => [C N] f g H H0.
      apply naturals.le_antisymm; auto using mul_degree.
      apply degree_lower_bound.
      rewrite -leading_term_prod =>
      /C [/leading_coefficient_nonzero | /leading_coefficient_nonzero] //.
    Qed.

    Theorem monic_linear_degree : ∀ (a : R), degree (x - a) = 1%N.
    Proof.
      move: is_ID => [C N] a.
      rewrite -(degree_of_a_plus_x N (-a)) -IRP_neg rings.A1 //.
    Qed.

    Theorem finite_roots : ∀ f, f ≠ 0 → finite (roots f).
    Proof.
      move=> f H.
      remember (degree f) as d.
      elim/Strong_Induction: d f H Heqd => d H f H0 Heqd.
      case (classic (roots f = ∅)) =>
      [-> | /Nonempty_classification [a /[dup] /roots_in_R H1]];
        auto using (naturals_are_finite 0).
      rewrite (reify H1) => /root_classification => [[g H2]].
      move: H2 H0 Heqd prod_root -> => /cancellation_ne0 [H0 H2] Heqd ->.
      apply finite_unions_are_finite.
      - eapply H; eauto.
        rewrite Heqd nonzero_prod_degree // monic_linear_degree add_1_r;
          auto using naturals.succ_lt.
      - rewrite monic_linear_root.
        auto using singletons_are_finite.
    Qed.

    Theorem root_degree_bound : ∀ f, f ≠ 0 → (# roots f ≤ degree f)%N.
    Proof.
      move: is_ID => [C NT] f H.
      remember (degree f) as d.
      elim/Strong_Induction: d f H Heqd => d IHd f H Heqd.
      case (classic (roots f = ∅)) =>
      [-> | /Nonempty_classification [a /[dup] /roots_in_R H1]];
        rewrite ? card_empty; auto using zero_le.
      rewrite (reify H1) => /root_classification => [[g H2]].
      move: H2 H prod_root Heqd IHd -> => /cancellation_ne0 [H0 H2] -> ->.
      rewrite nonzero_prod_degree // monic_linear_degree {1}add_1_r => H.
      eapply naturals.le_trans; eauto using finite_union_card_bound.
      apply naturals.le_cross_add; auto using naturals.succ_lt.
      rewrite monic_linear_root singleton_card.
      auto using naturals.le_refl.
    Qed.

    Theorem cyclotomic_leading_coeff : ∀ (d : N) (a : R),
        (1 ≤ d)%N → coefficient (x^d - a) d = 1%R.
    Proof.
      rewrite /rings.sub => d a H.
      rewrite coefficient_add coefficient_neg coeffs_of_x_to_n
              coeffs_above_degree -? neg_0 ? rings.A3_r ? degree_const
              ? naturals.lt_0_le_1 //.
    Qed.

    Theorem cyclotomic_degree : ∀ (d : N) (a : R),
        (1 ≤ d)%N → degree (x^d - a) = d.
    Proof.
      move: is_ID => [C N] d a H.
      apply naturals.le_antisymm.
      - eapply naturals.le_trans; eauto using add_degree.
        rewrite degree_x_to_n // IRP_neg degree_const max_0_r.
        eauto using naturals.le_refl.
      - apply degree_lower_bound.
        rewrite cyclotomic_leading_coeff //.
    Qed.

    Theorem cyclotomic_monic : ∀ (d : N) (a : R), (1 ≤ d)%N → monic (x^d - a).
    Proof.
      rewrite /monic => d a H.
      rewrite cyclotomic_degree ? cyclotomic_leading_coeff //.
    Qed.

  End Integral_domain_theorems.

End Polynomial_theorems.
