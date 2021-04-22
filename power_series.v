Set Warnings "-uniform-inheritance,-ambiguous-paths".
Require Export rings.

Section Power_series_construction.

  Variable Ring : ring.

  Declare Scope Ring_scope.
  Delimit Scope Ring_scope with ring.
  Bind Scope Ring_scope with Ring.
  Open Scope Ring_scope.
  Notation R := (elts Ring).
  Infix "+" := (add Ring) : Ring_scope.
  Infix "*" := (mul Ring) : Ring_scope.
  Notation "0" := (zero Ring) : Ring_scope.
  Notation "1" := (one Ring) : Ring_scope.
  Notation "- a" := (neg Ring a) : Ring_scope.

  Add Ring generic_ring : (ringify Ring).

  Definition power_series_set := {x in P (ω × Ring) | is_function x ω Ring}.

  Definition power_series := elts power_series_set.

  Definition series_functionify : power_series → function.
  Proof.
    move=> f.
    move: (elts_in_set f) => /Specify_classification [H H0].
    exact (mkFunc H0).
  Defined.

  Theorem series_functionify_injective :
    ∀ f g, series_functionify f = series_functionify g → f = g.
  Proof.
    rewrite /series_functionify => [[f F]] [g G].
    (repeat destruct iffLR => /=) => H.
    apply set_proj_injective => /=.
    suff -> : f = graph (mkFunc i0); auto.
    suff -> : g = graph (mkFunc i2); auto.
    apply f_equal, func_ext => /= //.
    congruence.
  Qed.

  Theorem series_functionify_inv :
    ∀ f : N → R, exists ! f', series_functionify f' = functionify f.
  Proof.
    move=> f.
    have H: graph (functionify f) ∈ power_series_set.
    { apply Specify_classification, conj; auto using functionify_is_function.
      apply Powerset_classification, functionify_graph. }
    exists (mkSet H).
    have H0: series_functionify (mkSet H) = functionify f.
    { rewrite /series_functionify.
      repeat destruct iffLR => /=.
      apply function_record_injective => /= //.
      rewrite functionify_range //. }
    split; auto => x'.
      by rewrite -{1}H0 => /series_functionify_injective.
  Qed.

  Theorem series_functionify_domain : ∀ f, domain (series_functionify f) = ω.
  Proof.
    move=> [f F].
    rewrite /series_functionify.
      by destruct iffLR.
  Qed.

  Theorem series_functionify_range : ∀ f, range (series_functionify f) = Ring.
  Proof.
    move=> [f F].
    rewrite /series_functionify.
      by destruct iffLR.
  Qed.

  Definition coefficient : power_series → N → R.
  Proof.
    move=> f.
    rewrite /N -(series_functionify_domain f) -(series_functionify_range f).
    exact (lambdaify (series_functionify f)).
  Defined.

  Definition seriesify : (N → R) → power_series.
  Proof.
    move=> f.
    elim (constructive_definite_description _ (series_functionify_inv f))
    => [x H].
    exact x.
  Defined.

  Theorem seriesify_coefficient : ∀ f, seriesify (coefficient f) = f.
  Proof.
    rewrite /coefficient /eq_rect /seriesify /sig_rect /functionify => f.
    elim constructive_definite_description => x.
    destruct series_functionify_domain, series_functionify_range.
    elim constructive_indefinite_description => f' [H [H0 H1]] H2.
    apply series_functionify_injective.
    rewrite H2.
    apply func_ext => // x' H3.
    rewrite H in H3.
      by rewrite (reify H3) H1.
  Qed.

  Theorem seriesify_injective : ∀ f g, seriesify f = seriesify g → f = g.
  Proof.
    rewrite /seriesify /sig_rect => f g.
    elim constructive_definite_description => x H.
    elim constructive_definite_description => x' H' H0.
    move: H0 H H' -> => -> H.
      by apply functionify_injective.
  Qed.

  Theorem coefficient_seriesify : ∀ f, coefficient (seriesify f) = f.
  Proof.
    move=> f.
    apply seriesify_injective.
      by rewrite seriesify_coefficient.
  Qed.

  Theorem power_series_extensionality :
    ∀ f g, (coefficient f = coefficient g) → f = g.
  Proof.
    move=> f g H.
      by rewrite -(seriesify_coefficient f) -(seriesify_coefficient g) H.
  Qed.

  Definition add : power_series → power_series → power_series.
  Proof.
    move=> a b.
    exact (seriesify (λ n, add _ (coefficient a n) (coefficient b n))).
  Defined.

  Declare Scope Series_scope.
  Delimit Scope Series_scope with series.
  Bind Scope Series_scope with power_series.
  Open Scope Series_scope.

  Infix "+" := add : Series_scope.

  Theorem add_comm : ∀ f g, f + g = g + f.
  Proof.
    rewrite /add => f g.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    extensionality n.
    ring.
  Qed.

  Theorem add_assoc : ∀ f g h, add f (add g h) = add (add f g) h.
  Proof.
    rewrite /add => f g h.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    extensionality n.
    ring.
  Qed.

  Definition ISS (a : power_series) := elt_to_set a.
  Definition IRS a := seriesify (λ n, If n = 0%N then a else 0%ring).

  Definition zero := IRS 0.
  Definition one := IRS 1.

  Notation "0" := zero : Series_scope.
  Notation "1" := one : Series_scope.
  Coercion ISS : power_series >-> set.
  Coercion IRS : R >-> power_series.

  Theorem zero_series_const : 0 = seriesify (λ n, 0%ring).
  Proof.
    apply power_series_extensionality.
    rewrite /zero /IRS ? coefficient_seriesify.
    extensionality n.
      by elim excluded_middle_informative.
  Qed.

  Theorem add_0_l : ∀ f, 0 + f = f.
  Proof.
    rewrite zero_series_const /add /zero => f.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    extensionality n.
    ring.
  Qed.

  Definition neg f := seriesify (λ n, neg _ (coefficient f n)).

  Notation "- f" := (neg f) : Series_scope.

  Theorem add_opp_r : ∀ f, f + -f = 0.
  Proof.
    rewrite zero_series_const /add /neg /zero => f.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    extensionality n.
    ring.
  Qed.

  Definition mul : power_series → power_series → power_series.
  Proof.
    move=> a b.
    exact
      (seriesify
         (λ n,
          sum _ (λ k, mul _ (coefficient a k) (coefficient b (n-k))) 0 n)).
  Defined.

  Lemma mul_comm_coeff :
    ∀ n f g, (sum _ (λ k, (f k) * (g (n-k))) 0 n) =
             (sum _ (λ k, (g k) * (f (n-k))) 0 n).
  Proof.
    induction n using Induction => f g; first by rewrite ? sum_0 sub_diag M1.
    rewrite sum_succ; auto using zero_le.
    have -> : sum _ (λ k : N, f k * g (S n - k)) 0 n =
              sum _ (λ k : N, f k * g (n - k + 1)%N) 0 n.
    { apply iterate_extensionality => k [H [c <-]].
      do 2 f_equal.
      rewrite add_1_r (naturals.add_comm k) sub_abba -add_succ_l.
      apply /(@eq_sym N) /sub_spec /naturals.add_comm. }
    rewrite (IHn f (λ k, g (k + 1)%N))
    -{5}add_1_r (naturals.add_comm _ 1) {2}/naturals.one {2}/sum
        iterate_lower 1 ? A1 1 ? M1 ? sub_diag ? sub_0_r => *; try ring.
    f_equal.
    move: {IHn} f g.
    induction n using Induction =>
    f g; try tauto; try rewrite add_0_r sum_0 ? iterate_0 ? sub_diag add_1_r //.
    rewrite sum_succ; auto using zero_le.
    have -> : sum _ (λ k : N, g (k + 1)%N * f (S n - k)) 0 n =
              sum _ (λ k : N, g (k + 1)%N * f (S n - (n - (n - k)))) 0 n.
    { apply iterate_extensionality => k [[c <-] [d <-]].
        by rewrite ? naturals.add_0_l {4} (naturals.add_comm c d) ? sub_abba. }
    rewrite (IHn (λ k, f (S n - (n - k)))) -? add_1_r ? naturals.add_0_l
    ? (naturals.add_comm 1) ? add_1_r
    -/(sum _ (λ k : N, g k * f (S n - (n - (S n - k)))) 1 (S n))
    -/(sum _ (λ k : N, g k * f (S (S n) - k)) 1 (S (S n)))
    ? sum_succ ? sub_diag; try (exists n; by rewrite naturals.add_comm add_1_r);
      first by (exists (n+1)%N; rewrite naturals.add_comm -? add_1_r).
    do 2 f_equal;
      try rewrite sub_0_r -? add_1_r ? (naturals.add_comm _ 1) ? sub_abba //.
    elim (classic (n = 0%N)) =>
    [-> | /succ_0 [m ->]]; first by rewrite ? sum_neg;
      eauto using naturals.succ_lt.
    rewrite -? add_1_r ? (naturals.add_comm m).
    apply iterate_extensionality => k [[c <-] [d <-]].
    do 2 f_equal.
    suff -> : (1+c+d+1 = 1+d+(1+c))%N; suff -> : (1+c+d = c+(1+d))%N;
      try suff -> : (1+d+(1+c)+1 = 1+d+1+(1+c))%N; try ring.
    rewrite ? sub_abba ? (naturals.add_assoc) sub_abba //.
  Qed.

  Infix "*" := mul : Series_scope.

  Theorem mul_comm : ∀ f g, f * g = g * f.
  Proof.
    rewrite /mul => f g.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    extensionality n.
    apply mul_comm_coeff.
  Qed.

  Lemma mul_assoc_coeff : ∀ n a b c,
      sum _ (λ k, (a k) *
                  sum _ (λ j, (b j) * (c (n - k - j))) 0 (n-k))%ring 0 n =
      sum _ (λ k, (sum _ (λ j, (a j) *
                               (b (k - j))) 0 k) * (c (n - k)))%ring 0 n.
  Proof.
    move=> n a b.
    elim/Induction: n =>
    [n | n /[swap] c /(_ (λ n, c (n+1)%N)) /=];
      first by rewrite ? sum_0 sub_0_r sum_0 sub_0_r M2.
    rewrite ? sum_succ ? sub_diag ? sum_0 ? sub_diag; auto using zero_le.
    elim (classic (n = 0%N)) =>
    [-> IH | /succ_0 [m -> IH]];
      first by rewrite ? sum_0 sub_0_r sum_succ ? sum_0
                       ? sub_diag ? sub_0_r; auto using zero_le; ring.
    have -> : (sum _ (λ k, a k * sum _ (λ j, b j * c (S (S m) - k - j))
                                         0 (S (S m) - k)) 0 (S m) =
               sum _ (λ k, a k * sum _ (λ j, b j * c (S (S m) - k - j))
                                         0 (S ((S m) - k))) 0 (S m))%ring.
    { apply iterate_extensionality => k [H [d <-]].
        by rewrite (naturals.add_comm k) -add_succ_l ? sub_abba. }
    have -> : (sum _ (λ k, a k * sum _ (λ j, b j * c (S (S m) - k - j))
                                         0 (S ((S m) - k))) 0 (S m) =
               sum _ (λ k, a k * (sum _ (λ j, b j * c (S (S m) - k - j))
                                          0 ((S m) - k))) 0 (S m) +
               sum _ (λ k, a k * b (S ((S m) - k)) * (c 0%N)) 0 (S m))%ring.
    { rewrite -sum_dist.
      apply iterate_extensionality => k [H [d <-]].
      rewrite -M2 -D1_l sum_succ ? (naturals.add_comm k) -? add_succ_l
                        ? sub_abba ? sub_diag; auto using zero_le. }
    have -> : (sum _ (λ k, a k * sum _ (λ j, b j * c (S (S m) - k - j))
                                         0 (S m - k)) 0 (S m) =
               sum _ (λ k, (a k * sum _ (λ j, b j * c (S m - k - j + 1)%N)
                                      0 (S m - k))%ring) 0 (S m))%ring.
    { apply iterate_extensionality => k [H [d <-]].
      f_equal.
      apply iterate_extensionality => j [H1 [e]].
      rewrite (naturals.add_comm k) sub_abba => <-.
      rewrite -add_succ_l sub_abba (naturals.add_comm _ e)
      -add_succ_l ? sub_abba add_1_r //. }
    rewrite IH -A2.
    f_equal.
    - apply iterate_extensionality => k [H [d <-]].
      do 2 f_equal.
      rewrite ? (naturals.add_comm k) -add_succ_l ? sub_abba add_1_r //.
    - rewrite D1 M2 ? (M1 _ _ (c 0%N)) sum_mul.
      f_equal.
      apply iterate_extensionality => k [H [d <-]].
      rewrite M1 ? (naturals.add_comm k) -add_succ_l ? sub_abba //.
  Qed.

  Theorem mul_assoc : ∀ a b c, a * (b * c) = (a * b) * c.
  Proof.
    rewrite /mul => a b c.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    extensionality n.
    apply mul_assoc_coeff.
  Qed.

  Theorem mul_distr_l : ∀ a b c, a * (b + c) = a * b + a * c.
  Proof.
    rewrite /mul /add => a b c.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    extensionality n.
    rewrite -sum_dist.
    apply iterate_extensionality => k _.
    ring.
  Qed.

  Theorem mul_1_r : ∀ f, f * 1 = f.
  Proof.
    rewrite /mul /one /IRS => f.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    apply functional_extensionality => n.
    induction n using Induction; rewrite ? sum_0 ? sum_succ; auto using zero_le;
      first by case excluded_middle_informative; rewrite sub_diag M1 ? M3 //.
    case excluded_middle_informative; rewrite sub_diag // => _.
    rewrite M1 M3 -{2}(A3 _ (coefficient f (S n))).
    f_equal => {IHn}.
    (induction n using Induction; rewrite ? sum_0 -1 ? {2} IHn ? sum_succ;
     first by (case excluded_middle_informative; rewrite sub_0_r ? mul_0_r //)
     => /(@eq_sym N) /PA4); auto using zero_le.
    elim excluded_middle_informative;
      first by rewrite -add_1_r naturals.add_comm sub_abba => /(@eq_sym N) /PA4.
    rewrite -> mul_0_r, A1, A3 => _.
    apply iterate_extensionality => k H.
    f_equal.
    (repeat elim excluded_middle_informative; auto) =>
    [/sub_ne_0_lt /(lt_trans _ (S n) (S (S n))) /(_ (succ_lt (S n)))
      /[swap] /sub_0_le /lt_le_trans /[apply] /lt_irrefl | ] //.
    move: H => [H [c <-] /sub_0_le /(le_trans (S k)) /succ_le] =>
    /(_ (iffLR (succ_le k (k+c)) (le_add k c))) /not_succ_le //.
  Qed.

  Theorem mul_1_l : ∀ f, 1 * f = f.
  Proof.
    move=> f.
      by rewrite mul_comm mul_1_r.
  Qed.

  Theorem mul_distr_r : ∀ a b c, (a + b) * c = a * c + b * c.
  Proof.
    move=> a b c.
      by rewrite ? (mul_comm _ c) mul_distr_l.
  Qed.

  Definition power_series_ring :=
    mkRing _ zero one add mul neg add_0_l add_comm add_assoc mul_1_l mul_comm
           mul_assoc mul_distr_r add_opp_r.

  Add Ring power_series_ring : (ringify power_series_ring).

  Theorem IRS_eq : ∀ a b, IRS a = IRS b → a = b.
  Proof.
    rewrite /IRS => a b /(f_equal (λ x, coefficient x 0%N)).
    rewrite ? coefficient_seriesify.
    elim excluded_middle_informative => //.
  Qed.

  Theorem IRS_add : ∀ a b, IRS (a + b)%ring = IRS a + IRS b.
  Proof.
    rewrite /IRS /add => a b.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    extensionality n.
    elim excluded_middle_informative => * //.
    ring.
  Qed.

  Theorem IRS_neg : ∀ a, IRS (-a)%ring = - IRS a.
  Proof.
    rewrite /IRS /neg => a.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    extensionality n.
    elim excluded_middle_informative => * //.
    ring.
  Qed.

  Theorem IRS_mul : ∀ a b, IRS (a * b)%ring = IRS a * IRS b.
  Proof.
    rewrite /IRS /mul => a b.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    extensionality n.
    elim excluded_middle_informative =>
    [-> | H]; rewrite ? sum_0 -1 ? (sum_of_0 _ n).
    - (repeat elim excluded_middle_informative => //) => [[]].
        by rewrite sub_0_r.
    - apply iterate_extensionality => k H0.
      repeat elim excluded_middle_informative;
        rewrite ? sum_of_0 ? mul_0_r ? mul_0_l // => H1 H2.
      move: H2 H1 H -> => <-.
      rewrite sub_0_r //.
  Qed.

  Definition shift f :=
    seriesify (λ n, If n = 0%N then 0%ring else (coefficient f (n - 1))).

  Definition x := shift 1.

  Theorem mul_x_shift : ∀ f, x * f = shift f.
  Proof.
    rewrite /x /one /IRS /shift /mul => x.
    apply power_series_extensionality.
    rewrite ? coefficient_seriesify.
    extensionality n.
    elim excluded_middle_informative => [-> | /succ_0 [m ->]].
    - rewrite sum_0 sub_0_l.
      (elim excluded_middle_informative; try tauto) => _.
      ring.
    - rewrite -(singleton_sum _ 1 (S m) (coefficient x (S m - 1)));
        auto using one_le_succ.
      apply iterate_extensionality => k H.
      (repeat elim excluded_middle_informative) =>
      [-> /(@eq_sym N) /PA4 | /[swap] | -> | | -> | ];
        rewrite ? sub_diag ? mul_0_l ? M3 // =>
      /[swap] /sub_0_le H0 H1 /succ_0 [c H2].
      move: H2 H0 H1 -> => /le_antisymm /(_ (one_le_succ c)) //.
  Qed.

  Theorem coefficient_add : ∀ n f g,
      coefficient (f + g) n = (coefficient f n + coefficient g n)%ring.
  Proof.
    rewrite /add => n f g.
      by rewrite coefficient_seriesify.
  Qed.

  Theorem coefficient_neg :
    ∀ n f, coefficient (-f) n = (- coefficient f n)%ring.
  Proof.
    rewrite /neg => n f.
      by rewrite coefficient_seriesify.
  Qed.

  Theorem coefficient_mul :
    ∀ n f g, coefficient (f * g) n =
             sum _ (λ k, (coefficient f k * coefficient g (n-k))%ring) 0 n.
  Proof.
    rewrite /mul => n f g.
    by rewrite coefficient_seriesify.
  Qed.

  Lemma const_coeff_mul : ∀ (n : N) (c : R) f,
      coefficient (IRS c * f) n = (c * coefficient f n)%ring.
  Proof.
    rewrite /IRS /mul => n c f.
    rewrite coefficient_seriesify
    -(singleton_sum _ 0 n (c * coefficient f n)%ring); auto using zero_le.
    apply iterate_extensionality => k H0.
    rewrite coefficient_seriesify.
    (repeat elim excluded_middle_informative; try tauto) =>
    [-> | _]; rewrite ? sub_0_r ? mul_0_l //.
  Qed.

End Power_series_construction.
