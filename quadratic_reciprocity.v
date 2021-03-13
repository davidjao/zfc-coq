Set Warnings "-ambiguous-paths".
Require Export integers_mod_n.

Section Pretty_picture_lemmas.

  Variable p q : N.
  Hypothesis prime_p : prime p.
  Hypothesis prime_q : prime q.
  Hypothesis distinct : p ≠ q.
  Hypothesis odd_p : 2 < p.
  Hypothesis odd_q : 2 < q.

  Lemma pp_helper_1 : ∀ x y k : N,
      (y < x)%N → ⌊p * k / q⌋ = x → (1 ≤ k ≤ # QR q)%N → (y + 1 ≤ # QR p)%N.
  Proof.
    intros x y k H H0 [H1 H2].
    rewrite add_1_r.
    apply lt_le_succ, INZ_le in H.
    eapply INZ_le, (ordered_rings.le_trans ℤ_order); eauto.
    rewrite <-H0.
    apply IZQ_le, floor_lower.
    rewrite inv_div; try now apply (pos_ne_0 ℤ_order), odd_prime_positive.
    apply (mul_denom_l ℚ_order); simpl.
    { now apply IZQ_lt, odd_prime_positive. }
    apply INZ_le, (mul_le_l ℤ_order (p : Z)), IZQ_le in H2; simpl in *;
      fold integers.le in *; auto using odd_prime_positive.
    eapply (le_lt_trans ℚ_ring_order); eauto; simpl.
    replace 1%Q with (1%Z : Q) by auto.
    rewrite IZQ_add, IZQ_mul.
    apply IZQ_lt, (O3_iff ℤ_order 2); simpl;
      try now apply (ordered_rings.zero_lt_2 ℤ_order).
    replace (2 * (p * (# QR q))) with (p * (2 * # QR q)) by ring.
    replace (2 * (q * (# QR p + 1))) with (q * (2 * (# QR p) + 2)) by ring.
    rewrite <-? size_of_QR_in_Z; auto.
    replace (p * (q - 1)) with (p * q + -p) by ring.
    replace (q * (p - 1 + 2)) with (p * q + q) by ring.
    apply integers.O1, (integers.lt_trans _ 0); auto using odd_prime_positive.
    rewrite (ordered_rings.lt_shift ℤ_order), (neg_neg ℤ), integers.A3;
      now apply odd_prime_positive.
  Qed.

  Lemma rectangle_slice_equiv : ∀ n : N, ({x of type 𝐙 | 1 ≤ x ≤ n} ~ n)%set.
  Proof.
    intros n.
    set (f := sets.functionify (λ x : N, x + 1)).
    assert (n ⊂ domain f) as H.
    { unfold f.
      rewrite sets.functionify_domain.
      intros x H.
      eauto using elements_of_naturals_are_naturals, elts_in_set. }
    apply injection_restriction in H.
    2: { apply Injective_classification.
         intros x y H0 H1 H2.
         unfold f in *.
         rewrite @sets.functionify_domain, (reify H0), (reify H1),
         ? @functionify_action in *.
         rewrite ? (integers.A1 _ 1) in H2.
         apply set_proj_injective, (cancellation_add ℤ), INZ_eq in H2.
         now f_equal. }
    rewrite H.
    apply cardinality_eq, Extensionality.
    split; intros H0.
    - apply Specify_classification in H0 as [H0 H1].
      rewrite (reify H0), despecify in *.
      destruct H1 as [H1 H2].
      apply Specify_classification.
      split; unfold f.
      { now rewrite sets.functionify_range. }
      apply le_def in H1 as [c H1].
      unfold integers.one in H1.
      rewrite H1, integers.A1, INZ_add, add_1_r in *.
      apply INZ_le, lt_le_succ, lt_is_in in H2.
      exists c.
      rewrite Pairwise_intersection_classification.
      repeat split; auto.
      + rewrite sets.functionify_domain.
        eauto using elts_in_set.
      + now rewrite @functionify_action, <-add_1_r, <-INZ_add.
    - apply Specify_classification in H0 as [H0 [c [H1 H2]]].
      apply Pairwise_intersection_classification in H1 as [H1 H3].
      unfold f in *.
      rewrite @sets.functionify_domain, @sets.functionify_range in *.
      apply Specify_classification.
      rewrite (reify H3), @functionify_action, <-H2, despecify in *.
      repeat split; auto; unfold integers.one; rewrite INZ_add, add_1_r;
        apply INZ_le.
      + apply one_le_succ.
      + now rewrite <-lt_le_succ, lt_is_in.
  Qed.

  Lemma rectangle_slice_finite : ∀ n : N, finite {x of type 𝐙 | 1 ≤ x ≤ n}.
  Proof.
    intros n.
    exists n.
    auto using rectangle_slice_equiv.
  Qed.

  Lemma rectangle_slice_card : ∀ n : N, # {x of type 𝐙 | 1 ≤ x ≤ n} = n.
  Proof.
    intros n.
    auto using equivalence_to_card, rectangle_slice_equiv.
  Qed.

  Lemma triangle_duality : ∀ x y : Z, (p * x / q < y → x < q * y / p)%Q.
  Proof.
    intros x y H.
    apply (lt_not_ge ℚ_ring_order); fold rationals.le.
    intros H0.
    rewrite ? inv_div in H, H0;
      try now apply (pos_ne_0 ℤ_order), odd_prime_positive.
    apply (O3 ℚ_ring_order (q : Q)), (O3_r ℚ_ring_order (p^-1 : Q)) in H;
      simpl in *; try (now apply IZQ_lt, odd_prime_positive);
        try now apply (inv_lt ℚ_order), IZQ_lt, odd_prime_positive.
    rewrite <-IZQ_mul in *.
    replace (q * (p * x * q^-1) * p^-1)%Q with (x : Q) in H.
    2: { field_simplify_eq; repeat split; auto;
         intros H1; apply IZQ_eq, (pos_ne_0 ℤ_order) in H1; auto;
         now apply odd_prime_positive. }
    eapply (lt_irrefl ℚ_ring_order (x : Q)), (lt_le_trans ℚ_ring_order); eauto.
  Qed.

  Lemma q_ndiv_p : ¬ q｜p.
  Proof.
    intros H.
    destruct prime_p as [H0 H1], prime_q as [H2 H3].
    apply H1 in H as [H | H]; try contradiction.
    apply assoc_pm in H as [H | H]; try now apply distinct, INZ_eq.
    contradiction (ordered_rings.lt_antisym ℤ_order 0 (p : Z));
      try now apply odd_prime_positive.
    rewrite (ordered_rings.lt_shift ℤ_order); simpl.
    rewrite <-H, integers.A3.
    auto using odd_prime_positive.
  Qed.

  Lemma empty_diagonal : ∀ x y : Z, 1 ≤ x ≤ # QR q → ¬ (p * x / q = y)%Q.
  Proof.
    intros x y H H0.
    apply Qequiv, eq_sym in H0; auto using integers.zero_ne_1.
    2: { now apply (pos_ne_0 ℤ_order), odd_prime_positive. }
    rewrite (rings.M3_r ℤ), integers.M1 in H0.
    destruct H as [H H1], (Euclid's_lemma p x q) as [H2 | H2];
      unfold divide, rings.divide; eauto using q_ndiv_p.
    apply lt_0_le_1 in H.
    apply div_le, le_not_gt in H2; auto; simpl in H2.
    contradict H2.
    eapply (le_lt_trans ℤ_order); eauto; simpl.
    replace (q : Z) with (q - 1 + 1) at 2 by ring.
    rewrite size_of_QR_in_Z, <-(integers.A3 (# QR q)) at 1;
      auto using odd_prime_positive.
    replace (2 * (# QR q) + 1) with (# QR q + 1 + # QR q) by ring.
    apply (O1_r ℤ_order), (ordered_rings.O0 ℤ_order); simpl;
      auto using integers.zero_lt_1, naturals.le_refl.
    now apply lt_0_le_1, INZ_le, size_QR_ge_1.
  Qed.

  Lemma pp_helper_2 : ∀ x y k : N,
      y < x → ⌊p * k / q⌋ = x → (1 ≤ k ≤ # QR q)%N → (y + 1 < p * k / q)%Q.
  Proof.
    intros x y k H H0 H1.
    apply INZ_lt, lt_le_succ, INZ_le, IZQ_le in H.
    rewrite <-add_1_r, <-H0, <-INZ_add, <-IZQ_add in H.
    eapply (le_lt_trans ℚ_ring_order); eauto; simpl.
    destruct (floor_refl (p * k / q)); auto.
    apply eq_sym, empty_diagonal in H2; intuition; now apply INZ_le.
  Qed.

  Definition rectangle :=
    {z of type 𝐙 × 𝐙 | 1 ≤ π1 z ≤ # QR q ∧ 1 ≤ π2 z ≤ # QR p}.
  Definition lower_triangle :=
    {z of type 𝐙 × 𝐙 | 1 ≤ π1 z ≤ # QR q ∧ 1 ≤ π2 z ≤ # QR p ∧
                       ((π2 z : Z) < p * (π1 z : Z) / q)%Q}.
  Definition upper_triangle :=
    {z of type 𝐙 × 𝐙 | 1 ≤ π1 z ≤ # QR q ∧ 1 ≤ π2 z ≤ # QR p ∧
                       ((π1 z : Z) < q * (π2 z : Z) / p)%Q}.

  Definition lower_triangle_f (a : N) :=
    {z in lower_triangle | ∃ x y : Z, z = (x,y) ∧ x = a}.
  Definition upper_triangle_f (b : N) :=
    {z in upper_triangle | ∃ x y : Z, z = (x,y) ∧ y = b}.

  Lemma rectangle_prod :
    rectangle =
    {x of type 𝐙 | 1 ≤ x ≤ # QR q} × {x of type 𝐙 | 1 ≤ x ≤ # QR p}.
  Proof.
    apply Extensionality.
    split; intros H.
    - apply Specify_classification in H as [H H0].
      rewrite (reify H), despecify in *.
      apply Product_classification.
      exists ((π1 (exist H)) : Z), ((π2 (exist H)) : Z).
      repeat split; try (apply Specify_classification; rewrite ? despecify);
        intuition; eauto using elts_in_set, eq_sym, π_image.
    - apply Product_classification in H as [a [b [H [H0 H1]]]]; subst.
      apply Specify_classification in H as [H H1], H0 as [H0 H2].
      assert ((a, b) ∈ 𝐙 × 𝐙) as H3.
      { apply Product_classification; eauto. }
      apply Specify_classification.
      now rewrite (reify H), (reify H0), (reify H3), despecify,
      π1_action, π2_action in *.
  Qed.

  Lemma rectangle_finite : finite rectangle.
  Proof.
    rewrite rectangle_prod.
    auto using finite_products_are_finite, rectangle_slice_finite.
  Qed.

  Lemma rectangle_card : (# rectangle = (# QR p) * (# QR q))%N.
  Proof.
    rewrite rectangle_prod, finite_products_card, ? rectangle_slice_card,
    mul_comm; auto using rectangle_slice_finite.
  Qed.

  Lemma lower_subset : lower_triangle ⊂ rectangle.
  Proof.
    intros z H.
    apply Specify_classification in H as [H H0].
    apply Specify_classification.
    now rewrite (reify H), despecify in *.
  Qed.

  Lemma upper_subset : upper_triangle ⊂ rectangle.
  Proof.
    intros z H.
    apply Specify_classification in H as [H H0].
    apply Specify_classification.
    now rewrite (reify H), despecify in *.
  Qed.

  Lemma disjoint_triangles : lower_triangle ∩ upper_triangle = ∅.
  Proof.
    apply NNPP.
    rewrite Nonempty_classification.
    intros [z H].
    apply Pairwise_intersection_classification in H as [H H0].
    apply Specify_classification in H as [H H1], H0 as [_ H2].
    rewrite (reify H), despecify in *.
    destruct H1 as [H1 [H3 H4]], H2 as [H2 [H5 H6]].
    rewrite ? inv_div in H4, H6;
      try now apply (pos_ne_0 ℤ_order), odd_prime_positive.
    apply (O3 ℚ_ring_order (p : Q)), (O3_r ℚ_ring_order (q^-1 : Q)) in H6;
      simpl in *; try (now apply IZQ_lt, odd_prime_positive);
      try now apply (inv_lt ℚ_order), IZQ_lt, odd_prime_positive.
    rewrite <-IZQ_mul in *.
    replace (p * (q * (π2 (exist H) : Z) * p^-1) * q^-1)%Q
      with ((π2 (exist H) : Z) : Q) in H6.
    2: { field_simplify_eq; repeat split; auto;
         intros H7; apply IZQ_eq, (pos_ne_0 ℤ_order) in H7; auto;
         now apply odd_prime_positive. }
    contradiction (lt_antisym ℚ_ring_order ((π2 (exist H) : Z) : Q)
                              (p * (π1 (exist H) : Z) * q^-1)%Q).
  Qed.

  Theorem rectangle_union : lower_triangle ∪ upper_triangle = rectangle.
  Proof.
    apply Subset_equality; intros z H.
    - apply Pairwise_union_classification in H as [H | H];
        auto using lower_subset, upper_subset.
    - apply Specify_classification in H as [H H0].
      rewrite (reify H), despecify in *.
      apply Pairwise_union_classification.
      destruct (rationals.T (π2 (exist H) : Z) (p * (π1 (exist H) : Z) / q)) as
          [[H3 [_ _]] | [[_ [H3 _]] | [_ [_ H3]]]].
      + apply or_introl, Specify_classification.
        rewrite despecify.
        intuition.
      + apply eq_sym, empty_diagonal in H3; intuition.
      + apply or_intror, Specify_classification.
        rewrite despecify.
        intuition eauto using triangle_duality.
  Qed.

  Theorem sum_lower_triangle :
    # lower_triangle = sum_N (λ l, QR_ε_exp (p*l) q) 1 (# QR q).
  Proof.
    apply INZ_eq, eq_sym.
    rewrite <-INZ_sum, <-(sum_card 1 (# QR q) lower_triangle lower_triangle_f).
    - apply iterate_extensionality.
      intros k H.
      unfold QR_ε_exp.
      repeat destruct excluded_middle_informative; try contradict n;
        try (apply integers.O2); auto using odd_prime_positive.
      2: { apply lt_0_le_1, INZ_le; intuition. }
      destruct constructive_indefinite_description.
      rewrite integers.A3 in e.
      apply INZ_eq, eq_sym, equivalence_to_card, cardinality_sym.
      assert (∀ y, (k : Z, y+1) ∈ 𝐙 × 𝐙) as H0.
      { intros y.
        apply Product_classification; eauto using elts_in_set. }
      set (f := sets.functionify (λ y : N, exist (H0 y))).
      assert (x ⊂ domain f) as H1.
      { unfold f.
        rewrite sets.functionify_domain.
        intros z H1.
        eauto using elements_of_naturals_are_naturals, elts_in_set. }
      apply injection_restriction in H1.
      2: { apply Injective_classification.
           intros x1 x2 H2 H3 H4.
           unfold f in *.
           rewrite @sets.functionify_domain, (reify H2), (reify H3),
           ? @functionify_action in *.
           unfold elt_to_set, proj1_sig, integers.one in *.
           apply Ordered_pair_iff in H4 as [H4 H5].
           apply set_proj_injective in H5.
           rewrite ? INZ_add, ? (add_comm _ 1) in H5.
           apply INZ_eq, naturals.cancellation_add in H5.
           now inversion H5. }
      replace (lower_triangle_f k) with (push_forward f x); auto.
      apply Extensionality.
      split; intros H2.
      + apply Specify_classification in H2 as [H2 [y [H3 H4]]]; subst.
        apply Pairwise_intersection_classification in H3 as [H3 H4].
        apply Specify_classification.
        unfold f in *.
        rewrite sets.functionify_domain in H4.
        set (γ := exist H4 : N).
        rewrite (reify H4) in *; fold γ in H3, H4 |-*.
        apply lt_is_in in H3.
        split; rewrite functionify_action; try exists k, (γ + 1); eauto.
        apply Specify_classification.
        split; eauto using elts_in_set.
        rewrite despecify.
        replace (π1 (exist (H0 γ))) with (k : Z);
          replace (π2 (exist (H0 γ))) with (γ + 1 : Z);
          try (unfold π1, π2;
               repeat destruct constructive_indefinite_description;
               repeat destruct a; apply Ordered_pair_iff in e1; destruct e1;
               now apply set_proj_injective).
        repeat split; auto; try (apply INZ_le; intuition); unfold integers.one.
        * rewrite INZ_add, add_1_r.
          apply INZ_le, one_le_succ.
        * rewrite INZ_add.
          eapply INZ_le, pp_helper_1; eauto.
        * rewrite <-IZQ_add.
          eapply pp_helper_2; eauto.
          now apply INZ_lt.
      + apply Specify_classification in H2 as [H2 [κ [y [H3 H4]]]]; subst.
        apply Specify_classification in H2 as [H2 H3].
        apply Specify_classification.
        unfold f in *.
        rewrite sets.functionify_range, sets.functionify_domain.
        split; auto.
        rewrite (reify H2), despecify in *.
        destruct H3 as [[H3 H4] [[H5 H6] H7]].
        apply lt_0_le_1, lt_def in H5 as [c [H5 H8]].
        unfold integers.zero, not in *.
        rewrite INZ_eq, integers.A3 in *.
        apply neq_sym, succ_0 in H5 as [m H5].
        subst.
        exists m.
        rewrite @functionify_action, Pairwise_intersection_classification.
        replace (π1 (exist H2)) with (k : Z) in *;
          replace (π2 (exist H2)) with (y : Z) in *;
          try (unfold π1, π2;
               repeat destruct constructive_indefinite_description;
               repeat destruct a; apply Ordered_pair_iff in e1; destruct e1;
               now apply set_proj_injective).
        subst; repeat split; eauto using elts_in_set.
        * apply lt_is_in, lt_le_succ, INZ_le.
          rewrite <-e.
          now apply IZQ_le, floor_upper, or_introl.
        * simpl.
          now rewrite <-add_1_r, <-INZ_add.
    - eapply subsets_of_finites_are_finite;
        eauto using rectangle_finite, lower_subset.
    - intros k H z H0.
      now apply Specify_classification in H0.
    - intros z; split; intros H.
      + apply Specify_classification in H as [H H0].
        pose proof H as H1.
        apply Product_classification in H1 as [z1 [z2 [H1 [H2 H3]]]]; subst.
        rewrite (reify H1), (reify H2), (reify H), despecify in *.
        rewrite π1_action, π2_action in H0.
        destruct H0 as [[H0 H3] [[H4 H5] H6]].
        apply lt_0_le_1, lt_def in H0 as [c [H0 H7]].
        rewrite integers.A3 in H7.
        exists c.
        unfold integers.zero, not in H0.
        rewrite INZ_eq in H0.
        apply neq_sym, succ_0 in H0 as [m H0].
        subst.
        repeat split.
        * auto using one_le_succ.
        * apply INZ_le; congruence.
        * apply Specify_classification.
          split; try now exists (exist H1 : Z), (exist H2 : Z).
          apply Specify_classification.
          rewrite despecify, π1_action, π2_action.
          repeat split; intuition.
          rewrite H7.
          apply INZ_le.
          auto using one_le_succ.
        * intros x' [[H0 H8] H9].
          apply Specify_classification in H9 as [H9 [x [y' [H10 H11]]]]; subst.
          rewrite <-π_image, π1_action, π2_action in H10.
          apply Ordered_pair_iff in H10 as [H10 H11].
          unfold IZS in H10, H11.
          apply set_proj_injective in H10, H11.
          apply INZ_eq; congruence.
      + destruct H as [y [[[H H0] H1] H2]].
        now apply Specify_classification in H1.
  Qed.

End Pretty_picture_lemmas.

Section Quadratic_reciprocity.

  Variable p q : N.
  Hypothesis prime_p : prime p.
  Hypothesis prime_q : prime q.
  Hypothesis distinct : p ≠ q.
  Hypothesis odd_p : 2 < p.
  Hypothesis odd_q : 2 < q.

  Theorem lower_to_upper : (lower_triangle q p ~ upper_triangle p q)%set.
  Proof.
    assert (lower_triangle q p = lower_triangle q p ∩ (𝐙 × 𝐙)) as H.
    { apply eq_sym, Intersection_subset.
      intros z H.
      now apply Specify_classification in H. }
    replace (lower_triangle q p) with
        (domain (restriction (swap_function 𝐙 𝐙) (lower_triangle q p))).
    2: { now rewrite restriction_domain, swap_domain. }
    rewrite injective_into_image.
    - apply cardinality_eq, Extensionality.
      split; intros H0.
      + apply Specify_classification in H0 as [H0 [z' [H1 H2]]].
        rewrite restriction_domain, swap_domain, <-H, <-restriction_action in *.
        2: { rewrite swap_domain; congruence. }
        apply Specify_classification in H1 as [H1 H3].
        pose proof H1 as H4.
        apply Product_classification in H4 as [a [b [H4 [H5 H6]]]]; subst.
        rewrite (reify H4), (reify H5), (reify H1), despecify, <-π_image,
        swap_action in *; auto using elts_in_set.
        apply Specify_classification.
        assert ((π2 (exist H1) : Z, π1 (exist H1) : Z) ∈ 𝐙 × 𝐙) as H6.
        { apply Product_classification; eauto using elts_in_set. }
        unfold IZS in *.
        rewrite π1_action, π2_action, (reify H6), despecify, π1_action,
        π2_action in *; intuition.
      + apply Specify_classification in H0 as [H0 H1].
        pose proof H0 as H2.
        apply Product_classification in H2 as [a [b [H2 [H3 H4]]]]; subst.
        apply Specify_classification.
        rewrite (reify H2), (reify H3), (reify H0), despecify, <-π_image,
        π1_action, π2_action, restriction_range, swap_range, restriction_domain,
        swap_domain, <-H in *.
        assert ((exist H3 : Z, exist H2 : Z) ∈ 𝐙 × 𝐙) as H4.
        { apply Product_classification; eauto using elts_in_set. }
        unfold IZS in *.
        split; auto.
        assert ((exist H3 : Z, exist H2 : Z) ∈ lower_triangle q p) as H5.
        { apply Specify_classification.
          rewrite Product_classification.
          split; eauto using elts_in_set.
          unfold IZS.
          rewrite (reify H4), despecify, π1_action, π2_action; intuition. }
        exists (exist H3 : Z, exist H2 : Z).
        rewrite <-restriction_action, swap_action; auto.
        now rewrite swap_domain, <-H.
    - apply Injective_classification.
      intros x y H0 H1 H2.
      rewrite <-? restriction_action in *;
        rewrite ? restriction_domain, ? swap_domain, <-? H in *; try congruence.
      apply Specify_classification in H0, H1.
      pose proof swap_bijective 𝐙 𝐙 as [H3 H4].
      rewrite Injective_classification, swap_domain in H3.
      intuition.
  Qed.

  Theorem sum_upper_triangle :
    # (upper_triangle p q) = sum_N (λ l, QR_ε_exp (q*l) p) 1 (# QR p).
  Proof.
    apply equivalence_to_card.
    rewrite <-lower_to_upper, <-card_equiv, sum_lower_triangle;
      eauto using cardinality_refl, subsets_of_finites_are_finite,
      rectangle_finite, lower_subset.
  Qed.

  Theorem Pretty_Picture_Lemma :
    (sum_N (λ l, QR_ε_exp (p*l) q) 1 (# QR q) +
     sum_N (λ l, QR_ε_exp (q*l) p) 1 (# QR p) = (# QR p) * (# QR q))%N.
  Proof.
    rewrite <-sum_lower_triangle, <-sum_upper_triangle, <-rectangle_card,
    <-rectangle_union, finite_union_cardinality;
      eauto using subsets_of_finites_are_finite, lower_subset, upper_subset,
      rectangle_finite, disjoint_triangles.
  Qed.

  Theorem quadratic_reciprocity :
    legendre_symbol _ (p mod q) * legendre_symbol _ (q mod p) =
    (-(1))^((# QR p) * (# QR q)).
  Proof.
    rewrite ? Gauss's_Lemma_a, <-(rings.pow_add_r ℤ), Pretty_Picture_Lemma;
      auto using p_odd, q_ndiv_p, odd_prime_positive.
  Qed.

End Quadratic_reciprocity.
