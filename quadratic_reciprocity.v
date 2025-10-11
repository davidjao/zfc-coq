Set Warnings "-ambiguous-paths,-non-reference-hint-using".
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
    move=> x y k /lt_le_succ /INZ_le /[swap] <- H.
    rewrite add_1_r => [[H0 H1]].
    eapply INZ_le, (ordered_rings.le_trans ℤ_order), IZQ_le, floor_lower; eauto.
    rewrite inv_div; try now apply (pos_ne_0 ℤ_order), odd_prime_positive.
    apply (mul_denom_l ℚ_order); first by apply IZQ_lt, odd_prime_positive.
    apply INZ_le, (mul_le_l ℤ_order (p : Z)), IZQ_le in H1 =>
    /=; auto using odd_prime_positive.
    eapply (le_lt_trans ℚ_ring_order); eauto; simpl.
    rewrite -[1%Q]/(1%Z : Q) IZQ_add IZQ_mul -IZQ_lt.
    apply (O3_iff ℤ_order 2) =>
            /=; eauto using (ordered_rings.zero_lt_2 ℤ_order : 0 < 2).
    have -> : 2 * (p * (# QR q)) = p * (2 * # QR q) by ring.
    have -> : 2 * (q * (# QR p + 1)) = q * (2 * (# QR p) + 2) by ring.
    rewrite -? size_of_QR_in_Z; auto.
    ring_simplify.
    apply integers.O1, (integers.lt_trans _ 0); auto using odd_prime_positive.
    by apply (neg_lt_0 ℤ_order (p : Z)), odd_prime_positive.
  Qed.

  Lemma rectangle_slice_equiv : ∀ n : N, ({x of type ℤ | 1 ≤ x ≤ n} ~ n)%set.
  Proof.
    move=> n.
    set (f := sets.functionify (λ x : N, x + 1)).
    have /injection_restriction ->: n ⊂ domain f;
      try (rewrite Injective_classification /f @sets.functionify_domain =>
             x y H0 H1; rewrite (reify H0) (reify H1) ? functionify_action
                                ? (integers.A1 _ 1)
             => /set_proj_injective /(cancellation_add ℤ) /INZ_eq -> //).
    { rewrite /f sets.functionify_domain => x H.
      eauto using elements_of_naturals_are_naturals, elts_in_set. }
    apply cardinality_eq, Extensionality => z.
    split => [/Specify_classification [H0] |
               /Specify_classification
                [H0 [c [/Pairwise_intersection_classification [H1 H2]]]]].
    - rewrite (reify H0) despecify Specify_classification /integers.one =>
                [[/le_def [c H1] H2]].
      split; rewrite /f ? sets.functionify_range // H1 integers.A1
                     INZ_add add_1_r in H2 |-*.
      apply INZ_le, lt_le_succ, lt_is_in in H2.
      exists c.
      rewrite Pairwise_intersection_classification sets.functionify_domain
              functionify_action -add_1_r -INZ_add.
      eauto using elts_in_set.
    - rewrite /f sets.functionify_domain sets.functionify_range
              Specify_classification in H0 H2 |-*.
      rewrite (reify H2) functionify_action => <-.
      repeat split; auto; rewrite ? despecify /integers.one INZ_add add_1_r
                                  ? INZ_le -? lt_le_succ ? (lt_is_in _ n);
        eauto using elts_in_set, naturals.lt_succ.
  Qed.

  Lemma rectangle_slice_finite : ∀ n : N, finite {x of type ℤ | 1 ≤ x ≤ n}.
  Proof.
    eexists; eauto using rectangle_slice_equiv.
  Qed.

  Lemma rectangle_slice_card : ∀ n : N, # {x of type ℤ | 1 ≤ x ≤ n} = n.
  Proof.
    eauto using equivalence_to_card, rectangle_slice_equiv.
  Qed.

  Lemma triangle_duality : ∀ x y : Z, (p * x / q < y → x < q * y / p)%Q.
  Proof.
    move=> x y H.
    apply (lt_not_ge ℚ_ring_order) => H0.
    move: (odd_prime_positive _ odd_p) (odd_prime_positive _ (odd_q)) =>
          /[dup] H1 /(pos_ne_0 ℤ_order) /= ? /[dup] H2 /(pos_ne_0 ℤ_order) /= ?.
    rewrite ? inv_div //= in H, H0.
    move: H H1 H2 => /(O3 ℚ_ring_order (q : Q)) /(O3_r ℚ_ring_order (p^-1)) /=.
    rewrite ? IZQ_lt -IZQ_mul (IZQ_mul q y) =>
              /[swap] /(inv_lt ℚ_order) /[swap] /[apply] /[apply].
    (have ->: (q * (p * x * q^-1) * p^-1)%Q = (x : Q);
     first by field_simplify_eq; split; auto => /IZQ_eq //) => ?.
    eapply (lt_irrefl ℚ_ring_order (x : Q)), (lt_le_trans ℚ_ring_order); eauto.
  Qed.

  Lemma q_ndiv_p : ¬ q｜p.
  Proof.
    move: prime_p prime_q => [H H0] [H1 H2] /H0 [H3 | /assoc_pm [H3 | H3]];
                               try contradiction; try by apply distinct, INZ_eq.
    contradiction (ordered_rings.lt_antisym ℤ_order 0 (p : Z));
      rewrite ? (ordered_rings.lt_shift ℤ_order (p : Z)) /= -? H3 ? integers.A3;
      auto using odd_prime_positive.
  Qed.

  Lemma empty_diagonal : ∀ x y : Z, 1 ≤ x ≤ # QR q → ¬ (p * x / q = y)%Q.
  Proof.
    move=> x y [/lt_0_le_1 H H0] /Qequiv /(@eq_sym Z).
    move: (odd_prime_positive _ odd_q) =>
    /(pos_ne_0 ℤ_order) /[swap] /[apply] /(_ integers.zero_ne_1).
    rewrite (rings.M3_r ℤ : ∀ a, a * 1 = a) integers.M1 => H1.
    elim (Euclid's_lemma p x q); rewrite /divide /rings.divide;
      eauto using q_ndiv_p => /div_le => /(_ H) /le_not_gt /= [].
    eapply (le_lt_trans ℤ_order); eauto => /=.
    have {2}-> : (q : Z) = q - 1 + 1 by ring.
    rewrite size_of_QR_in_Z // -{1}(integers.A3 (# QR q)) integers.D1.
    rewrite integers.M3 -integers.A2; apply (lt_cross_add ℤ_order);
      first apply lt_0_le_1, INZ_le, size_QR_ge_1; auto; apply lt_succ.
  Qed.

  Lemma pp_helper_2 : ∀ x y k : N,
      y < x → ⌊p * k / q⌋ = x → (1 ≤ k ≤ # QR q)%N → (y + 1 < p * k / q)%Q.
  Proof.
    move=> x y k /INZ_lt /lt_le_succ /INZ_le /IZQ_le.
    rewrite -add_1_r => /[swap] <-.
    rewrite -INZ_add -IZQ_add -? INZ_le => H H0.
    eapply (le_lt_trans ℚ_ring_order); eauto => /=.
    elim (floor_refl (p * k / q)); auto => /(@eq_sym Q) /empty_diagonal //.
  Qed.

  Definition rectangle :=
    {z in ℤ × ℤ | ∃ x y : Z, z = (x,y) ∧ 1 ≤ x ≤ # QR q ∧ 1 ≤ y ≤ # QR p}.
  Definition lower_triangle :=
    {z in ℤ × ℤ | ∃ x y : Z,
       z = (x,y) ∧ 1 ≤ x ≤ # QR q ∧ 1 ≤ y ≤ # QR p ∧ (y < p * x / q)%Q}.
  Definition upper_triangle :=
    {z in ℤ × ℤ | ∃ x y : Z,
       z = (x,y) ∧ 1 ≤ x ≤ # QR q ∧ 1 ≤ y ≤ # QR p ∧ (x < q * y / p)%Q}.

  Definition lower_triangle_f (a : N) :=
    {z in lower_triangle | ∃ x y : Z, z = (x,y) ∧ x = a}.
  Definition upper_triangle_f (b : N) :=
    {z in upper_triangle | ∃ x y : Z, z = (x,y) ∧ y = b}.

  Lemma rectangle_prod :
    rectangle =
    {x of type ℤ | 1 ≤ x ≤ # QR q} × {x of type ℤ | 1 ≤ x ≤ # QR p}.
  Proof.
    apply Extensionality => z.
    split => [/Specify_classification [H [a [b H0]]] |
              /Product_classification
               [a [b [/Specify_classification [H] /[swap] [[]]
                       /Specify_classification [H0]]]]].
    - rewrite Product_classification.
      exists a, b.
      rewrite ? Specify_classification ? despecify.
      intuition eauto using elts_in_set.
    - rewrite (reify H) (reify H0) ? despecify Specify_classification
              Product_classification => H1 -> H2.
      repeat split; eauto.
  Qed.

  Lemma rectangle_finite : finite rectangle.
  Proof.
    rewrite rectangle_prod.
    auto using finite_products_are_finite, rectangle_slice_finite.
  Qed.

  Lemma rectangle_card : (# rectangle = (# QR p) * (# QR q))%N.
  Proof.
    rewrite rectangle_prod product_card ? rectangle_slice_card
            1 ? mul_comm; auto using rectangle_slice_finite.
  Qed.

  Lemma lower_subset : lower_triangle ⊂ rectangle.
  Proof.
    move=> z /Specify_classification [H [x [y [H0 [H1 [H2 H3]]]]]].
    apply Specify_classification.
    eauto 6.
  Qed.

  Lemma upper_subset : upper_triangle ⊂ rectangle.
  Proof.
    move=> z /Specify_classification [H [x [y [H0 [H1 [H2 H3]]]]]].
    apply Specify_classification.
    eauto 6.
  Qed.

  Lemma disjoint_triangles : lower_triangle ∩ upper_triangle = ∅.
  Proof.
    apply NNPP.
    rewrite Nonempty_classification =>
    [[z /Pairwise_intersection_classification [
          /Specify_classification [H [x1 [y1 [-> [H0 [H1]]]]]] /[swap]
           /Specify_classification
           [H3 [x2 [y2 [/Ordered_pair_iff
                         [/set_proj_injective <- /set_proj_injective <-]
                         [H4 [H5]]]]]]]]].
    (rewrite ? inv_div; try now apply (pos_ne_0 ℤ_order), odd_prime_positive)
    => /(O3 ℚ_ring_order (p : Q)) /(O3_r ℚ_ring_order (q^-1 : Q)).
    move: (odd_prime_positive _ odd_q) (inv_lt ℚ_order (q : Q)) =>
          /[dup] ? /IZQ_lt /[swap] /[apply] /[swap] /[apply].
    move: (odd_prime_positive _ odd_p) => /[dup] ? /IZQ_lt /[swap] /[apply] /=.
    rewrite -? IZQ_mul.
    have ->: (p * (q * y1 * p^-1) * q^-1 = (y1 : Q))%Q =>
           [ | /(lt_antisym ℚ_ring_order)? ?] //.
    field_simplify_eq; split => /IZQ_eq /(pos_ne_0 ℤ_order) //.
  Qed.

  Theorem rectangle_union : lower_triangle ∪ upper_triangle = rectangle.
  Proof.
    apply Subset_equality =>
    [z /Pairwise_union_classification [H | H] |
     z /Specify_classification [H [x [y [H0 [H1 H2]]]]]];
      auto using lower_subset, upper_subset.
    apply Pairwise_union_classification.
    case (rationals.T y (p * x / q)) =>
    [[H3 [_ _]] | [[_ [/(@eq_sym Q) /empty_diagonal H3 _]] | [_ [_ H3]]]]
      //; [left | right]; rewrite Specify_classification;
      eauto 8 using triangle_duality.
  Qed.

  Theorem sum_lower_triangle :
    # lower_triangle = sum_N (λ l, QR_ε_exp (p*l) q) 1 (# QR q).
  Proof.
    apply INZ_eq, eq_sym.
    rewrite -INZ_sum -(sum_card 1 (# QR q) lower_triangle lower_triangle_f) =>
    [ | k H z /Specify_classification [H0] | z | ]
      //; eauto using subsets_of_finites_are_finite,
    rectangle_finite, lower_subset.
    - split => [/Specify_classification
                 [H [x [y [H0 [[/lt_0_le_1 /lt_def
                                 [c [/INZ_eq /neq_sym /succ_0 [m H1] H2]] H3]
                                 [[H4 H5] H6]]]]]] |
                [y [[[H H0] /Specify_classification [H1]] H2]]] //.
      move: integers.A3 H2 H1 H0 H3 H6 -> => -> {x} -> {c} -> H0 H1.
      exists (S m).
      (repeat split; auto using one_le_succ; first by apply INZ_le) =>
      [ | x' [[H2 H3] /Specify_classification
                      [H7 [x [y' [/Ordered_pair_iff [/set_proj_injective <- H8]
                                   /INZ_eq H9]]]]]] //.
      do 2 rewrite Specify_classification ? Product_classification.
      repeat split; eauto using elts_in_set.
      exists (S m), y.
      repeat split; eauto.
      apply INZ_le, one_le_succ.
    - apply iterate_extensionality => k H.
      rewrite /QR_ε_exp /sig_rect.
      (repeat case excluded_middle_informative) =>
        [H0 H1 | [] | []]; try apply integers.O2; auto using odd_prime_positive.
      2: { apply lt_0_le_1, INZ_le; intuition. }
      elim constructive_indefinite_description => x.
      rewrite integers.A3 => H2.
      apply INZ_eq, eq_sym, equivalence_to_card, cardinality_sym.
      have H3: ∀ y, (k : Z, y+1) ∈ ℤ × ℤ =>
             [y | ]; rewrite ? Product_classification; eauto using elts_in_set.
      set (f := sets.functionify (λ y : N, mkSet (H3 y))).
      have /injection_restriction: x ⊂ domain f.
      { rewrite /f sets.functionify_domain => z H4.
        eauto using elements_of_naturals_are_naturals, elts_in_set. }
      suff <-: push_forward f x = lower_triangle_f k => [H4 | ].
      { apply H4, Injective_classification => x1 x2.
        rewrite /f sets.functionify_domain => H5 H6.
        rewrite (reify H5) (reify H6) ? @functionify_action /elt_to_set
                /proj1_sig /integers.one ? INZ_add ? (add_comm _ 1) =>
        /Ordered_pair_iff [_ /set_proj_injective] /INZ_eq
         /naturals.cancellation_add [H7] //. }
      apply Extensionality => z.
      split => [/Specify_classification [] /[swap]
                 [[y [/Pairwise_intersection_classification
                       [] H4 /[swap] <-]]] |
                /Specify_classification
                 [/[swap] [[κ [y [-> ->]]]]
                   /Specify_classification
                   [H4 [k' [y' [H5 [[H6 H7] [[/lt_0_le_1 /lt_def
                                               [[c H8 [/INZ_eq /neq_sym /succ_0
                                                        [m H9] H10]]] H11]
                                               H12]]]]]]]].
      + rewrite Specify_classification /f sets.functionify_domain
                sets.functionify_range => H5.
        move: H4.
        rewrite (reify H5) -[elt_to_set]/INS -? lt_is_in functionify_action =>
                  /[dup] H4 /INZ_lt H6.
        repeat (split; auto using elts_in_set;
                try apply Specify_classification); exists k, ((mkSet H5:N) + 1);
          repeat split; auto; try (apply INZ_le; intuition);
            rewrite /integers.one -? IZQ_add -? [1%Z : Q]/(1%Q) ? INZ_add
                    ? INZ_le; eauto using pp_helper_1, pp_helper_2, le_add_l.
      + move: integers.A3 H5 H6 H7 H10 H11 H12 -> => /Ordered_pair_iff [] =>
        /set_proj_injective <- /set_proj_injective <- H5 H6 H7 H10 H11.
        apply Specify_classification.
        rewrite /f sets.functionify_range sets.functionify_domain.
        split.
        { apply Product_classification; eauto using elts_in_set. }
        exists m.
        rewrite functionify_action /= H7 H9 -add_1_r
        -INZ_add Pairwise_intersection_classification.
        repeat split; eauto using elts_in_set.
        apply lt_is_in, lt_le_succ, INZ_le.
        rewrite -H9 -H7 -H2.
          by apply IZQ_le, floor_upper, or_introl.
  Qed.

End Pretty_picture_lemmas.

Section Quadratic_reciprocity.

  Context {p q : N}.
  Hypothesis prime_p : prime p.
  Hypothesis prime_q : prime q.
  Hypothesis distinct : p ≠ q.
  Hypothesis odd_p : 2 < p.
  Hypothesis odd_q : 2 < q.

  Theorem lower_to_upper : (lower_triangle q p ~ upper_triangle p q)%set.
  Proof.
    have H: lower_triangle q p = lower_triangle q p ∩ (ℤ × ℤ).
    { apply eq_sym, Intersection_subset => z /Specify_classification [H] //. }
    have ->: lower_triangle q p =
    domain (restriction (swap_function ℤ ℤ) (lower_triangle q p)) by
        rewrite restriction_domain swap_domain.
    rewrite injective_into_image ? Injective_classification;
      try (move=> ? ?; rewrite ? restriction_domain ? swap_domain -? H =>
             /[dup] ? /Specify_classification ? /[dup] ? /Specify_classification
              ?; rewrite -? restriction_action ? swap_domain -? H //;
              move: (swap_bijective ℤ ℤ) => [/Injective_classification];
                                            rewrite swap_domain; intuition).
    apply cardinality_eq, Extensionality => z.
    split => [/Specify_classification |
               /Specify_classification
                [/[swap] [[x [y [-> [H0 [H1 H2]]]]]]] H3].
    - rewrite restriction_domain swap_domain -H =>
                [[H0 [z' /[dup] [[H1 H2]] []]]].
      (rewrite -restriction_action ? swap_domain; try congruence) =>
        /Specify_classification [H3 [x [y [H4 [H5 [H6 H7]]]]]]; subst.
      move: H3 => /Product_classification =>
            [[x' [y' [H2 [H3 /Ordered_pair_iff []]]]]]; intuition; subst.
      rewrite Specify_classification
              -restriction_action ? swap_domain -? H // swap_action //
                                  Product_classification; split; eauto 8.
    - rewrite Specify_classification restriction_range swap_range
              restriction_domain swap_domain -H.
      split; auto.
      exists (y, x).
      have H4: (y, x) ∈ lower_triangle q p;
        [ rewrite Specify_classification Product_classification |
          rewrite -restriction_action ? swap_action ? swap_domain -? H];
        repeat split; eauto 8 using elts_in_set.
  Qed.

  Theorem sum_upper_triangle :
    # (upper_triangle p q) = sum_N (λ l, QR_ε_exp (q*l) p) 1 (# QR p).
  Proof.
    apply equivalence_to_card.
    rewrite <-lower_to_upper, card_equiv, ? sum_lower_triangle;
      eauto using cardinality_refl, subsets_of_finites_are_finite,
      rectangle_finite, lower_subset.
  Qed.

  Theorem quadratic_reciprocity :
    legendre_symbol (p mod q) * legendre_symbol (q mod p) =
    (-1)^((# QR p) * (# QR q)).
  Proof.
    (rewrite -> ? Gauss's_Lemma_a, <-(rings.pow_add_r ℤ), <-sum_lower_triangle,
    <-sum_upper_triangle, <-rectangle_card, <-rectangle_union,
      <-finite_union_cardinality; eauto using p_odd, q_ndiv_p);
    eauto using odd_prime_positive, disjoint_triangles, lower_subset,
      upper_subset, subsets_of_finites_are_finite, rectangle_finite.
  Qed.

End Quadratic_reciprocity.
