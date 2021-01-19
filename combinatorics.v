Require Export cardinality integers_mod_n.

Definition permutations (n : N) := size_of_bijections n n.

Definition factorial (n : N) := (prod integers (λ x, x : Z) 1 n) : Z.

Lemma two_sided_inverse_bijective : ∀ A B,
  (∃ (f : elts A → elts B) (g : elts B → elts A),
        ((∀ a : elts A, g (f a) = a) ∧ (∀ b : elts B, f (g b) = b)))
  → (A ~ B)%set.
Proof.
  intros A B [f [g [H H0]]].
  exists (functionify _ _ f).
  set (γ := functionify _ _ g).
  unfold functionify in *.
  destruct constructive_indefinite_description as [g'].
  destruct a as [H1 [H2 H3]].
  clear γ.
  destruct constructive_indefinite_description as [f'].
  destruct a as [H4 [H5 H6]].
  repeat split; try tauto; subst.
  - rewrite Injective_classification.
    intros x y H1 H2 H7.
    assert (g' (f' x) = g' (f' y)) as H8 by congruence.
    rewrite H4 in H1, H2.
    replace x with (proj1_sig (exist (λ x, x ∈ range g') _ H1)) in *
      by auto.
    replace y with (proj1_sig (exist (λ x, x ∈ range g') _ H2)) in *
      by auto.
    now rewrite ? H6, ? H3, ? H in H8.
  - rewrite Surjective_classification.
    intros y H1.
    exists (g' y).
    split.
    + rewrite H4.
      apply function_maps_domain_to_range.
      congruence.
    + rewrite H5 in H1.
      replace y with (proj1_sig (exist (λ x, x ∈ domain g') _ H1)) in *
        by auto.
      now rewrite H3, H6, H0.
Qed.

Definition inverse_image_of_element : function → set → set.
Proof.
  intros f y.
  destruct (excluded_middle_informative (y ∈ range f)).
  - exact ({x in domain f | f x = y}).
  - exact ∅.
Defined.

Section orbit_stabilizer_cardinality_helper.

  Variable f : function.
  Variable x : set.
  Hypothesis H : (∀ y, y ∈ range f → inverse_image_of_element f y ~ x)%set.

  Definition oschf : set → function.
  Proof.
    intros z.
    destruct (excluded_middle_informative (z ~ x)%set).
    - destruct (constructive_indefinite_description _ e) as [g [H1 [H2 H3]]].
      exact g.
    - exact empty_function.
  Defined.

  Theorem oschf_domain : ∀ z, (z ~ x)%set → domain (oschf z) = z.
  Proof.
    intros z H0.
    unfold oschf.
    destruct excluded_middle_informative; try tauto.
    destruct constructive_indefinite_description.
    now repeat destruct a.
  Qed.

  Theorem oschf_range : ∀ z, (z ~ x)%set → range (oschf z) = x.
  Proof.
    intros z H0.
    unfold oschf.
    destruct excluded_middle_informative; try tauto.
    destruct constructive_indefinite_description.
    now repeat destruct a.
  Qed.

  Theorem oschf_bijective : ∀ z, (z ~ x)%set → bijective (oschf z).
  Proof.
    intros z H0.
    unfold oschf.
    destruct excluded_middle_informative; try tauto.
    destruct constructive_indefinite_description.
    now repeat destruct a.
  Qed.

  Theorem orbit_stabilizer_cardinality : (domain f ~ range f × x)%set.
  Proof.
    destruct (function_construction
                (domain f) (range f × x)
                (λ x,
                 (f x, (oschf (inverse_image_of_element f (f x)) x))))
      as [g [H0 [H1 H2]]].
    { intros a H0.
      unfold oschf.
      destruct excluded_middle_informative.
      - destruct constructive_indefinite_description as [g].
        repeat destruct a0.
        apply Product_classification.
        exists (f a), (g a).
        repeat split; auto.
        + now apply function_maps_domain_to_range.
        + rewrite <-e1.
          apply function_maps_domain_to_range.
          rewrite e0.
          unfold inverse_image_of_element.
          destruct excluded_middle_informative.
          * now apply Specify_classification.
          * contradict n.
            now apply function_maps_domain_to_range.
      - contradict n.
        now apply H, function_maps_domain_to_range. }
    exists g.
    repeat split; auto.
    - apply Injective_classification.
      intros u v H3 H4 H5.
      rewrite H0 in H3, H4.
      rewrite ? H2 in H5; auto.
      apply Ordered_pair_iff in H5 as [H5 H6].
      rewrite H5 in H6.
      unfold oschf in H6.
      destruct excluded_middle_informative;
        try (contradict n; now apply H, function_maps_domain_to_range).
      destruct constructive_indefinite_description as [h].
      repeat destruct a.
      destruct b.
      rewrite Injective_classification in H7.
      apply H7 in H6; auto.
      + rewrite e0.
        unfold inverse_image_of_element.
        destruct excluded_middle_informative.
        * now apply Specify_classification.
        * contradict n.
          now apply function_maps_domain_to_range.
      + rewrite e0.
        unfold inverse_image_of_element.
        destruct excluded_middle_informative.
        * now apply Specify_classification.
        * contradict n.
          now apply function_maps_domain_to_range.
    - rewrite Surjective_classification.
      intros y H3.
      rewrite H1 in H3.
      apply Product_classification in H3 as [a [b [H3 [H4 H5]]]].
      subst.
      pose proof oschf_domain (inverse_image_of_element f a) (H a H3).
      pose proof oschf_range (inverse_image_of_element f a) (H a H3).
      pose proof oschf_bijective (inverse_image_of_element f a) (H a H3).
      pose proof H7 as [H8 H9].
      rewrite Surjective_classification in H9.
      destruct (H9 b) as [z [H10 H11]]; try congruence.
      exists z.
      assert (f z = a).
      { rewrite H5 in H10.
        unfold inverse_image_of_element in H10.
        destruct excluded_middle_informative; try tauto.
        apply Specify_classification in H10.
        tauto. }
      assert (z ∈ domain g).
      { rewrite H5 in H10.
        unfold inverse_image_of_element in H10.
        destruct excluded_middle_informative; try tauto.
        apply Specify_classification in H10 as [H10 H13].
        congruence. }
      split; auto.
      rewrite H2; congruence.
  Qed.

End orbit_stabilizer_cardinality_helper.

Section permutation_succ_helper_function.

  Variable n : N.

  Definition permutation_succ_helper : set → set.
  Proof.
    intros x.
    destruct (excluded_middle_informative (x ∈ (bijection_set (S n) (S n)))).
    - apply Specify_classification in i as [H H0].
      destruct (constructive_indefinite_description _ H0) as [f [H1 [H2 [H3 H4]]]].
      exact (f n).
    - exact ∅.
  Defined.
      
End permutation_succ_helper_function.

Theorem Graph_classification :
  ∀ f z, z ∈ graph f ↔ ∃ a, a ∈ domain f ∧ z = (a, f a).
Proof.
  split; intros H.
  - pose proof (func_hyp f) as [H0 H1].
    apply H0 in H as H2.
    apply Product_classification in H2 as [a [b [H2 [H3 H4]]]].
    exists a.
    split; auto; subst.
    pose proof
         Function_classification (graph f) (domain f) (range f) _ H2 (func_hyp f)
      as [[H5 H6] H7].
    apply H1 in H2 as [z [[H4 H8] H9]].
    assert (z = b) by now apply H9.
    assert (z = (f a)) by now apply H9.
    congruence.
  - destruct H as [a [H H0]].
    subst.
    pose proof
         Function_classification (graph f) (domain f) (range f) _ H (func_hyp f)
      as [[H0 H1] H2].
    exact H1.
Qed.

Theorem function_graph_uniqueness : ∀ f x a b, x ∈ domain f → 
    (x, a) ∈ graph f → (x, b) ∈ graph f → a = b.
Proof.
  intros f x a b H H0 H1.
  pose proof (func_hyp f) as [H2 H3].
  apply H2 in H0 as H6.
  apply Product_classification in H6 as [x' [a' [H6 [H7 H8]]]].
  apply Ordered_pair_iff in H8 as [H8 H9].
  subst.
  apply H2 in H1 as H4.
  apply Product_classification in H4 as [x [a [H4 [H5 H8]]]].
  apply Ordered_pair_iff in H8 as [H8 H9].
  subst.
  apply H3 in H4 as [y [[H4 H8] H9]].
  assert (y = a) by now apply H9.
  assert (y = a') by now apply H9.
  congruence.
Qed.

Theorem permutation_succ :
  (∀ n : N, (bijection_set (S n) (S n)) ~ (S n) × (bijection_set n n))%set.
Proof.
  intros n.
  destruct (function_construction
              (bijection_set (S n) (S n)) (S n)
              (permutation_succ_helper n)) as [psh [H [H0 H1]]].
  { intros a H.
    unfold permutation_succ_helper.
    destruct excluded_middle_informative; try tauto.
    destruct Specify_classification, a0, constructive_indefinite_description.
    repeat destruct a1.
    rewrite <-e1.
    apply function_maps_domain_to_range.
    rewrite e0, <-S_is_succ.
    apply Pairwise_union_classification.
    right.
    now apply Singleton_classification. }             
  rewrite <-H, <-H0.
  apply orbit_stabilizer_cardinality.
  intros y H2.
  unfold inverse_image_of_element.
  destruct excluded_middle_informative; try tauto.
  rewrite H0 in H2.
  assert ((S n \ {n,n}) = n) as L0.
  { apply Extensionality.
    split; intros H3.
    - apply Complement_classification in H3 as [H3 H4].
      rewrite <-S_is_succ in H3.
      rewrite Singleton_classification in H4.
      apply Pairwise_union_classification in H3 as [H3 | H3]; auto.
      now apply Singleton_classification in H3.
    - apply Complement_classification.
      split.
      + rewrite <-S_is_succ.
        apply Pairwise_union_classification; tauto.
      + intros H4.
        apply Singleton_classification in H4.
        subst.
        now apply (no_quines n). }
  assert ((S n \ {y,y}) ~ (S n \ {n,n}))%set as L1.
  { apply equivalence_minus_element; auto using cardinality_refl.
    apply lt_is_in, naturals.succ_lt. }
  rewrite <-L0 at 2.
  rewrite <-L1.
  set (X := {x in domain psh | psh x = y}).
  set (Y := bijection_set n (S n \ {y,y})).
  set (G := {z in X × Y |
              proj2 X Y z = {t in proj1 X Y z | proj1 (S n) (S n) t ≠ n}}).
  assert (∀ x, x ∈ X → {z in x | proj1 (S n) (S n) z ≠ n} ∈ Y) as Z.
  { intros x H3.
    apply Specify_classification.
    pose proof H3 as H4.
    apply Specify_classification in H4 as [H4 H5].
    rewrite H in H4.
    apply Specify_classification in H4 as [H4 [f [H6 [H7 [H8 H9]]]]].
    split.
    - apply Powerset_classification.
      intros z H10.
      apply Specify_classification in H10 as [H10 H11].
      apply Powerset_classification in H4.
      apply H4 in H10 as H12.
      apply Product_classification in H12 as [a [b [H12 [H13 H14]]]].
      subst.
      rewrite H1.
      2: { apply Specify_classification in H3 as [H3].
           congruence. }
      apply Product_classification.
      exists a, b.
      repeat split; auto.
      + rewrite <-S_is_succ in H12.
        apply Pairwise_union_classification in H12 as [H12 | H12]; auto.
        apply Singleton_classification in H12.
        subst.
        contradict H11.
        rewrite proj1_eval; auto.
        apply lt_is_in, naturals.succ_lt.
      + apply Complement_classification.
        split; auto.
        rewrite Singleton_classification.
        intros H14.
        unfold permutation_succ_helper in H14.
        destruct excluded_middle_informative.
        2: { contradict n0.
             apply Specify_classification in H3 as [H3].
           congruence. }
        destruct Specify_classification, a0,
        constructive_indefinite_description as [f'].
        repeat destruct a1.
        subst.
        rewrite proj1_eval in H11; auto.
        contradict H11.
        rewrite <-e2 in H10.
        apply Graph_classification in H10 as [a' [H5 H10]].
        apply Ordered_pair_iff in H10 as [H10 H11].
        destruct b0 as [H14 H15].
        rewrite Injective_classification in H14.
        apply H14 in H11; try congruence.
        rewrite e0, <-lt_is_in.
        apply naturals.succ_lt.
    - rewrite H1 in H5.
      2: { apply Specify_classification in H3 as [H3].
           congruence. }
      unfold permutation_succ_helper in H5.
      destruct excluded_middle_informative.
      2: { contradict n0.
           apply Specify_classification in H3 as [H3].
           congruence. }
      destruct Specify_classification, a, constructive_indefinite_description as [f'].
      repeat destruct a0.
      assert (f = f').
      { apply function_record_injective; congruence. }        
      destruct (function_construction n (S n \ {y,y}) (λ x, f' x)) as [f'' [H11 [H12 H13]]].
      { intros a0 H11. 
        apply Complement_classification.
        split.
        - rewrite <-e1.
          apply function_maps_domain_to_range.
          rewrite e0, <-S_is_succ.
          apply Pairwise_union_classification; auto.
        - rewrite Singleton_classification.
          intros H12.
          subst.
          destruct b as [H13 H14].
          rewrite Injective_classification in H13.
          apply H13 in H12.
          + subst.
            contradiction (no_quines n).
          + rewrite e0, <-S_is_succ.
            apply Pairwise_union_classification; auto.
          + rewrite e0, <-lt_is_in. 
            apply naturals.succ_lt. }
      exists f''.
      repeat split; auto.
      { apply Extensionality.
        split; intros H14.
        - apply Specify_classification.
          split.
          + rewrite <-e2.
            apply Graph_classification in H14 as [z1 [H14 H15]].
            apply Graph_classification.
            exists z1.
            split.
            { rewrite e0, <-S_is_succ.
              apply Pairwise_union_classification.
              left.
              congruence. }
            subst.
            apply Ordered_pair_iff.
            split; auto.
            rewrite H13; congruence.
          + intros H15.
            apply Graph_classification in H14 as [z1 [H14 H16]].
            subst.
            rewrite proj1_eval in H15.
            * rewrite H15, H11 in H14.
              contradiction (no_quines n).
            * rewrite <-S_is_succ.
              apply Pairwise_union_classification; left; congruence.
            * assert (f'' z1 ∈ range f'').
              { now apply function_maps_domain_to_range. }
              rewrite H12, Complement_classification in H5; tauto.
        - apply Specify_classification in H14 as [H14 H15].
          rewrite <-e2 in H14.
          apply Graph_classification in H14 as [z1 [H14 H16]].
          subst.
          rewrite proj1_eval in H15.
          + apply Graph_classification.
            exists z1.
            split.
            * rewrite H6, <-S_is_succ in H14.
              apply Pairwise_union_classification in H14 as [H14 | H14]; try congruence.
              now apply Singleton_classification in H14.
            * rewrite H13; auto.
              rewrite H6, <-S_is_succ in H14.
              apply Pairwise_union_classification in H14 as [H14 | H14]; try congruence.
              now apply Singleton_classification in H14.
          + congruence.
          + rewrite <-e1.
            now apply function_maps_domain_to_range. }
      { rewrite Injective_classification.
        intros x0 y0 H14 H15 H16.
        rewrite ? H13 in H16; try congruence.
        destruct b as [H17 H18].
        rewrite Injective_classification in H17.
        apply H17 in H16; auto.
        - rewrite e0, <-S_is_succ.
          apply Pairwise_union_classification.
          left; congruence.
        - rewrite e0, <-S_is_succ.
          apply Pairwise_union_classification.
          left; congruence. }
      { rewrite Surjective_classification.
        intros z H14.
        assert (z ∈ range f').
        { rewrite H12 in H14.
          apply Complement_classification in H14.
          rewrite <-e1 in H14.
          tauto. }
        destruct b as [H16 H17].
        rewrite Surjective_classification in H17.
        apply H17 in H15 as [u [H15 H18]].
        exists u.
        split.
        - rewrite e0, <-S_is_succ in H15.
          apply Pairwise_union_classification in H15 as [H15 | H15].
          + congruence.
          + apply Singleton_classification in H15.
            subst.
            rewrite H12 in H14.
            apply Complement_classification in H14.
            rewrite Singleton_classification in H14.
            tauto.
        - rewrite H13; auto.
          rewrite e0, <-S_is_succ in H15.
          apply Pairwise_union_classification in H15 as [H15 | H15].
          + congruence.
          + apply Singleton_classification in H15.
            subst.
            rewrite H12 in H14.
            apply Complement_classification in H14.
            rewrite Singleton_classification in H14.
            tauto. } }
  assert (is_function G X Y).
  { split.
    { intros z H3.
      apply Specify_classification in H3.
      tauto. }
    intros x H3.
    apply Z in H3 as H4.
    exists {z in x | proj1 (S n) (S n) z ≠ n}.
    repeat split; auto.
    - apply Specify_classification.
      split.
      + apply Product_classification.
        exists x, {z in x | proj1 (S n) (S n) z ≠ n}.
        repeat split; auto.
      + rewrite proj1_eval, proj2_eval; auto.
    - intros x' [H5 H6].
      apply Specify_classification in H6 as [H6 H7].
      rewrite proj1_eval, proj2_eval in H7; auto. }
  set (g := mkFunc _ _ _ H3).
  exists g.
  simpl in *.
  assert (∀ f x, x ∈ bijection_set (S n) (S n) →
                 domain f = S n → range f = S n → graph f = x →
                 psh x = y → f n = y) as Z0.
  { intros f x H4 H5 H6 H7 H8.
    rewrite H1 in H8; auto.
    unfold permutation_succ_helper in H8.
    destruct excluded_middle_informative; try tauto.
    destruct Specify_classification, a, constructive_indefinite_description.
    repeat destruct a0.
    replace f with x0; try congruence.
    apply function_record_injective; congruence. }
  assert (∀ x, x ∈ X → g x = {z in x | proj1 (S n) (S n) z ≠ n}) as Z1.
  { intros x H13.
    assert ((x, g x) ∈ graph g) as H14.
    { apply Graph_classification.
      exists x.
      auto. }
    simpl in H14.
    apply (function_graph_uniqueness g x); auto.
    simpl.
    apply Specify_classification.
    split.
    - apply Product_classification.
      exists x, {z in x | proj1 (S n) (S n) z ≠ n}.
      split; auto.
    - rewrite proj1_eval, proj2_eval; auto. }
  repeat split; auto.
  - rewrite Injective_classification.
    intros a b H4 H5 H6.
    pose proof Function_classification G (domain g) (range g) a H4 H3
      as [[H7 H8] H9].
    pose proof Function_classification G (domain g) (range g) b H5 H3
      as [[H10 H11] H12].
    simpl in *.
    replace (eval_rel G X Y a) with (g a) in * by auto.
    replace (eval_rel G X Y b) with (g b) in * by auto.
    apply Extensionality.
    rewrite ? Z1 in H6; auto.
    pose proof H4 as H15.
    apply Specify_classification in H15 as [H15 H16].
    rewrite H in H15.
    apply Specify_classification in H15 as [H15 [f_a [H17 [H18 [H19 H20]]]]].
    apply (Z0 f_a) in H16; auto.
    2: { apply Specify_classification in H4.
         rewrite <-H; tauto. }
    pose proof H5 as H21.
    apply Specify_classification in H21 as [H21 H22].
    rewrite H in H21.
    apply Specify_classification in H21 as [H21 [f_b [H23 [H24 [H25 H26]]]]].
    apply (Z0 f_b) in H22; auto.
    2: { apply Specify_classification in H5.
         rewrite <-H; tauto. }
    rewrite <-H19, <-H25 in *.
    intros z.
    assert (n ⊂ S n) as Z2.
    { rewrite <-naturals.le_is_subset.
      exists 1%N.
      now rewrite add_1_r. }
    destruct (classic ((proj1 (S n) (S n) z) = n)).
    { split; intros H14.
      - apply Graph_classification in H14 as [z1 [H14 H27]].
        rewrite H27 in *.
        apply Graph_classification.
        exists z1.
        rewrite proj1_eval in H13; try congruence.
        2: { rewrite <-H18.
             now apply function_maps_domain_to_range. }
        split; try congruence.
      - apply Graph_classification in H14 as [z1 [H14 H27]].
        rewrite H27 in *.
        apply Graph_classification.
        exists z1.
        rewrite proj1_eval in H13; try congruence.
        2: { rewrite <-H24.
             now apply function_maps_domain_to_range. }
        split; try congruence. }
    split; intros H14.
    assert (z ∈ {z in graph f_a | proj1 (S n) (S n) z ≠ n}).
    { apply Specify_classification; auto. }
    rewrite H6 in H27.
    apply Specify_classification in H27.
    tauto.
    assert (z ∈ {z in graph f_b | proj1 (S n) (S n) z ≠ n}).
    { apply Specify_classification; auto. }
    rewrite <-H6 in H27.
    apply Specify_classification in H27.
    tauto.
  - rewrite Surjective_classification.
    simpl.
    intros z H4.
    apply Specify_classification in H4 as [H4 [f [H5 [H6 [H7 H8]]]]].
    destruct
      (function_construction
         (S n) (S n)
         (λ x, if (excluded_middle_informative (x = n)) then y else f x))
      as [f' [H9 [H10 H11]]].
    { intros a H9.
      destruct excluded_middle_informative; auto.
      assert (f a ∈ range f).
      { apply function_maps_domain_to_range.
        rewrite H5.
        rewrite <-S_is_succ in H9.
        apply Pairwise_union_classification in H9 as [H9 | H9]; auto.
        now apply Singleton_classification in H9. }
      rewrite H6 in H10.
      apply Complement_classification in H10; tauto. }
    exists (z ∪ {(n,y),(n,y)}).
    assert ((z ∪ {(n,y),(n,y)}) ∈ bijection_set (S n) (S n)) as Z2.
    { apply Specify_classification.
        split.
        { apply Powerset_classification.
          intros x H12.
          apply Pairwise_union_classification in H12 as [H12 | H12].
          - apply Powerset_classification in H4.
            apply H4 in H12.
            apply Product_classification in H12 as [a [b [H12 [H13 H14]]]].
            subst.
            apply Product_classification.
            exists a, b.
            repeat split; auto.
            + rewrite <-S_is_succ.
              apply Pairwise_union_classification; tauto.
            + apply Complement_classification in H13; tauto.
          - apply Singleton_classification in H12.
            subst.
            apply Product_classification.
            exists n, y.
            repeat split; auto.
            apply lt_is_in, naturals.succ_lt. }
        exists f'.
        repeat split; auto.
        { apply Extensionality.
          split; intros H12.
          - apply Graph_classification in H12 as [z1 [H12 H13]].
            subst.
            apply Pairwise_union_classification.
            destruct (classic (z1 = n)).
            + right.
              rewrite H11.
              2: { subst.
                   apply lt_is_in, naturals.succ_lt. }
              destruct excluded_middle_informative; try tauto.
              subst.
              now apply Singleton_classification.
            + left.
              apply Graph_classification.
              exists z1.
              split.
              { rewrite H9, <-S_is_succ in H12.
                apply Pairwise_union_classification in H12 as [H12 | H12].
                - congruence.
                - now apply Singleton_classification in H12. }
              rewrite H11; try congruence.
              destruct excluded_middle_informative; intuition.
          - apply Pairwise_union_classification in H12 as [H12 | H12].
            + rewrite <-H7 in H12.
              apply Graph_classification in H12 as [z1 [H12 H13]].
              subst.
              apply Graph_classification.
              exists z1.
              split.
              * rewrite H9, <-S_is_succ.
                apply Pairwise_union_classification.
                left.
                congruence.
              * rewrite H11.
                2: { rewrite <-S_is_succ.
                     apply Pairwise_union_classification.
                     left.
                     congruence. }
                destruct excluded_middle_informative; auto.
                rewrite e, H5 in H12.
                contradiction (no_quines n).
            + apply Singleton_classification in H12.
              subst.
              apply Graph_classification.
              exists n.
              split.
              * rewrite H9.
                apply lt_is_in, naturals.succ_lt.
              * rewrite H11.
                2: { apply lt_is_in, naturals.succ_lt. }
                destruct excluded_middle_informative; tauto. }
        { rewrite Injective_classification.
          intros u v H12 H13 H14.
          rewrite ? H11 in H14; try congruence.
          repeat destruct excluded_middle_informative; try congruence.
          - assert (f v ∈ range f).
            { apply function_maps_domain_to_range.
              rewrite H9, <-S_is_succ in H13.
              apply Pairwise_union_classification in H13 as [H13 | H13].
              - congruence.
              - now apply Singleton_classification in H13. }
            rewrite H6 in H15.
            rewrite Complement_classification, Singleton_classification in H15.
            subst; tauto.
          - assert (f u ∈ range f).
            { apply function_maps_domain_to_range.
              rewrite H9, <-S_is_succ in H12.
              apply Pairwise_union_classification in H12 as [H12 | H12].
              - congruence.
              - now apply Singleton_classification in H12. }
            rewrite H6 in H15.
            rewrite Complement_classification, Singleton_classification in H15.
            subst; tauto.
          - destruct H8 as [H8 H15].
            rewrite Injective_classification in H8.
            apply H8 in H14; auto.
            + rewrite H9, <-S_is_succ in H12.
              apply Pairwise_union_classification in H12 as [H12 | H12].
              * congruence.
              * now apply Singleton_classification in H12.
            + rewrite H9, <-S_is_succ in H13.
              apply Pairwise_union_classification in H13 as [H13 | H13].
              * congruence.
              * now apply Singleton_classification in H13. }
        { rewrite Surjective_classification.
          intros v H12.
          destruct (classic (v = y)).
          - exists n.
            split.
            + rewrite H9, <-lt_is_in.
              apply naturals.succ_lt.
            + rewrite H11.
              destruct excluded_middle_informative; auto; try tauto.
              apply lt_is_in, naturals.succ_lt.
          - assert (v ∈ range f).
            { rewrite H6.
              apply Complement_classification.
              split; try congruence.
              now rewrite Singleton_classification. }
            destruct H8 as [H8 H15].
            rewrite Surjective_classification in H15.
            apply H15 in H14 as [x [H14 H16]].
            exists x.
            split.
            + rewrite H9, <-S_is_succ.
              apply Pairwise_union_classification.
              left; congruence.
            + rewrite H11.
              2: { rewrite <-S_is_succ.
                   apply Pairwise_union_classification.
                   left; congruence. }
              destruct excluded_middle_informative; auto.
              rewrite e, H5 in H14.
              contradiction (no_quines n). } }
    assert (z ∪ {(n,y),(n,y)} ∈ X).
    { apply Specify_classification.
      split; try congruence.
      rewrite H1; auto.
      unfold permutation_succ_helper.
      destruct excluded_middle_informative; try tauto.
      destruct Specify_classification, a, constructive_indefinite_description.
      repeat destruct a0.
      apply (function_graph_uniqueness x n).
      - rewrite e0, <-lt_is_in.
        apply naturals.succ_lt.
      - apply Graph_classification.
        exists n.
        split; auto.
        rewrite e0, <-lt_is_in.
        apply naturals.succ_lt.
      - rewrite e2.
        apply Pairwise_union_classification.
        right.
        now apply Singleton_classification. }
    split; auto.
    rewrite Z1; auto.
    apply Extensionality.
    split; intros H13.
    + apply Specify_classification in H13 as [H13 H14].
      apply Pairwise_union_classification in H13 as [H13 | H13]; auto.
      apply Singleton_classification in H13.
      subst.
      rewrite proj1_eval in H14; try tauto.
      apply lt_is_in, naturals.succ_lt.
    + apply Specify_classification.
      split.
      * apply Pairwise_union_classification; tauto.
      * rewrite <-H7 in H13.
        apply Graph_classification in H13 as [z1 [H13 H14]].
        subst.
        rewrite proj1_eval.
        -- intros H14.
           subst.
           rewrite H5 in H13.
           contradiction (no_quines n).
        -- rewrite <-S_is_succ.
           apply Pairwise_union_classification.
           left; congruence.
        -- assert (f z1 ∈ range f) by now apply function_maps_domain_to_range.
           rewrite H6, Complement_classification in H7; tauto.
Qed.

Theorem bijection_empty_is_singleton : bijection_set 0%N 0%N = {∅, ∅}.
Proof.
  apply Extensionality.
  split; intros.
  - apply Singleton_classification.
    apply Specify_classification in H as [H H0].
    rewrite Empty_product_left in H.
    apply Powerset_classification in H.
    apply Extensionality.
    split; intros.
    + now apply H in H1.
    + contradiction (Empty_set_classification z0).
  - apply Singleton_classification in H.
    subst.
    apply Specify_classification.
    split.
    + rewrite Empty_product_left.
      apply Empty_set_in_powerset.
    + exists empty_function.
      unfold empty_function.
      destruct constructive_indefinite_description.
      repeat split; intuition.
      * apply Extensionality.
        split; intros H3.
        -- apply Graph_classification in H3 as [a [H3 H4]].
           rewrite H in H3.
           contradiction (Empty_set_classification a).
        -- contradiction (Empty_set_classification z).
      * apply Injective_classification.
        intros x0 y H0 H3 H4.
        rewrite H in *.
        contradiction (Empty_set_classification y).
      * apply Surjective_classification.
        intros y H0.
        rewrite H1 in *.
        contradiction (Empty_set_classification y).
Qed.

Theorem bijections_of_empty_set : (bijection_set 0%N 0%N ~ 1%N)%set.
Proof.
  rewrite bijection_empty_is_singleton.
  apply singleton_card_1.
Qed.

Theorem bijections_of_one : (bijection_set 1%N 1%N = {{(∅,∅),(∅,∅)},{(∅,∅),(∅,∅)}}).
Proof.
  simpl.
  unfold succ.
  rewrite Union_comm, Union_empty.
  apply Extensionality.
  split; intros H; rewrite Singleton_classification in *.
  - apply Specify_classification in H as [H [f [H0 [H1 [H2 H3]]]]].
    subst.
    apply Extensionality.
    split; intros H2; rewrite Singleton_classification in *.
    + apply Graph_classification in H2 as [a [H2 H4]].
      rewrite H0 in H2.
      rewrite Singleton_classification in H2.
      subst.
      apply Ordered_pair_iff.
      split; auto.
      assert (f ∅ ∈ range f).
      { apply function_maps_domain_to_range.
        rewrite H0.
        now apply Singleton_classification. }
      rewrite H1 in H2.
      now apply Singleton_classification in H2.
    + apply Graph_classification.
      exists ∅.
      split.
      * now rewrite H0, Singleton_classification.
      * subst.
        apply Ordered_pair_iff.
        split; auto.
        assert (f ∅ ∈ range f).
        { apply function_maps_domain_to_range.
          rewrite H0.
          now apply Singleton_classification. }
        rewrite H1 in H2.
        now apply Singleton_classification in H2.
  - subst.
    apply Specify_classification.
    split.
    + apply Powerset_classification.
      intros z H.
      apply Singleton_classification in H.
      subst.
      apply Product_classification.
      exists ∅, ∅.
      now rewrite Singleton_classification.
    + destruct (function_construction {∅,∅} {∅,∅} (λ x, x)) as [f]; try tauto.
      exists f.
      destruct H as [H [H0 H1]].
      repeat split; auto.
      { apply Extensionality.
        split; intros H2.
        - apply Graph_classification in H2 as [a [H2 H3]].
          subst.
          rewrite Singleton_classification, Ordered_pair_iff.
          split.
          + rewrite H in H2.
            now rewrite Singleton_classification in H2.
          + rewrite H in H2.
            apply Singleton_classification in H2.
            subst.
            assert (f ∅ ∈ range f).
            { apply function_maps_domain_to_range.
              rewrite H.
              now apply Singleton_classification. }
            rewrite H0 in H2.
            now apply Singleton_classification in H2.
        - apply Graph_classification.
          exists ∅.
          split.
          * now rewrite H, Singleton_classification.
          * rewrite Singleton_classification in H2.
            subst.
            apply Ordered_pair_iff.
            split; auto.
            assert (f ∅ ∈ range f).
            { apply function_maps_domain_to_range.
              rewrite H.
              now apply Singleton_classification. }
            rewrite H0 in H2.
            now apply Singleton_classification in H2. }
      { rewrite Injective_classification.
        intros x y H2 H3 H4.
        rewrite H, Singleton_classification in *.
        congruence. }
      { rewrite Surjective_classification.
        intros y H2.
        exists ∅.
        split.
        - now rewrite H, Singleton_classification.
        - rewrite H0, Singleton_classification in H2.
          subst.
          assert (f ∅ ∈ range f).
          { apply function_maps_domain_to_range.
            rewrite H.
            now apply Singleton_classification. }
          rewrite H0 in H2.
          now apply Singleton_classification in H2. }
Qed.

Theorem permutations_are_finite : ∀ n : N, finite (bijection_set n n).
Proof.
  intros n.
  induction n using Induction.
  { exists 1%N.
    apply bijections_of_empty_set. }
  unfold finite in *.
  destruct IHn as [m H].
  exists ((S n) * m)%N.
  symmetry.
  now rewrite permutation_succ, H, <-(card_of_natural (S n)),
  <-(card_of_natural m), <-natural_prod_card, card_equiv at 1;
    auto using finite_products_are_finite, naturals_are_finite.
Qed.

Theorem size_of_bijections_of_empty_set : size_of_bijections 0%N 0%N = 1%N.
Proof.
  unfold size_of_bijections, finite_cardinality.
  destruct excluded_middle_informative.
  - destruct constructive_definite_description.
    apply natural_cardinality_uniqueness.
    rewrite <-e.
    apply bijections_of_empty_set.
  - contradict n.
    apply permutations_are_finite.
Qed.

Theorem size_of_bijections_of_one : size_of_bijections 1%N 1%N = 1%N.
Proof.
  unfold size_of_bijections, finite_cardinality.
  destruct excluded_middle_informative.
  - destruct constructive_definite_description.
    apply natural_cardinality_uniqueness.
    rewrite <-e, bijections_of_one.
    apply singleton_card_1.
  - contradict n.
    apply permutations_are_finite.
Qed.

Theorem number_of_permutations : ∀ n, factorial n = permutations n.
Proof.
  intros n.
  induction n using Induction.
  { unfold factorial, prod, iterate_with_bounds.
    destruct excluded_middle_informative.
    - exfalso.
      rewrite naturals.le_not_gt in l.
      contradict l.
      apply naturals.lt_succ.
    - unfold permutations.
      now rewrite size_of_bijections_of_empty_set. }
  destruct (classic (n = 0%N)).
  { subst.
    unfold factorial, prod.
    rewrite iterate_0.
    unfold permutations.
    now rewrite size_of_bijections_of_one. }
  unfold factorial, prod in *.
  rewrite iterate_succ, IHn.
  simpl.
  unfold permutations, size_of_bijections.
  rewrite permutation_succ, finite_products_card, card_of_natural,
  mul_comm, INZ_mul; auto using naturals_are_finite, permutations_are_finite.
  rewrite naturals.le_not_gt.
  contradict H.
  now apply lt_1_eq_0 in H.
Qed.
