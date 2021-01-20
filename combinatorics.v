Require Export cardinality integers.

Definition permutations (n : N) := size_of_bijections n n.

Definition factorial (n : N) := (prod integers (λ x, x : Z) 1 n) : Z.

Section orbit_stabilizer_cardinality_theorem.

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
          now apply Specify_classification.
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
      apply H7 in H6; auto; rewrite e0; unfold inverse_image_of_element;
          now apply Specify_classification.
    - rewrite Surjective_classification.
      intros y H3.
      rewrite H1 in H3.
      apply Product_classification in H3 as [a [b [H3 [H4 H5]]]].
      subst.
      pose proof oschf_bijective (inverse_image_of_element f a) (H a H3)
        as [H5 H6].
      rewrite Surjective_classification in H6.
      destruct (H6 b) as [z [H7 H8]].
      { rewrite oschf_range; auto. }
      rewrite oschf_domain in H7.
      + apply Specify_classification in H7.
        exists z.
        split; intuition; try congruence.
        rewrite H2; congruence.
      + now rewrite H.
  Qed.

End orbit_stabilizer_cardinality_theorem.

Section permutation_succ_helper_functions.

  Variable n : N.
  Variable y : elts (S n).

  Section functionify_construction.
    Variable A B : set.
    Definition functionify : elts (bijection_set A B) → function.
    Proof.
      intros [f F].
      apply Specify_classification in F as [F F0].
      destruct (constructive_indefinite_description _ F0) as [f'].
      exact f'.
    Defined.

    Theorem functionify_domain : ∀ f, domain (functionify f) = A.
    Proof.
      intros [f F].
      unfold functionify.
      destruct Specify_classification, a, constructive_indefinite_description.
      tauto.
    Qed.

    Theorem functionify_range : ∀ f, range (functionify f) = B.
    Proof.
      intros [f F].
      unfold functionify.
      destruct Specify_classification, a, constructive_indefinite_description.
      tauto.
    Qed.

    Theorem functionify_graph : ∀ f, graph (functionify f) = proj1_sig f.
    Proof.
      intros [f F].
      unfold functionify.
      destruct Specify_classification, a, constructive_indefinite_description.
      tauto.
    Qed.

    Theorem functionify_bijective : ∀ f, bijective (functionify f).
    Proof.
      intros [f F].
      unfold functionify.
      destruct Specify_classification, a, constructive_indefinite_description.
      tauto.
    Qed.

  End functionify_construction.

  Definition permutation_succ_helper : set → set.
  Proof.
    intros x.
    destruct (excluded_middle_informative (x ∈ (bijection_set (S n) (S n)))).
    - apply Specify_classification in i as [H H0].
      destruct (constructive_indefinite_description _ H0)
        as [f [H1 [H2 [H3 H4]]]].
      exact (f n).
    - exact ∅.
  Defined.

  Lemma permutation_succ_proj_lemma : ∀ a,
      a ∈ bijection_set (S n) (S n) → permutation_succ_helper a ∈ S n.
  Proof.
    intros a H.
    unfold permutation_succ_helper.
    destruct excluded_middle_informative; try tauto.
    destruct Specify_classification, a0, constructive_indefinite_description.
    repeat destruct a1.
    rewrite <-e1.
    apply function_maps_domain_to_range.
    rewrite e0, <-lt_is_in.
    apply naturals.succ_lt.
  Qed.

  Definition permutation_succ_proj : function.
  Proof.
    destruct (constructive_indefinite_description
                _ (function_construction
                     (bijection_set (S n) (S n)) (S n)
                     permutation_succ_helper permutation_succ_proj_lemma))
      as [f].
    exact f.
  Defined.

  Theorem psp_domain : domain permutation_succ_proj = bijection_set (S n) (S n).
  Proof.
    unfold permutation_succ_proj.
    destruct constructive_indefinite_description.
    tauto.
  Qed.

  Theorem psp_range : range permutation_succ_proj = S n.
  Proof.
    unfold permutation_succ_proj.
    destruct constructive_indefinite_description.
    tauto.
  Qed.

  Definition n_in_Sn : elts (S n).
  Proof.
    pose proof naturals.succ_lt n.
    rewrite lt_is_in in H.
    exact (exist _ _ H).
  Defined.

  Theorem psp_action :
    ∀ x :  elts (bijection_set (S n) (S n)),
      permutation_succ_proj (proj1_sig x) = ((functionify (S n) (S n) x) n).
  Proof.
    intros x.
    unfold permutation_succ_proj.
    destruct constructive_indefinite_description as [f].
    destruct a as [H [H0 H1]].
    rewrite H1; try apply (proj2_sig x).
    unfold permutation_succ_helper.
    destruct excluded_middle_informative.
    - destruct Specify_classification, a, constructive_indefinite_description
        as [f'].
      repeat destruct a0.
      unfold functionify.
      destruct x.
      destruct Specify_classification, a0, constructive_indefinite_description
        as [f''].
      destruct a1 as [H2 [H3 [H4 H5]]].
      simpl in *.
      replace f' with f''; auto.
      apply function_record_injective; congruence.
    - contradict n0.
      apply (proj2_sig x).
  Qed.

  Definition inverse_image_incl :
    elts (inverse_image_of_element permutation_succ_proj (proj1_sig y)) →
    elts (bijection_set (S n) (S n)).
  Proof.
    intros [f F].
    unfold inverse_image_of_element in F.
    apply Specify_classification in F as [F F0].
    rewrite psp_domain in F.
    exact (exist _ _ F).
  Defined.

  Lemma inverse_image_incl_value :
    ∀ f, proj1_sig (inverse_image_incl f) = proj1_sig f.
  Proof.
    intros f.
    unfold inverse_image_incl, inverse_image_of_element in *.
    now destruct f, Specify_classification, a.
  Qed.

  Lemma inverse_image_classification:
    ∀ f : elts (inverse_image_of_element permutation_succ_proj (proj1_sig y)),
      ((functionify (S n) (S n) (inverse_image_incl f)) n) = proj1_sig y.
  Proof.
    intros f.
    unfold functionify, inverse_image_incl, inverse_image_of_element in *.
    destruct f.
    destruct Specify_classification, a, Specify_classification, a0,
    constructive_indefinite_description as [f'].
    destruct a1 as [H [H0 [H1 H2]]].
    apply Specify_classification in i0 as [H3 H4]; auto.
    clear i a i1 i2 a0 i3 e0.
    rewrite psp_domain in H3.
    set (ξ := (exist (λ x, x ∈ bijection_set (S n) (S n)) _ H3)).
    replace x with (proj1_sig ξ) in * by auto.
    rewrite <-e, psp_action.
    replace f' with (functionify (S n) (S n) ξ); auto.
    apply function_record_injective.
    - rewrite functionify_domain; congruence.
    - rewrite functionify_range; congruence.
    - rewrite functionify_graph; congruence.
  Qed.

  Theorem permutation_succ_left_helper_lemma :
    ∀ f (x : elts n), ((functionify (S n) (S n) (inverse_image_incl f))
                         (proj1_sig x) ∈ (S n \ {proj1_sig y, proj1_sig y})).
  Proof.
    intros f x.
    apply Complement_classification.
    split.
    - rewrite <-(functionify_range (S n) (S n) (inverse_image_incl f)).
      apply function_maps_domain_to_range.
      rewrite functionify_domain, <-S_is_succ.
      apply Pairwise_union_classification.
      left.
      apply (proj2_sig x).
    - rewrite Singleton_classification, <-(inverse_image_classification f).
      intros H.
      pose proof (functionify_bijective _ _ (inverse_image_incl f)) as [H0 H1].
      rewrite Injective_classification in H0.
      apply H0 in H.
      + contradiction (no_quines n).
        rewrite <-H at 1.
        apply (proj2_sig x).
      + rewrite functionify_domain, <-S_is_succ.
        apply Pairwise_union_classification.
        left.
        apply (proj2_sig x).
      + rewrite functionify_domain, <-lt_is_in.
        apply naturals.succ_lt.
  Qed.

  Definition permutation_succ_left_helper :
    elts (inverse_image_of_element permutation_succ_proj (proj1_sig y)) →
    elts n → elts (S n \ {proj1_sig y, proj1_sig y}).
  Proof.
    intros f x.
    exact (exist _ _ (permutation_succ_left_helper_lemma f x)).
  Defined.
 
  Theorem pslh_action : ∀ f x,
      proj1_sig (permutation_succ_left_helper f x) =
      (functionify _ _ (inverse_image_incl f)) (proj1_sig x).
  Proof.
    intros f x.
    unfold permutation_succ_left_helper.
    now simpl.
  Qed.

  Theorem psl_bijective :
    ∀ f, bijective (sets.functionify _ _ (permutation_succ_left_helper f)).
  Proof.
    intros f.
    split.
    - rewrite Injective_classification.
      intros x1 x2 H H0 H1.
      unfold sets.functionify in *.
      destruct constructive_indefinite_description as [f'].
      destruct a as [H2 [H3 H4]].
      rewrite H2 in H, H0.
      set (ξ1 := (exist _ _ H : elts n)).
      set (ξ2 := (exist _ _ H0 : elts n)).
      replace x1 with (proj1_sig ξ1) in * by auto.
      replace x2 with (proj1_sig ξ2) in * by auto.
      rewrite ? H4, ? pslh_action in H1.
      pose proof functionify_bijective _ _ (inverse_image_incl f) as [H5 H6].
      rewrite Injective_classification in H5.
      apply H5; auto; rewrite functionify_domain, <-S_is_succ;
        apply Pairwise_union_classification; left.
      + apply (proj2_sig ξ1).
      + apply (proj2_sig ξ2).
    - apply Surjective_classification.
      intros z H.
      unfold sets.functionify in *.
      destruct constructive_indefinite_description as [f'].
      destruct a as [H0 [H1 H2]].
      rewrite H1 in H.
      apply Complement_classification in H as [H H3].
      rewrite Singleton_classification in H3.
      pose proof functionify_bijective _ _ (inverse_image_incl f) as [H4 H5].
      rewrite Surjective_classification, functionify_range,
      functionify_domain in H5.
      pose proof H as H6.
      apply H5 in H6 as [x [H6 H7]].
      exists x.
      assert (x ∈ n).
      { rewrite <-S_is_succ in H6.
        apply Pairwise_union_classification in H6 as [H6 | H6]; auto.
        apply Singleton_classification in H6; subst.
        now rewrite inverse_image_classification in H3. }
      split; try congruence.
      set (ξ := (exist _ _ H8 : elts n)).
      replace x with (proj1_sig ξ) by auto.
      now rewrite H2, pslh_action.
  Qed.

  Theorem permutation_succ_left_construction : ∀ f,
      graph (sets.functionify _ _ (permutation_succ_left_helper f))
            ∈ bijection_set n (S n \ {proj1_sig y, proj1_sig y}).
  Proof.
    intros f.
    unfold bijection_set.
    apply Specify_classification.
    split.
    - apply Powerset_classification.
      intros z H.
      apply Graph_classification in H as [z1 [H H0]].
      unfold sets.functionify in *.
      destruct constructive_indefinite_description as [f'].
      destruct a as [H2 [H3 H4]].
      subst.
      apply Product_classification.
      exists z1, (f' z1).
      repeat split; try congruence.
      rewrite <-H3.
      now apply function_maps_domain_to_range.
    - exists (sets.functionify _ _ (permutation_succ_left_helper f)).
      pose proof psl_bijective f.
      unfold sets.functionify in *.
      destruct constructive_indefinite_description.
      tauto.
  Qed.

  Definition permutation_succ_left :
    elts (inverse_image_of_element permutation_succ_proj (proj1_sig y)) →
    elts (bijection_set n (S n \ {proj1_sig y, proj1_sig y})).
  Proof.
    intros f.
    exact (exist _ _ (permutation_succ_left_construction f)).
  Defined.

  Definition permutation_succ_right_helper :
    elts (bijection_set n (S n \ {proj1_sig y, proj1_sig y})) →
    elts (S n) → elts (S n).
  Proof.
    intros f x.
    destruct (excluded_middle_informative (proj1_sig x = n)).
    - exact y.
    - assert ((functionify _ _ f) (proj1_sig x) ∈
                                  S n \ {proj1_sig y, proj1_sig y}).
      { rewrite <-(functionify_range _ _ f).
        apply function_maps_domain_to_range.
        rewrite functionify_domain.
        pose proof (proj2_sig x) as H.
        simpl in *.
        rewrite <-S_is_succ in H.
        apply Pairwise_union_classification in H as [H | H]; auto.
        now apply Singleton_classification in H. }
      apply Complement_classification in H as [H H0].
      exact (exist _ _ H).
  Defined.

  Theorem psrh_n : ∀ f, permutation_succ_right_helper f n_in_Sn = y.
  Proof.
    intros f.
    unfold permutation_succ_right_helper.
    destruct excluded_middle_informative; auto.
    contradict n0.
    now simpl.
  Qed.

  Theorem psrh_bijective :
    ∀ f, bijective (sets.functionify _ _ (permutation_succ_right_helper f)).
  Proof.
    intros f.
    unfold sets.functionify.
    destruct constructive_indefinite_description as [f'].
    destruct a as [H [H0 H1]].
    split.
    - rewrite Injective_classification.
      intros x1 x2 H2 H3 H4.
      rewrite H in H2, H3.
      set (ξ1 := exist _ _ H2 : elts (S n)).
      set (ξ2 := exist _ _ H3 : elts (S n)).
      replace x1 with (proj1_sig ξ1) in * by auto.
      replace x2 with (proj1_sig ξ2) in * by auto.
      rewrite ? H1 in H4.
      unfold permutation_succ_right_helper in H4.
      repeat destruct excluded_middle_informative; simpl in *; try congruence;
        try (destruct Complement_classification, a;
             simpl in *; contradict n1; now rewrite Singleton_classification).
      repeat destruct Complement_classification.
      destruct a, a0.
      simpl in *.
      pose proof (functionify_bijective _ _ f) as [H5 H6].
      rewrite Injective_classification in H5.
      clear ξ1 ξ2.
      apply H5; auto; rewrite functionify_domain.
      + rewrite <-S_is_succ in H2.
        apply Pairwise_union_classification in H2 as [H2 | H2]; auto.
        now rewrite Singleton_classification in H2.
      + rewrite <-S_is_succ in H3.
        apply Pairwise_union_classification in H3 as [H3 | H3]; auto.
        now rewrite Singleton_classification in H3.
    - rewrite Surjective_classification.
      intros z H2.
      rewrite H0 in H2.
      set (ζ := exist _ _ H2 : elts (S n)).
      replace z with (proj1_sig ζ) in * by auto.
      destruct (classic (ζ = y)).
      + exists n.
        split.
        * rewrite H, <-S_is_succ.
          apply Pairwise_union_classification.
          rewrite Singleton_classification; tauto.
        * replace (INS n) with (proj1_sig n_in_Sn) by auto.
          rewrite H1, psrh_n.
          congruence.
      + pose proof (functionify_bijective _ _ f) as [H4 H5].
        rewrite Surjective_classification, functionify_range,
        functionify_domain in H5.
        assert (z ∈ S n \ {proj1_sig y, proj1_sig y}).
        { rewrite Complement_classification, Singleton_classification.
          split; auto.
          contradict H3.
          now apply set_proj_injective. }
        apply H5 in H6 as [x [H6 H7]].
        exists x.
        split.
        * rewrite H, <-S_is_succ.
          apply Pairwise_union_classification; tauto.
        * assert (x ∈ S n).
          { rewrite <-S_is_succ.
            apply Pairwise_union_classification; tauto. }
          set (ξ := exist _ _ H8 : elts (S n)).
          replace x with (proj1_sig ξ) in * by auto.
          rewrite H1.
          unfold permutation_succ_right_helper.
          destruct excluded_middle_informative.
          -- rewrite e in H6.
             contradiction (no_quines n).
          -- destruct Complement_classification, a.
             now simpl in *.
  Qed.

  Lemma permutation_succ_right_construction : ∀ f,
      graph (sets.functionify _ _ (permutation_succ_right_helper f)) ∈
            (inverse_image_of_element permutation_succ_proj (proj1_sig y)).
  Proof.
    intros.
    unfold inverse_image_of_element.
    apply Specify_classification.
    assert
        (graph (sets.functionify (S n) (S n) (permutation_succ_right_helper f))
               ∈ bijection_set (S n) (S n)) as H.
    { apply Specify_classification.
      split.
      - apply Powerset_classification.
        intros z H.
        apply Graph_classification in H as [z1 [H H0]].
        subst.
        unfold sets.functionify in *.
        destruct constructive_indefinite_description as [f'].
        apply Product_classification.
        destruct a as [H0 [H1 H2]].
        exists z1, (f' z1).
        repeat split; try congruence.
        rewrite <-H1.
        apply function_maps_domain_to_range.
        congruence.
      - pose proof psrh_bijective f.
        exists (sets.functionify (S n) (S n) (permutation_succ_right_helper f)).
        unfold sets.functionify in *.
        destruct constructive_indefinite_description.
        tauto. }
    split.
    - unfold permutation_succ_proj.
      destruct constructive_indefinite_description.
      destruct a as [H0 [H1 H2]].
      rewrite H0; auto.
    - set (γ := exist _ _ H : elts (bijection_set (S n) (S n))).
      replace
        (graph (sets.functionify (S n) (S n) (permutation_succ_right_helper f)))
        with (proj1_sig γ) in * by auto.
      rewrite psp_action.
      unfold functionify, γ.
      destruct Specify_classification, a, constructive_indefinite_description
        as [f'].
      clear a e i0 γ.
      destruct a0 as [H0 [H1 [H2 H3]]].
      replace f' with
          (sets.functionify (S n) (S n) (permutation_succ_right_helper f)) in *.
      2: { apply function_record_injective; try congruence;
           unfold sets.functionify;
           destruct constructive_indefinite_description;
           destruct a as [H4 [H5 H6]]; congruence. }
      unfold sets.functionify.
      destruct constructive_indefinite_description as [f''].
      destruct a as [H4 [H5 H6]].
      replace (INS n) with (proj1_sig n_in_Sn) by auto.
      now rewrite H6, psrh_n.
  Qed.

  Definition permutation_succ_right :
    elts (bijection_set n (S n \ {proj1_sig y, proj1_sig y})) →
    elts (inverse_image_of_element permutation_succ_proj (proj1_sig y)).
  Proof.
    intros f.
    exact (exist _ _ (permutation_succ_right_construction f)).
  Defined.
 
End permutation_succ_helper_functions.

Theorem permutation_succ :
  (∀ n : N, (bijection_set (S n) (S n)) ~ (S n) × (bijection_set n n))%set.
Proof.
  intros n.
  rewrite <-psp_domain, <-psp_range.
  apply orbit_stabilizer_cardinality.
  intros y H.
  rewrite psp_range in H.
  replace (INS n) with (S n \ {n,n}) at 2.
  2: { apply Extensionality.
       split; intros H0.
       - apply Complement_classification in H0 as [H0 H1].
         rewrite <-S_is_succ in H0.
         rewrite Singleton_classification in H1.
         apply Pairwise_union_classification in H0 as [H0 | H0]; auto.
         now apply Singleton_classification in H0.
       - apply Complement_classification.
         split.
         + rewrite <-S_is_succ.
           apply Pairwise_union_classification; tauto.
         + intros H1.
           apply Singleton_classification in H1.
           subst.
           now apply (no_quines n). }
  setoid_replace (S n \ {n,n}) with (S n \ {y,y}).
  2: { apply equivalence_minus_element; auto using cardinality_refl.
       apply lt_is_in, naturals.succ_lt. }
  apply two_sided_inverse_bijective.
  set (γ := exist _ _ H : elts (S n)).
  replace y with (proj1_sig γ) in * by auto.
  exists (permutation_succ_left _ γ), (permutation_succ_right _ γ).
  split.
  - intros a.
    pose proof (proj2_sig a) as H0; simpl in H0.
    apply set_proj_injective, (function_graph_equality (S n) (S n)); simpl in *.
    { pose proof func_hyp (sets.functionify
                             _ _ (permutation_succ_right_helper
                                    _ _ (permutation_succ_left _ γ a))).
      now rewrite sets.functionify_domain, sets.functionify_range in *. }
    { pose proof proj2_sig a.
      simpl in *.
      apply Inverse_image_subset in H0.
      - rewrite psp_domain in H0.
        apply Specify_classification in H0 as [H0 [f H2]].
        replace (proj1_sig a) with (graph f) by intuition.
        pose proof func_hyp f.
        intuition; congruence.
      - now rewrite psp_range. }
    unfold sets.functionify.
    destruct constructive_indefinite_description as [f].
    destruct a0 as [H1 [H2 H3]].
    intros z H4.
    apply Graph_classification in H4 as [z1 [H4 H5]].
    subst.
    rewrite H1 in H4.
    set (ζ1 := exist _ _ H4 : elts (S n)).
    replace z1 with (proj1_sig ζ1) in * by auto.
    rewrite H3.
    unfold permutation_succ_right_helper; simpl.
    destruct excluded_middle_informative.
    * subst.
      apply Inverse_image_classification in H0 as H5.
      2: { apply Specify_classification in H0; tauto. }
      2: { now rewrite psp_range. }
      unfold inverse_image_of_element in H0.
      apply Specify_classification in H0 as [H0 H6].
      rewrite psp_domain in H0.
      set (α := exist _ _ H0 : elts (bijection_set (S n) (S n))).
      replace (proj1_sig a) with (proj1_sig α) in * by auto.
      rewrite psp_action in H5.
      simpl.
      pose proof H0 as H7.
      apply Specify_classification in H7 as [H7 [f' [H8 [H9 [H10 H11]]]]].
      rewrite <-H10.
      replace f' with (functionify (S n) (S n) α).
      -- apply Graph_classification.
         exists n.
         split; try congruence.
         rewrite functionify_domain, <-lt_is_in.
         apply naturals.succ_lt.
      -- apply function_record_injective.
         ++ now rewrite functionify_domain.
         ++ now rewrite functionify_range.
         ++ now rewrite H10, functionify_graph.
    * destruct Complement_classification, a0, Specify_classification,
      a1, constructive_indefinite_description as [f'].
      simpl.
      clear n1 i0 i a0 e i2 i1 a1.
      destruct a2 as [H5 [H6 [H7 H8]]].
      assert ((z1, f' z1) ∈ graph f').
      { apply Graph_classification.
        exists z1.
        split; auto.
        clear ζ1.
        rewrite <-S_is_succ in H4.
        apply Pairwise_union_classification in H4 as [H4 | H4]; try congruence.
        now apply Singleton_classification in H4. }
      rewrite H7 in H9.
      apply Graph_classification in H9 as [z1' [H9 H10]].
      apply Ordered_pair_iff in H10 as [H10 H11].
      subst.
      rewrite H11.
      unfold sets.functionify in *.
      destruct constructive_indefinite_description as [f''].
      destruct a0 as [H10 [H12 H13]].
      rewrite H10 in H9.
      set (ζ1' := exist _ _ H9 : elts n).
      replace z1' with (proj1_sig ζ1') in * by auto.
      rewrite H13.
      simpl.
      clear H11 H8 H7 H13 H12 H10 f'' H6 H5 f' ζ1 H3 H2 H1 f.
      rewrite Inverse_image_classification in H0.
      2: { rewrite psp_domain.
           pose proof (proj2_sig (inverse_image_incl n (exist _ _ H) a)).
           simpl in *.
           now rewrite inverse_image_incl_value in H1. }
      2: { now rewrite psp_range. }
      replace (proj1_sig a) with
          (proj1_sig (inverse_image_incl n (exist _ _ H) a)) in *.
      2: { now rewrite inverse_image_incl_value. }
      rewrite psp_action in H0.
      unfold functionify in H0.
      destruct inverse_image_incl, Specify_classification, a0,
      constructive_indefinite_description as [f].
      clear a0 i0 i1 e.
      simpl.
      destruct Specify_classification, a0,
      constructive_indefinite_description, a2 as [H1 [H2 [H3 H5]]].
      rewrite <-H3.
      apply Graph_classification.
      exists z1'.
      split; auto.
      rewrite H1, <-S_is_succ.
      apply Pairwise_union_classification; tauto.
  - intros b.
    pose proof (proj2_sig b) as H0; simpl in H0.
    apply set_proj_injective; simpl.
    apply (function_graph_equality n (S n \ {y,y})); auto.
    { pose proof (func_hyp (sets.functionify
                              _ _ (permutation_succ_left_helper
                                     _ _ (permutation_succ_right n γ b)))).
      now rewrite sets.functionify_domain, sets.functionify_range in *. }
    { apply Specify_classification in H0 as [H0 [f H2]].
      replace (proj1_sig b) with (graph f) by intuition.
      pose proof func_hyp f.
      intuition; congruence. }
    intros z H3.
    unfold sets.functionify in H3.
    destruct constructive_indefinite_description as [f].
    destruct a as [H4 [H5 H6]].
    apply Graph_classification in H3 as [z1 [H3 H7]].
    subst.
    rewrite H4 in H3.
    set (ζ := exist _ _ H3 : elts n).
    replace z1 with (proj1_sig ζ) in * by auto.
    rewrite H6.
    apply Specify_classification in H0 as [H0 [f' [H7 [H8 [H9 H10]]]]].
    rewrite <-H9.
    apply Graph_classification.
    exists (proj1_sig ζ).
    split; try (simpl; congruence).
    rewrite (pslh_action n γ).
    apply Ordered_pair_iff.
    split; auto.
    clear f H4 H5 H6.
    unfold functionify, inverse_image_incl, permutation_succ_right.
    destruct Specify_classification, a, Specify_classification, a0,
    constructive_indefinite_description.
    clear e0 i2 i1 a0 e i0 i a.
    destruct a1 as [H1 [H2 [H4 H5]]].
    replace x with (sets.functionify _ _ (permutation_succ_right_helper n γ b)).
    2: { apply function_record_injective.
         - rewrite sets.functionify_domain; congruence.
         - rewrite sets.functionify_range; congruence.
         - congruence. }
    clear x H1 H2 H4 H5.
    unfold sets.functionify.
    destruct constructive_indefinite_description.
    destruct a as [H1 [H2 H4]].
    assert (z1 ∈ S n).
    { rewrite <-S_is_succ.
      apply Pairwise_union_classification.
      now left. }
    set (ζ' := exist _ _ H5 : elts (S n)).
    replace (proj1_sig ζ) with (proj1_sig ζ') by auto.
    rewrite H4.
    clear x H1 H2 H4.
    unfold permutation_succ_right_helper.
    destruct excluded_middle_informative.
    { simpl in e.
      subst.
      contradiction (no_quines n). }
    destruct Complement_classification, a.
    simpl.
    clear n0 a i i0 n1 ζ' ζ.
    replace f' with (functionify n (S n \ {y,y}) b); auto.
    apply function_record_injective.
    + now rewrite functionify_domain.
    + now rewrite functionify_range.
    + now rewrite functionify_graph.
Qed.

Theorem bijection_empty_is_singleton : bijection_set 0%N 0%N = {∅, ∅}.
Proof.
  apply Extensionality.
  split; intros.
  - apply Singleton_classification.
    apply Specify_classification in H as [H H0].
    rewrite Empty_product_left, Powerset_classification in H.
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

Theorem bijections_of_one :
  (bijection_set 1%N 1%N = {{(∅,∅),(∅,∅)},{(∅,∅),(∅,∅)}}).
Proof.
  simpl.
  unfold succ.
  rewrite Union_comm, Union_empty.
  apply Extensionality.
  split; intros H; rewrite Singleton_classification in *; subst.
  - apply Specify_classification in H as [H [f [H0 [H1 [H2 H3]]]]];
      subst; auto using singleton_functions.
  - apply Specify_classification.
    split.
    + rewrite Powerset_classification, singleton_products.
      apply Set_is_subset.
    + destruct (function_construction {∅,∅} {∅,∅} (λ x, x)) as [f]; try tauto.
      exists f.
      repeat split; intuition; try congruence; auto using singleton_functions.
      * rewrite Injective_classification.
        intros x y H1 H3 H4.
        now rewrite ? H0, ? H, ? Singleton_classification, ? H1, ? H3 in *.
      * rewrite Surjective_classification.
        intros y H1.
        exists ∅.
        split; try now rewrite H0, Singleton_classification.
        rewrite H, Singleton_classification in *.
        subst.
        apply function_maps_domain_to_graph;
          now rewrite ? (singleton_functions f ∅ ∅),
          ? H0, ? H, ? Singleton_classification.
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
  destruct (classic (n = 0%N)) as [H | H].
  { subst.
    unfold factorial, prod.
    rewrite iterate_0.
    unfold permutations.
    now rewrite size_of_bijections_of_one. }
  unfold factorial, prod in *.
  rewrite iterate_succ, IHn.
  - simpl.
    unfold permutations, size_of_bijections.
    rewrite permutation_succ, finite_products_card, card_of_natural,
    mul_comm, INZ_mul; auto using naturals_are_finite, permutations_are_finite.
  - rewrite naturals.le_not_gt.
    contradict H.
    now apply lt_1_eq_0 in H.
Qed.
