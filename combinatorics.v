Require Export cardinality rationals.

Definition permutations (n : N) := size_of_bijections n n.

Definition factorial (n : N) := (prod integers (λ x, x : Z) 1 n) : Z.

Notation "n !" := (factorial n) (at level 35, format "n '!'") : Z_scope.

Definition set_of_combinations (n k : N) := {x in P n | # x = k}.

Definition binomial n k := # set_of_combinations n k.

(* The goal is to prove that the number of permutations of n is n!,
   and that (binomial n k) = n!/(k! (n-k)!). *)

Open Scope set_scope.

Section orbit_stabilizer_cardinality_theorem.

  Variable f : function.
  Variable x : set.
  Hypothesis H : ∀ y, y ∈ range f → inverse_image_of_element f y ~ x.

  Definition oschf : set → function.
  Proof.
    intros z.
    destruct (excluded_middle_informative (z ~ x)).
    - destruct (constructive_indefinite_description _ e) as [g [H1 [H2 H3]]].
      exact g.
    - exact empty_function.
  Defined.

  Theorem oschf_domain : ∀ z, z ~ x → domain (oschf z) = z.
  Proof.
    intros z H0.
    unfold oschf.
    destruct excluded_middle_informative; try tauto.
    destruct constructive_indefinite_description.
    now repeat destruct a.
  Qed.

  Theorem oschf_range : ∀ z, z ~ x → range (oschf z) = x.
  Proof.
    intros z H0.
    unfold oschf.
    destruct excluded_middle_informative; try tauto.
    destruct constructive_indefinite_description.
    now repeat destruct a.
  Qed.

  Theorem oschf_bijective : ∀ z, z ~ x → bijective (oschf z).
  Proof.
    intros z H0.
    unfold oschf.
    destruct excluded_middle_informative; try tauto.
    destruct constructive_indefinite_description.
    now repeat destruct a.
  Qed.

  Theorem orbit_stabilizer_cardinality : domain f ~ range f × x.
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

  Lemma permutation_succ_proj_construction : ∀ a,
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
                     permutation_succ_helper
                     permutation_succ_proj_construction))
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
      f_equal.
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
    f_equal.
    apply function_record_injective;
      now rewrite ? functionify_domain, ? functionify_range,
      ? functionify_graph; congruence.
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
        * replace (n : set) with (proj1_sig n_in_Sn) by auto.
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
      apply function_record_injective in H2.
      + subst.
        unfold sets.functionify.
        destruct constructive_indefinite_description as [f''].
        destruct a as [H4 [H5 H6]].
        replace (n : set) with (proj1_sig n_in_Sn) by auto.
        now rewrite H6, psrh_n.
      + now rewrite sets.functionify_domain.
      + now rewrite sets.functionify_range.
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
  ∀ n : N, bijection_set (S n) (S n) ~ (S n) × (bijection_set n n).
Proof.
  intros n.
  rewrite <-psp_domain, <-psp_range.
  apply orbit_stabilizer_cardinality.
  intros y H.
  rewrite psp_range in H.
  replace (n : set) with (S n \ {n,n}) at 2.
  2: { rewrite <-S_is_succ.
       apply complement_disjoint_union, disjoint_succ. }
  setoid_replace (S n \ {n,n}) with (S n \ {y,y}).
  2: { apply equivalence_minus_element; auto using cardinality_refl;
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
      assert (graph f' = proj1_sig α) as H12 by now rewrite H10.
      rewrite <-(functionify_graph (S n) (S n) α) in H12.
      apply function_record_injective in H12.
      -- rewrite <-H10, H12.
         apply Graph_classification.
         exists n.
         split; congruence.
      -- now rewrite functionify_domain.
      -- now rewrite functionify_range.
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
    apply function_record_injective in H4;
      rewrite ? sets.functionify_domain, ? sets.functionify_range; auto.
    subst.
    unfold sets.functionify.
    destruct constructive_indefinite_description.
    destruct a as [H4 [H6 H11]].
    assert (z1 ∈ S n) as H12.
    { rewrite <-S_is_succ.
      apply Pairwise_union_classification; tauto. }
    set (ζ' := exist _ _ H12 : elts (S n)).
    replace (proj1_sig ζ) with (proj1_sig ζ') by auto.
    rewrite H11.
    unfold permutation_succ_right_helper.
    destruct excluded_middle_informative.
    { simpl in e.
      subst.
      contradiction (no_quines n). }
    destruct Complement_classification, a.
    simpl.
    f_equal.
    apply function_record_injective;
      now rewrite ? functionify_domain, ? functionify_range,
      ? functionify_graph.
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
    split; rewrite ? Empty_product_left; auto using Empty_set_in_powerset.
    exists empty_function.
    unfold empty_function.
    destruct constructive_indefinite_description; repeat split; intuition;
      rewrite ? Injective_classification, ? Surjective_classification; intros.
    + apply NNPP.
      contradict H.
      apply Nonempty_classification in H as [z H].
      apply Graph_classification in H as [t [H H0]].
      apply Nonempty_classification; eauto.
    + contradiction (Empty_set_classification y).
      congruence.
    + contradiction (Empty_set_classification y).
      congruence.
Qed.

Theorem bijections_of_empty_set : bijection_set 0%N 0%N ~ 1%N.
Proof.
  rewrite bijection_empty_is_singleton.
  apply singleton_card_1.
Qed.

Theorem bijections_of_one : bijection_set 1%N 1%N ~ 1%N.
Proof.
  unfold naturals.one.
  rewrite permutation_succ, bijections_of_empty_set.
  simpl.
  unfold succ.
  now rewrite Union_comm, Union_empty, singleton_products, ? singleton_card_1.
Qed.

Theorem permutations_are_finite : ∀ n : N, finite (bijection_set n n).
Proof.
  intros n.
  induction n as [| n [m H]] using Induction.
  { exists 1%N.
    apply bijections_of_empty_set. }
  exists ((S n) * m)%N.
  symmetry.
  now rewrite permutation_succ, H, <-(card_of_natural (S n)),
  <-(card_of_natural m), <-natural_prod_card, card_equiv at 1;
    auto using finite_products_are_finite, naturals_are_finite.
Qed.

Theorem size_of_bijections_of_empty_set : size_of_bijections 0%N 0%N = 1%N.
Proof.
  apply natural_cardinality_uniqueness.
  rewrite <-bijections_of_empty_set.
  eauto using card_equiv, permutations_are_finite.
Qed.

Theorem size_of_bijections_of_one : size_of_bijections 1%N 1%N = 1%N.
Proof.
  unfold size_of_bijections.
  now rewrite bijections_of_one, card_of_natural.
Qed.

Theorem number_of_permutations_n : ∀ n, n! = permutations n.
Proof.
  intros n.
  induction n using Induction; unfold factorial in *.
  - unfold prod, iterate_with_bounds.
    destruct excluded_middle_informative.
    + exfalso.
      rewrite naturals.le_not_gt in l.
      contradict l.
      apply naturals.lt_succ.
    + unfold permutations.
      now rewrite size_of_bijections_of_empty_set.
  - rewrite prod_succ, IHn.
    + unfold permutations, size_of_bijections.
      rewrite permutation_succ, finite_products_card, card_of_natural, mul_comm,
      INZ_mul; auto using naturals_are_finite, permutations_are_finite.
    + exists n.
      now rewrite add_comm, add_1_r.
Qed.

Theorem number_of_permutations :
  ∀ S (n : N), S ~ n → n! = size_of_bijections S S.
Proof.
  intros S n H.
  now rewrite H, number_of_permutations_n.
Qed.

Section Combinations_orbit_stabilizer.

  Variable n k : N.
  Hypothesis nontriviality : k ⊂ n.

  Definition φ (f : elts (bijection_set n n)) :=
    {x in n | (functionify n n f x) ∈ k}.

  Definition combinations_proj_helper : set → set.
  Proof.
    intros f.
    destruct (excluded_middle_informative (f ∈ bijection_set n n)).
    - exact (φ (exist _ _ i)).
    - exact ∅.
  Defined.

  Theorem combinations_proj_construction : ∀ f,
      f ∈ bijection_set n n →
      combinations_proj_helper f ∈ set_of_combinations n k.
  Proof.
    intros f H.
    unfold combinations_proj_helper.
    destruct excluded_middle_informative; try tauto.
    set (η := exist _ _ i : elts (bijection_set n n)).
    replace f with (proj1_sig η) in * by auto.
    apply Specify_classification.
    split.
    - apply Powerset_classification.
      intros x H0.
      apply Specify_classification in H0.
      tauto.
    - apply equivalence_to_card.
      destruct (function_construction (φ η) k (λ x, functionify n n η x))
        as [h [H0 [H1 H2]]].
      { intros a H0.
        apply Specify_classification in H0.
        tauto. }
      exists h.
      pose proof functionify_bijective _ _ η as [H3 H4].
      repeat split; auto.
      + rewrite Injective_classification in *.
        intros x y H5 H6 H7.
        rewrite ? H2 in H7; try congruence.
        apply H3; rewrite ? functionify_domain, H0 in *; try congruence.
        * apply Specify_classification in H5; tauto.
        * apply Specify_classification in H6; tauto.
      + rewrite Surjective_classification in *.
        intros y H5.
        assert (y ∈ n) as H6 by (apply nontriviality; congruence).
        rewrite <-(functionify_range n n η) in H6.
        apply H4 in H6 as [x [H6 H7]].
        rewrite functionify_domain in H6.
        exists x.
        split.
        * rewrite H0.
          apply Specify_classification.
          split; auto.
          rewrite H7.
          congruence.
        * rewrite H2; try congruence.
          apply Specify_classification.
          split; auto.
          rewrite H7.
          congruence.
  Qed.

  Definition combinations_proj : function.
  Proof.
    destruct
      (constructive_indefinite_description
         _ (function_construction
              (bijection_set n n)
              (set_of_combinations n k)
              (λ x, combinations_proj_helper x) combinations_proj_construction))
      as [f].
    exact f.
  Defined.

  Theorem cp_domain : domain combinations_proj = bijection_set n n.
  Proof.
    unfold combinations_proj.
    destruct constructive_indefinite_description.
    tauto.
  Qed.

  Theorem cp_range : range combinations_proj = set_of_combinations n k.
  Proof.
    unfold combinations_proj.
    destruct constructive_indefinite_description.
    tauto.
  Qed.

  Theorem cp_action : ∀ f, combinations_proj (proj1_sig f) = φ f.
  Proof.
    intros [f F].
    unfold combinations_proj.
    destruct constructive_indefinite_description.
    destruct a as [H [H0 H1]].
    rewrite H1; auto.
    unfold combinations_proj_helper.
    destruct excluded_middle_informative; try tauto.
    simpl in *.
    now replace i with F by now apply proof_irrelevance.
  Qed.

  Theorem combinations_proj_surj : surjective combinations_proj.
  Proof.
    rewrite Surjective_classification.
    intros y H.
    rewrite cp_range in H.
    apply Specify_classification in H as [H H0].
    apply Powerset_classification in H.
    apply equivalence_to_bijection in H0 as [f [H0 [H1 [H2 H3]]]].
    2: { apply subsets_of_finites_are_finite in H;
           auto using naturals_are_finite. }
    assert (y ~ k) as H4 by now (exists f).
    assert (n \ y ~ n \ k) as H5.
    { assert (n ~ n) as H5 by easy.
      replace (n : set) with (k ∪ n \ k) in H5 at 1;
        replace (n : set) with (y ∪ n \ y) in H5 at 2;
        try now rewrite <-disjoint_union_complement, <-Union_subset.
      apply equinumerous_cardinality in H5.
      rewrite ? finite_union_cardinality in H5;
        eauto using naturals_are_finite, subsets_of_finites_are_finite,
        disjoint_intersection_complement, complement_subset.
      apply equinumerous_cardinality in H4.
      rewrite H4 in H5.
      apply naturals.cancellation_add in H5.
      now apply finite_cardinality_equinumerous in H5;
        eauto using naturals_are_finite, subsets_of_finites_are_finite,
        disjoint_intersection_complement, complement_subset. }
    pose proof H5 as [g [H6 [H7 [H8 H9]]]].
    destruct (function_construction
                n n (λ x, (if (excluded_middle_informative (x ∈ y)) then
                             (f x) else (g x)))) as [h [H10 [H11 H12]]].
    { intros a H10.
      destruct excluded_middle_informative.
      - apply nontriviality.
        rewrite <-H1.
        apply function_maps_domain_to_range.
        congruence.
      - assert (g a ∈ range g) as H11.
        { apply function_maps_domain_to_range.
          rewrite H6.
          now apply Specify_classification. }
        rewrite H7 in H11.
        apply Complement_classification in H11.
        tauto. }
    exists (graph h).
    assert (graph h ∈ domain combinations_proj).
    { rewrite cp_domain.
      apply Specify_classification.
      split.
      - apply Powerset_classification.
        intros z H13.
        apply Graph_classification in H13 as [z1 [H13 H14]].
        subst.
        apply Product_classification.
        exists z1, (h z1).
        repeat split; auto; try congruence.
        rewrite <-H11.
        now apply function_maps_domain_to_range.
      - exists h.
        repeat split; auto.
        + rewrite Injective_classification in *.
          intros x1 x2 H13 H14 H15.
          rewrite ? H12 in H15; try congruence.
          repeat destruct excluded_middle_informative.
          * apply H2; congruence.
          * assert (g x2 ∈ n \ k).
            { rewrite <-H7.
              apply function_maps_domain_to_range.
              rewrite H6.
              apply Complement_classification; split; congruence. }
            apply Complement_classification in H16 as [H16 H17].
            contradict H17.
            rewrite <-H15, <-H1.
            apply function_maps_domain_to_range.
            congruence.
          * assert (g x1 ∈ n \ k).
            { rewrite <-H7.
              apply function_maps_domain_to_range.
              rewrite H6.
              apply Complement_classification; split; congruence. }
            apply Complement_classification in H16 as [H16 H17].
            contradict H17.
            rewrite H15, <-H1.
            apply function_maps_domain_to_range.
            congruence.
          * apply H8; try congruence; rewrite H6;
              apply Complement_classification; split; congruence.
        + rewrite Surjective_classification in *.
          intros z H13.
          rewrite H11 in H13.
          destruct (excluded_middle_informative (z ∈ k)).
          * rewrite <-H1 in i.
            apply H3 in i as [x [H14 H15]].
            exists x.
            rewrite H0 in H14.
            apply H in H14 as H16.
            rewrite H12; auto.
            destruct excluded_middle_informative; split; congruence.
          * destruct (H9 z) as [x [H14 H15]].
            { rewrite H7.
              now apply Specify_classification. }
            exists x.
            rewrite H6 in H14.
            apply Complement_classification in H14 as [H14 H16].
            rewrite H12; auto.
            destruct excluded_middle_informative; split; congruence. }
    split; auto.
    rewrite cp_domain in H13.
    replace (graph h)
      with (proj1_sig (exist _ _ H13 : elts (bijection_set n n))) by auto.
    rewrite cp_action.
    apply Extensionality.
    split; intros H17.
    + apply Specify_classification in H17 as [H17 H18].
      unfold functionify in *.
      destruct Specify_classification, a,
      constructive_indefinite_description as [h' [H19 [H20 [H21 H22]]]].
      apply function_record_injective in H21; try congruence.
      subst.
      rewrite H12 in H18; auto.
      destruct excluded_middle_informative; try tauto.
      assert (g z ∈ n \ k) as H0.
      { rewrite <-H7.
        apply function_maps_domain_to_range.
        rewrite H6.
        now apply Complement_classification. }
      apply Complement_classification in H0.
      tauto.
    + apply Specify_classification.
      split; auto.
      unfold functionify.
      destruct Specify_classification, a, constructive_indefinite_description
        as [h' [H18 [H19 [H20 H21]]]].
      apply function_record_injective in H20; try congruence.
      subst.
      rewrite H12; auto.
      destruct excluded_middle_informative; try tauto.
      rewrite <-H1.
      now apply function_maps_domain_to_range.
  Qed.

  Variable y : elts (set_of_combinations n k).

  Definition
    h : elts (inverse_image_of_element combinations_proj (proj1_sig y)).
  Proof.
    pose proof (proj2_sig y) as H; simpl in *.
    pose proof combinations_proj_surj as H0.
    rewrite <-? cp_range, ? Surjective_classification in *.
    apply H0 in H.
    destruct (constructive_indefinite_description _ H) as [h].
    assert (h ∈ inverse_image_of_element combinations_proj (proj1_sig y)) by
        now apply Specify_classification.
    exact (exist _ _ H1).
  Defined.

  Theorem image_of_comb_proj : ∀ x (f : elts (bijection_set n n)),
      (combinations_proj (proj1_sig f) = proj1_sig y)
      → x ∈ n → x ∈ (proj1_sig y) ↔ (functionify n n f) x ∈ k.
  Proof.
    split; intros H1.
    - rewrite <-H, cp_action in H1.
      now apply Specify_classification in H1 as [H1 H5].
    - rewrite <-H, cp_action.
      apply Specify_classification.
      split; auto.
  Qed.

  Lemma combinations_left_helper_k_construction_1 :
    ∀ (f1 f2 : elts (bijection_set n n)) (x : elts k),
      combinations_proj (proj1_sig f1) = proj1_sig y →
      combinations_proj (proj1_sig f2) = proj1_sig y →
      (functionify n n f1) (inverse (functionify n n f2) (proj1_sig x)) ∈ k.
  Proof.
    intros f1 f2 x H H0.
    unfold inverse.
    destruct excluded_middle_informative.
    2: { contradict n0.
         apply functionify_bijective. }
    destruct b, constructive_indefinite_description as [f2_inv].
    destruct a as [H1 [H2 H3]].
    destruct f1 as [f1' H4].
    unfold functionify.
    destruct Specify_classification, a,
    constructive_indefinite_description as [f1''].
    destruct a0 as [H5 [H6 [H7 H8]]].
    assert (f2_inv (proj1_sig x) ∈ proj1_sig y) as H9.
    { rewrite image_of_comb_proj, H3; auto.
      - apply (proj2_sig x).
      - rewrite functionify_range.
        apply nontriviality, (proj2_sig x).
      - rewrite <-(functionify_domain _ _ f2), <-H2.
        apply function_maps_domain_to_range.
        rewrite H1, functionify_range.
        apply nontriviality, (proj2_sig x). }
    replace f1' with (proj1_sig (exist _ _ H4 : elts (bijection_set n n)))
      in * by auto.
    rewrite <-functionify_graph in H7.
    apply function_record_injective in H7; subst;
      rewrite ? functionify_domain, ? functionify_range; try congruence.
    apply image_of_comb_proj; auto.
    rewrite <-(functionify_domain _ _ f2), <-H2.
    apply function_maps_domain_to_range.
    rewrite H1, functionify_range.
    apply nontriviality, (proj2_sig x).
  Qed.

  Definition combinations_left_helper_k :
    elts (inverse_image_of_element combinations_proj (proj1_sig y)) →
    elts k → elts k.
  Proof.
    intros h0 x.
    pose proof (proj2_sig h) as H; simpl in *.
    pose proof (proj2_sig h0) as H0; simpl in *.
    apply Specify_classification in H as [H H1].
    rewrite cp_domain in H.
    apply Specify_classification in H0 as [H0 H2].
    rewrite cp_domain in H0.
    exact (exist _ _ (combinations_left_helper_k_construction_1
                        (exist _ _ H) (exist _ _ H0) x H1 H2)).
  Defined.

  Theorem image_of_comb_proj_2 : ∀ x (f : elts (bijection_set n n)),
      (combinations_proj (proj1_sig f) = proj1_sig y)
      → x ∈ n → x ∈ n \ (proj1_sig y) ↔ (functionify n n f) x ∈ n \ k.
  Proof.
    split; intros H1.
    - rewrite <-H, cp_action in H1.
      apply Complement_classification in H1 as [H1 H5].
      apply Complement_classification.
      split.
      + rewrite <-(functionify_range _ _ f).
        apply function_maps_domain_to_range.
        now rewrite functionify_domain.
      + contradict H5.
        now apply Specify_classification.
    - rewrite <-H, cp_action.
      unfold φ.
      rewrite Complement_classification, Specify_classification in *.
      split; auto; tauto.
  Qed.

  Lemma combinations_left_helper_k_construction_2 :
    ∀ (f1 f2 : elts (bijection_set n n)) (x : elts (n \ k)),
      combinations_proj (proj1_sig f1) = proj1_sig y →
      combinations_proj (proj1_sig f2) = proj1_sig y →
      (functionify n n f1)
        (inverse (functionify n n f2) (proj1_sig x)) ∈ (n \ k).
  Proof.
    intros f1 f2 x H H0.
    unfold inverse.
    destruct excluded_middle_informative.
    2: { contradict n0.
         apply functionify_bijective. }
    destruct b, constructive_indefinite_description as [f2_inv].
    destruct a as [H1 [H2 H3]].
    destruct f1 as [f1' H4].
    unfold functionify.
    destruct Specify_classification, a,
    constructive_indefinite_description as [f1''].
    destruct a0 as [H5 [H6 [H7 H8]]].
    assert (f2_inv (proj1_sig x) ∈ n \ proj1_sig y) as H9.
    { rewrite image_of_comb_proj_2, H3; auto.
      - apply (proj2_sig x).
      - rewrite functionify_range.
        apply (complement_subset k n), (proj2_sig x).
      - rewrite <-(functionify_domain _ _ f2), <-H2.
        apply function_maps_domain_to_range.
        rewrite H1, functionify_range.
        apply (complement_subset k n), (proj2_sig x). }
    replace f1' with (proj1_sig (exist _ _ H4 : elts (bijection_set n n)))
      in * by auto.
    rewrite <-functionify_graph in H7.
    apply function_record_injective in H7; subst;
      rewrite ? functionify_domain, ? functionify_range; try congruence.
    apply image_of_comb_proj_2; auto.
    rewrite <-(functionify_domain _ _ f2), <-H2.
    apply function_maps_domain_to_range.
    rewrite H1, functionify_range.
    apply (complement_subset k n), (proj2_sig x).
  Qed.

  Definition combinations_left_helper_n_minus_k :
    elts (inverse_image_of_element combinations_proj (proj1_sig y)) →
    elts (n \ k) → elts (n \ k).
  Proof.
    intros h0 x.
    pose proof (proj2_sig h) as H; simpl in *.
    pose proof (proj2_sig h0) as H0; simpl in *.
    apply Specify_classification in H as [H H1].
    rewrite cp_domain in H.
    apply Specify_classification in H0 as [H0 H2].
    rewrite cp_domain in H0.
    exact (exist _ _ (combinations_left_helper_k_construction_2
                        (exist _ _ H) (exist _ _ H0) x H1 H2)).
  Defined.

  Lemma combinations_left_helper_k_bijective : ∀ h',
      bijective (sets.functionify _ _ (combinations_left_helper_k h')).
  Proof.
    intros h'.
    unfold sets.functionify.
    destruct constructive_indefinite_description as [h'' [H [H0 H1]]].
    apply finite_set_injection_is_bijection.
    - rewrite H.
      apply naturals_are_finite.
    - now rewrite H, H0.
    - rewrite Injective_classification.
      intros x1 x2 H2 H3 H4.
      rewrite ? H, ? H0 in *.
      set (ξ1 := exist _ _ H2 : elts k).
      set (ξ2 := exist _ _ H3 : elts k).
      replace x1 with (proj1_sig ξ1) in * by auto.
      replace x2 with (proj1_sig ξ2) in * by auto.
      rewrite ? H1 in H4.
      unfold combinations_left_helper_k in H4.
      destruct Specify_classification, a, Specify_classification, a0.
      simpl in *.
      destruct Specify_classification, a1, constructive_indefinite_description,
      Specify_classification, a3, constructive_indefinite_description.
      clear e2 i6 i5 a3 e1 i4 i3 a1 i2 i1 a0 e0 e i0 i a.
      destruct a2 as [H5 [H6 [H7 [H8 H9]]]].
      destruct a4 as [H10 [H11 [H12 H13]]].
      apply inverse_bijective in H13 as H14.
      destruct H14 as [H14 H15].
      rewrite Injective_classification in *.
      apply H8 in H4; try apply H14 in H4; auto.
      + rewrite inverse_domain; auto.
        rewrite H11; auto.
      + rewrite inverse_domain; auto.
        rewrite H11; auto.
      + rewrite H5, <-H10, <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite inverse_domain; auto.
        rewrite H11; auto.
      + rewrite H5, <-H10, <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite inverse_domain; auto.
        rewrite H11; auto.
  Qed.

  Lemma combinations_left_helper_n_minus_k_bijective : ∀ h',
      bijective (sets.functionify _ _ (combinations_left_helper_n_minus_k h')).
  Proof.
    intros h'.
    unfold sets.functionify.
    destruct constructive_indefinite_description as [h'' [H [H0 H1]]].
    apply finite_set_injection_is_bijection.
    - rewrite H.
      eauto using subsets_of_finites_are_finite,
      naturals_are_finite, complement_subset.
    - now rewrite H, H0.
    - rewrite Injective_classification.
      intros x1 x2 H2 H3 H4.
      rewrite ? H, ? H0 in *.
      set (ξ1 := exist _ _ H2 : elts (n \ k)).
      set (ξ2 := exist _ _ H3 : elts (n \ k)).
      replace x1 with (proj1_sig ξ1) in * by auto.
      replace x2 with (proj1_sig ξ2) in * by auto.
      rewrite ? H1 in H4.
      unfold combinations_left_helper_n_minus_k in H4.
      destruct Specify_classification, a, Specify_classification, a0.
      simpl in *.
      destruct Specify_classification, a1, constructive_indefinite_description,
      Specify_classification, a3, constructive_indefinite_description.
      clear e2 i6 i5 a3 e1 i4 i3 a1 i2 i1 a0 e0 e i0 i a.
      destruct a2 as [H5 [H6 [H7 [H8 H9]]]].
      destruct a4 as [H10 [H11 [H12 H13]]].
      apply inverse_bijective in H13 as H14.
      destruct H14 as [H14 H15].
      rewrite Injective_classification in *.
      apply H8 in H4; try apply H14 in H4; auto.
      + rewrite inverse_domain; auto.
        rewrite H11; auto.
        eapply complement_subset; eauto.
      + rewrite inverse_domain; auto.
        rewrite H11; auto.
        eapply complement_subset; eauto.
      + rewrite H5, <-H10, <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite inverse_domain; auto.
        rewrite H11; auto.
        eapply complement_subset; eauto.
      + rewrite H5, <-H10, <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite inverse_domain; auto.
        rewrite H11; auto.
        eapply complement_subset; eauto.
  Qed.

  Theorem combinations_left_construction : ∀ h0,
      (graph (sets.functionify _ _ (combinations_left_helper_k h0)),
       graph (sets.functionify _ _ (combinations_left_helper_n_minus_k h0)))
        ∈ bijection_set k k × bijection_set (n \ k) (n \ k).
  Proof.
    intros h0.
    apply Product_classification.
    exists (graph (sets.functionify _ _ (combinations_left_helper_k h0))),
    (graph (sets.functionify _ _ (combinations_left_helper_n_minus_k h0))).
    repeat split; auto.
    - apply Specify_classification.
      split.
      + pose proof func_hyp
             (sets.functionify k k (combinations_left_helper_k h0)) as [H].
        now rewrite sets.functionify_domain, sets.functionify_range,
        <-Powerset_classification in H.
      + exists (sets.functionify k k (combinations_left_helper_k h0)).
        rewrite sets.functionify_domain, sets.functionify_range.
        auto using combinations_left_helper_k_bijective.
    - apply Specify_classification.
      split.
      + pose proof func_hyp
             (sets.functionify _ _ (combinations_left_helper_n_minus_k h0))
          as [H].
        now rewrite sets.functionify_domain, sets.functionify_range,
        <-Powerset_classification in H.
      + exists (sets.functionify _ _ (combinations_left_helper_n_minus_k h0)).
        rewrite sets.functionify_domain, sets.functionify_range.
        auto using combinations_left_helper_n_minus_k_bijective.
  Qed.

  Definition combinations_left :
    elts (inverse_image_of_element combinations_proj (proj1_sig y)) →
    elts (bijection_set k k × bijection_set (n \ k) (n \ k)).
  Proof.
    intros h0.
    exact (exist _ _ (combinations_left_construction h0)).
  Defined.

  Definition comb_inverse_image_incl :
    elts (inverse_image_of_element combinations_proj (proj1_sig y)) → function.
  Proof.
    intros [f F].
    apply Inverse_image_classification_left in F as H;
      apply Inverse_image_classification_domain in F as H0;
      try (rewrite cp_range; apply (proj2_sig y)).
    rewrite cp_domain in H0.
    exact (functionify n n (exist _ _ H0)).
  Defined.

  Theorem cii_domain : ∀ f, domain (comb_inverse_image_incl f) = n.
  Proof.
    intros [f F].
    simpl.
    destruct Specify_classification, a, constructive_indefinite_description.
    tauto.
  Qed.

  Theorem cii_range : ∀ f, range (comb_inverse_image_incl f) = n.
  Proof.
    intros [f F].
    simpl.
    destruct Specify_classification, a, constructive_indefinite_description.
    tauto.
  Qed.

  Theorem cii_graph : ∀ f, graph (comb_inverse_image_incl f) = proj1_sig f.
  Proof.
    intros [f F].
    simpl.
    destruct Specify_classification, a, constructive_indefinite_description.
    tauto.
  Qed.

  Theorem cii_bijection : ∀ f, graph (comb_inverse_image_incl f) ∈ bijection_set n n.
  Proof.
    intros [f F].
    pose proof F as H.
    apply Inverse_image_classification_domain in H.
    - rewrite cii_graph.
      simpl.
      now rewrite <-cp_domain.
    - rewrite cp_range.
      apply (proj2_sig y).
  Qed.

  Theorem cii_bijective : ∀ f, bijective (comb_inverse_image_incl f).
  Proof.
    intros f.
    pose proof cii_bijection f as H.
    apply Specify_classification in H as [H [f' [H0 [H1 [H2 H3]]]]].
    apply function_record_injective in H2;
      rewrite ? cii_domain, ? cii_range; congruence.
  Qed.

  Lemma combinations_right_helper_0 :
    ∀ x, x ∈ n → x ∈ proj1_sig y ↔ comb_inverse_image_incl h x ∈ k.
  Proof.
    pose proof proj2_sig h as H.
    apply Inverse_image_classification_left in H as H1;
      apply Inverse_image_classification_domain in H as H0;
      try (rewrite cp_range; apply (proj2_sig y)).
    rewrite cp_domain in H0.
    replace (proj1_sig h)
      with (proj1_sig (exist _ _ H0 : elts (bijection_set n n))) in H1 by auto.
    rewrite cp_action in H1.
    split; intros H6; destruct h; simpl in *.
    - destruct Specify_classification, a,
      constructive_indefinite_description as [h'].
      clear a i0 i1 e.
      destruct a0 as [H7 [H8 [H9 H10]]].
      rewrite <-H1 in H6.
      apply Specify_classification in H6 as [H6 H11].
      unfold functionify in H11.
      destruct Specify_classification, a, constructive_indefinite_description
        as [h''], a0 as [H12 [H13 [H14 H15]]].
      subst.
      apply function_record_injective in H9; congruence.
    - destruct Specify_classification, a,
      constructive_indefinite_description as [h'].
      clear a i0 i1 e.
      destruct a0 as [H7 [H8 [H9 H10]]].
      rewrite <-H1.
      apply Specify_classification.
      split; auto.
      unfold functionify.
      destruct Specify_classification, a, constructive_indefinite_description
        as [h''], a0 as [H11 [H12 [H13 H14]]].
      subst.
      apply function_record_injective in H13; congruence.
  Qed.

  Lemma combinations_right_helper_l_1 :
    ∀ x (z1 : elts (bijection_set k k)),
      x ∈ k →
      inverse (comb_inverse_image_incl h) (functionify k k z1 x) ∈ proj1_sig y.
  Proof.
    intros x z1 H.
    apply combinations_right_helper_0.
    { rewrite <-(cii_domain h), <-inverse_range; auto using cii_bijective.
      apply function_maps_domain_to_range.
      rewrite inverse_domain, cii_range; auto using cii_bijective.
      apply nontriviality.
      rewrite <-(functionify_range _ _ z1).
      apply function_maps_domain_to_range.
      now rewrite functionify_domain. }
    rewrite right_inverse; auto using cii_bijective.
    { rewrite <-(functionify_range _ _ z1).
      apply function_maps_domain_to_range.
      now rewrite functionify_domain. }
    rewrite inverse_domain; auto using cii_bijective.
    rewrite cii_range.
    apply nontriviality.
    rewrite <-(functionify_range _ _ z1).
    apply function_maps_domain_to_range.
    now rewrite functionify_domain.
  Qed.

  Lemma combinations_right_helper_l :
    ∀ x (z1 : elts (bijection_set k k)),
      x ∈ k →
      inverse (comb_inverse_image_incl h) (functionify k k z1 x) ∈ n.
  Proof.
    intros x z1 H.
    pose proof (proj2_sig y) as H0; simpl in *.
    apply Specify_classification in H0 as [H0 H1].
    apply Powerset_classification in H0.
    now apply H0, combinations_right_helper_l_1.
  Qed.

  Lemma combinations_right_helper_r_1 :
    ∀ x (z2 : elts (bijection_set (n \ k) (n \ k))),
      x ∈ n \ k →
      inverse (comb_inverse_image_incl h)
              (functionify (n \ k) (n \ k) z2 x) ∈ n \ proj1_sig y.
  Proof.
    intros x z2 H.
    apply Complement_classification in H as [H H0].
    apply Complement_classification.
    assert ((inverse (comb_inverse_image_incl h))
              ((functionify (n \ k) (n \ k) z2) x) ∈ n) as H1.
    { rewrite <-(cii_domain h), <-inverse_range; auto using cii_bijective.
      apply function_maps_domain_to_range.
      rewrite inverse_domain, cii_range; auto using cii_bijective.
      apply (complement_subset k n).
      rewrite <-(functionify_range _ _ z2).
      apply function_maps_domain_to_range.
      rewrite functionify_domain.
      now apply Complement_classification. }
    split; auto.
    intros H2.
    apply combinations_right_helper_0 in H2; auto.
    rewrite right_inverse in H2; auto using cii_bijective.
    2: { rewrite inverse_domain; auto using cii_bijective.
         rewrite cii_range.
         apply (complement_subset k n).
         rewrite <-(functionify_range _ _ z2).
         apply function_maps_domain_to_range.
         rewrite functionify_domain.
         now apply Complement_classification. }
    assert ((functionify (n \ k) (n \ k) z2) x ∈ n \ k) as H3.
    { rewrite <-(functionify_range _ _ z2).
      apply function_maps_domain_to_range.
      rewrite functionify_domain.
      now apply Complement_classification. }
    apply Complement_classification in H3.
    tauto.
  Qed.

  Lemma combinations_right_helper_r :
    ∀ x (z2 : elts (bijection_set (n \ k) (n \ k))),
      x ∈ n \ k →
      inverse (comb_inverse_image_incl h)
              (functionify (n \ k) (n \ k) z2 x) ∈ n.
  Proof.
    intros x z1 H.
    now apply (complement_subset (proj1_sig y) n),
    combinations_right_helper_r_1.
  Qed.

  Definition combinations_right_helper :
    elts (bijection_set k k) → elts (bijection_set (n \ k) (n \ k)) →
    elts n → elts n.
  Proof.
    intros z1 z2 x.
    destruct (excluded_middle_informative (proj1_sig x ∈ k)).
    - exact (exist _ _ (combinations_right_helper_l (proj1_sig x) z1 i)).
    - assert (proj1_sig x ∈ n \ k) as H.
      { apply Complement_classification.
        split; auto; apply (proj2_sig x). }
      exact (exist _ _ (combinations_right_helper_r (proj1_sig x) z2 H)).
  Defined.

  Theorem combinations_right_helper_bijective : ∀ z1 z2,
      bijective (sets.functionify n n (combinations_right_helper z1 z2)).
  Proof.
    intros z1 z2.
    apply finite_set_injection_is_bijection.
    - rewrite sets.functionify_domain.
      apply naturals_are_finite.
    - now rewrite sets.functionify_domain, sets.functionify_range.
    - pose proof (cii_bijective h) as H.
      apply inverse_bijective in H as [H H0].
      rewrite Injective_classification in *.
      intros x1 x2 H1 H2 H3.
      rewrite sets.functionify_domain in *.
      unfold sets.functionify in H3.
      destruct constructive_indefinite_description as [g].
      destruct a as [H4 [H5 H6]].
      set (ξ1 := exist _ _ H1 : elts n).
      set (ξ2 := exist _ _ H2 : elts n).
      replace x1 with (proj1_sig ξ1) in * by auto.
      replace x2 with (proj1_sig ξ2) in * by auto.
      rewrite ? H6 in H3.
      unfold combinations_right_helper in H3.
      repeat destruct excluded_middle_informative; simpl in *.
      + apply H in H3.
        2: { rewrite inverse_domain; auto using cii_bijective.
             rewrite cii_range.
             apply nontriviality.
             rewrite <-(functionify_range _ _ z1).
             apply function_maps_domain_to_range.
             now rewrite functionify_domain. }
        2: { rewrite inverse_domain; auto using cii_bijective.
             rewrite cii_range.
             apply nontriviality.
             rewrite <-(functionify_range _ _ z1).
             apply function_maps_domain_to_range.
             now rewrite functionify_domain. }
        pose proof functionify_bijective _ _ z1 as [H7 H8].
        rewrite Injective_classification in H7.
        now apply H7 in H3; try now rewrite functionify_domain.
      + assert ((inverse (comb_inverse_image_incl h))
                  ((functionify k k z1) x1) ∈ proj1_sig y) as H7
            by auto using combinations_right_helper_l_1.
        assert ((inverse (comb_inverse_image_incl h))
                  ((functionify (n \ k) (n \ k) z2) x2) ∈ n \ proj1_sig y)
          as H8 by now apply combinations_right_helper_r_1,
             Complement_classification.
        rewrite <-H3, Complement_classification in H8.
        tauto.
      + assert ((inverse (comb_inverse_image_incl h))
                  ((functionify k k z1) x2) ∈ proj1_sig y) as H7
            by auto using combinations_right_helper_l_1.
        assert ((inverse (comb_inverse_image_incl h))
                  ((functionify (n \ k) (n \ k) z2) x1) ∈ n \ proj1_sig y)
          as H8 by now apply combinations_right_helper_r_1,
             Complement_classification.
        rewrite H3, Complement_classification in H8.
        tauto.
      + apply H in H3.
        2: { rewrite inverse_domain; auto using cii_bijective.
             rewrite cii_range.
             apply (complement_subset k n).
             rewrite <-(functionify_range _ _ z2).
             apply function_maps_domain_to_range.
             now rewrite functionify_domain, Complement_classification. }
        2: { rewrite inverse_domain; auto using cii_bijective.
             rewrite cii_range.
             apply (complement_subset k n).
             rewrite <-(functionify_range _ _ z2).
             apply function_maps_domain_to_range.
             now rewrite functionify_domain, Complement_classification. }
        pose proof functionify_bijective _ _ z2 as [H7 H8].
        rewrite Injective_classification in H7.
        now apply H7 in H3;
          try now rewrite functionify_domain, Complement_classification.
  Qed.

  Theorem combinations_right_construction_proto : ∀ z1 z2,
      graph (inverse (sets.functionify n n (combinations_right_helper z1 z2)))
            ∈ bijection_set n n.
  Proof.
    intros z1 z2.
    apply Specify_classification.
    split.
    { apply Powerset_classification.
      intros x H.
      apply Graph_classification in H as [x1 [H H0]].
      subst.
      apply Product_classification.
      exists x1,
      (inverse (sets.functionify n n (combinations_right_helper z1 z2)) x1).
      repeat split.
      + rewrite inverse_domain, sets.functionify_range in H;
          auto using combinations_right_helper_bijective.
      + rewrite <-(sets.functionify_domain
                     _ _ (combinations_right_helper z1 z2)),
        <-inverse_range; auto using combinations_right_helper_bijective.
        now apply function_maps_domain_to_range. }
    exists (inverse (sets.functionify n n (combinations_right_helper z1 z2))).
    rewrite inverse_domain, inverse_range, sets.functionify_domain,
    sets.functionify_range; intuition;
      auto using combinations_right_helper_bijective, inverse_bijective.
  Qed.

  Lemma combinatorics_right_construction_helper_2 : ∀ z1 z2 x,
      x ∈ n → x ∈ k ↔ (sets.functionify n n (combinations_right_helper z1 z2)) x
                ∈ proj1_sig y.
  Proof.
    split; intros H0.
    - unfold sets.functionify.
      destruct constructive_indefinite_description as [crh].
      destruct a as [H1 [H2 H3]].
      set (ξ := exist _ _ H : elts n).
      replace x with (proj1_sig ξ) in * by auto.
      rewrite H3.
      unfold combinations_right_helper.
      destruct excluded_middle_informative; try now contradict n0.
      simpl.
      replace x with (proj1_sig ξ) in * by auto.
      now apply combinations_right_helper_l_1.
    - unfold sets.functionify in *.
      destruct constructive_indefinite_description as [crh].
      destruct a as [H1 [H2 H3]].
      set (ξ := exist _ _ H : elts n).
      replace x with (proj1_sig ξ) in * by auto.
      rewrite H3 in H0.
      unfold combinations_right_helper in H0.
      destruct excluded_middle_informative; auto.
      simpl in *.
      assert (x ∈ n \ k) as H4 by now apply Complement_classification.
      apply (combinations_right_helper_r_1 x z2),
      Complement_classification in H4.
      tauto.
  Qed.

  Theorem combinations_right_construction : ∀ z1 z2,
      graph (inverse (sets.functionify n n (combinations_right_helper z1 z2)))
            ∈ inverse_image_of_element combinations_proj (proj1_sig y).
  Proof.
    intros z1 z2.
    apply Specify_classification.
    split.
    - rewrite cp_domain.
      apply combinations_right_construction_proto.
    - set (g := (inverse (sets.functionify
                            n n (combinations_right_helper z1 z2)))).
      assert (graph g ∈ bijection_set n n).
      { apply combinations_right_construction_proto. }
      replace (graph g)
        with (proj1_sig (exist _ _ H : elts (bijection_set n n))) by auto.
      rewrite cp_action.
      apply Extensionality.
      split; intros H2.
      + apply Specify_classification in H2 as [H2 H3].
        unfold functionify in H3.
        destruct Specify_classification, a, constructive_indefinite_description
          as [crh_inv].
        clear a i0 i e.
        destruct a0 as [H4 [H5 [H6 H7]]].
        apply function_record_injective in H6; unfold g in *.
        2: { rewrite inverse_domain, sets.functionify_range;
             auto using combinations_right_helper_bijective. }
        2: { rewrite inverse_range, sets.functionify_domain;
             auto using combinations_right_helper_bijective. }
        subst.
        unfold inverse in H3.
        destruct excluded_middle_informative.
        2: { contradict n0.
             auto using combinations_right_helper_bijective. }
        destruct b, constructive_indefinite_description as [crh_inv].
        repeat destruct a.
        rewrite inverse_range, inverse_domain, sets.functionify_domain,
        sets.functionify_range in *;
          auto using combinations_right_helper_bijective.
        rewrite <-(e1 z); auto.
        apply combinatorics_right_construction_helper_2; auto.
      + apply Specify_classification.
        assert (z ∈ n) as H9.
        { pose proof proj2_sig y as H0; simpl in *.
          apply Specify_classification in H0 as [H0 H1].
          apply Powerset_classification in H0.
          now apply H0. }
        split; auto.
        unfold functionify.
        destruct Specify_classification, a, constructive_indefinite_description
          as [crh_inv].
        clear a i0 i e.
        destruct a0 as [H4 [H5 [H6 H7]]].
        apply function_record_injective in H6; unfold g in *.
        2: { rewrite inverse_domain, sets.functionify_range;
             auto using combinations_right_helper_bijective. }
        2: { rewrite inverse_range, sets.functionify_domain;
             auto using combinations_right_helper_bijective. }
        subst.
        unfold inverse.
        destruct excluded_middle_informative.
        2: { contradict n0.
             auto using combinations_right_helper_bijective. }
        destruct b, constructive_indefinite_description as [crh_inv].
        repeat destruct a.
        rewrite inverse_range, inverse_domain, sets.functionify_domain,
        sets.functionify_range in *;
          auto using combinations_right_helper_bijective.
        rewrite <-(e1 z) in H2; auto.
        apply combinatorics_right_construction_helper_2 in H2; auto.
        rewrite <-e0.
        apply function_maps_domain_to_range.
        now rewrite e.
  Qed.

  Definition combinations_right :
    elts (bijection_set k k × bijection_set (n \ k) (n \ k)) →
    elts (inverse_image_of_element combinations_proj (proj1_sig y)).
  Proof.
    intros z.
    pose proof (proj2_sig z) as H; simpl in H.
    apply Product_classification in H.
    destruct (constructive_indefinite_description _ H) as [z1].
    destruct (constructive_indefinite_description _ e) as [z2 [H0 [H1 H2]]].
    exact (exist _ _ (combinations_right_construction
                        (exist _ _ H0) (exist _ _ H1))).
  Defined.

  Theorem combinations_left_right :
    ∀ x, combinations_left (combinations_right x) = x.
  Proof.
    intros x.
    apply set_proj_injective.
    unfold combinations_left.
    simpl.
    pose proof proj2_sig x as H; simpl in H.
    apply Product_classification in H as [x1 [x2 [H [H0 H1]]]].
    rewrite H1.
    apply Ordered_pair_iff.
    split.
    - unfold sets.functionify.
      destruct constructive_indefinite_description as [x1'].
      apply Specify_classification in H as [H [x1'' [H2 [H3 [H4 H5]]]]].
      destruct a as [H6 [H7 H8]].
      rewrite <-H4.
      replace x1'' with x1'; auto.
      apply func_ext; try congruence.
      intros z H9.
      rewrite H6 in H9.
      set (ζ := exist _ _ H9 : elts k).
      replace z with (proj1_sig ζ) in * by auto.
      rewrite H8.
      unfold combinations_left_helper_k.
      destruct Specify_classification, a, Specify_classification, a0.
      simpl.
      destruct Specify_classification, a1, constructive_indefinite_description
        as [h'], Specify_classification, a3, constructive_indefinite_description
          as [cr].
      clear a i i0 e a0 i1 a1 i3 i4 e1 a3 i5 e2 H8.
      destruct a2 as [H10 [H11 [H12 H13]]].
      destruct a4 as [H14 [H15 [H16 H17]]].
      unfold inverse.
      destruct excluded_middle_informative; try tauto.
      destruct b.
      destruct constructive_indefinite_description as [cr_inv].
      repeat destruct a.
      pose proof H9 as Z.
      rewrite <-(e2 z) at 2; rewrite <-(e2 z) in Z;
        try (rewrite H15; auto).
      unfold combinations_right in H16.
      destruct constructive_indefinite_description as [z1].
      destruct constructive_indefinite_description as [z2].
      repeat destruct a.
      simpl in *.
      clear e3.
      assert ((z1,z2) = (x1,x2)) as H18 by congruence.
      apply Ordered_pair_iff in H18 as [H18 H19].
      subst.
      apply function_record_injective in H16.
      2: { rewrite H14, inverse_domain, sets.functionify_range;
           auto using combinations_right_helper_bijective. }
      2: { rewrite H15, inverse_range, sets.functionify_domain;
           auto using combinations_right_helper_bijective. }
      clear H17 i s.
      subst.
      rewrite inverse_domain, inverse_range, sets.functionify_domain,
      sets.functionify_range in *;
        auto using combinations_right_helper_bijective.
      unfold inverse in Z |-*.
      destruct excluded_middle_informative.
      2: { exfalso; auto using combinations_right_helper_bijective. }
      destruct b, constructive_indefinite_description as [crh_inv].
      repeat destruct a.
      rewrite ? inverse_domain, ? inverse_range, ? sets.functionify_domain,
      ? sets.functionify_range in *;
        auto using combinations_right_helper_bijective.
      clear i s.
      rewrite <-(e6 (cr_inv z)) at 1.
      2: { rewrite <-e1.
           apply function_maps_domain_to_range.
           rewrite e; auto. }
      unfold sets.functionify.
      destruct constructive_indefinite_description as [crh].
      destruct a as [H4 [H8 H16]].
      assert (crh_inv (cr_inv z) ∈ n) as H17.
      { rewrite <-e5.
        apply function_maps_domain_to_range.
        rewrite e3, <-e1.
        apply function_maps_domain_to_range.
        rewrite e; auto. }
      set (ζ' := exist _ _ H17 : elts n).
      replace (crh_inv (cr_inv z)) with (proj1_sig ζ') by auto.
      rewrite H16.
      unfold combinations_right_helper.
      destruct excluded_middle_informative.
      2: { now contradict n0. }
      simpl.
      destruct Specify_classification, a,
      constructive_indefinite_description as [x1].
      clear a i3 i4 e7.
      destruct a0 as [H18 [H19 [H20 H21]]].
      apply function_record_injective in H20; try congruence.
      subst.
      unfold inverse.
      destruct excluded_middle_informative.
      2: { exfalso; auto using cii_bijective. }
      destruct b, constructive_indefinite_description as [cii].
      repeat destruct a.
      rewrite <-(e9 (x1'' (crh_inv (cr_inv z)))) at 2.
      2: { rewrite cii_range.
           apply nontriviality.
           rewrite <-H19.
           apply function_maps_domain_to_range.
           congruence. }
      destruct h as [h'' H''].
      unfold comb_inverse_image_incl.
      simpl.
      destruct Specify_classification, a,
      constructive_indefinite_description as [h'''].
      clear e7 e8 e9 i i3 i4 i5 e10 a s.
      simpl in H12.
      destruct a0 as [H22 [H23 [H24 H25]]].
      replace h' with h'''; try congruence.
      apply function_record_injective; congruence.
    - unfold sets.functionify.
      destruct constructive_indefinite_description as [x2'].
      apply Specify_classification in H0 as [H0 [x2'' [H2 [H3 [H4 H5]]]]].
      destruct a as [H6 [H7 H8]].
      rewrite <-H4.
      replace x2'' with x2'; auto.
      apply func_ext; try congruence.
      intros z H9.
      rewrite H6 in H9.
      set (ζ := exist _ _ H9 : elts (n \ k)).
      replace z with (proj1_sig ζ) in * by auto.
      rewrite H8.
      unfold combinations_left_helper_n_minus_k.
      destruct Specify_classification, a, Specify_classification, a0.
      simpl.
      destruct Specify_classification, a1, constructive_indefinite_description
        as [h'], Specify_classification, a3, constructive_indefinite_description
          as [cr].
      clear a i i0 e a0 i1 a1 i3 i4 e1 a3 i5 e2 H8.
      destruct a2 as [H10 [H11 [H12 H13]]].
      destruct a4 as [H14 [H15 [H16 H17]]].
      unfold inverse.
      destruct excluded_middle_informative; try tauto.
      destruct b.
      destruct constructive_indefinite_description as [cr_inv].
      repeat destruct a.
      pose proof H9 as Z.
      rewrite <-(e2 z) at 2; rewrite <-(e2 z) in Z;
        try (rewrite H15; apply (complement_subset k n); auto).
      unfold combinations_right in H16.
      destruct constructive_indefinite_description as [z1].
      destruct constructive_indefinite_description as [z2].
      repeat destruct a.
      simpl in *.
      clear e3.
      assert ((z1,z2) = (x1,x2)) as H18 by congruence.
      apply Ordered_pair_iff in H18 as [H18 H19].
      subst.
      apply function_record_injective in H16.
      2: { rewrite H14, inverse_domain, sets.functionify_range;
           auto using combinations_right_helper_bijective. }
      2: { rewrite H15, inverse_range, sets.functionify_domain;
           auto using combinations_right_helper_bijective. }
      clear H17 i s.
      subst.
      rewrite inverse_domain, inverse_range, sets.functionify_domain,
      sets.functionify_range in *;
        auto using combinations_right_helper_bijective.
      unfold inverse in Z |-*.
      destruct excluded_middle_informative.
      2: { exfalso; auto using combinations_right_helper_bijective. }
      destruct b, constructive_indefinite_description as [crh_inv].
      repeat destruct a.
      rewrite ? inverse_domain, ? inverse_range, ? sets.functionify_domain,
      ? sets.functionify_range in *;
        auto using combinations_right_helper_bijective.
      clear i s.
      rewrite <-(e6 (cr_inv z)) at 1.
      2: { rewrite <-e1.
           apply function_maps_domain_to_range.
           rewrite e; apply (complement_subset k n); auto. }
      unfold sets.functionify.
      destruct constructive_indefinite_description as [crh].
      destruct a as [H4 [H8 H16]].
      assert (crh_inv (cr_inv z) ∈ n) as H17.
      { rewrite <-e5.
        apply function_maps_domain_to_range.
        rewrite e3, <-e1.
        apply function_maps_domain_to_range.
        rewrite e; apply (complement_subset k n); auto. }
      set (ζ' := exist _ _ H17 : elts n).
      replace (crh_inv (cr_inv z)) with (proj1_sig ζ') by auto.
      rewrite H16.
      unfold combinations_right_helper.
      destruct excluded_middle_informative.
      { simpl in i.
        apply Complement_classification in Z.
        tauto. }
      simpl.
      destruct Specify_classification, a,
      constructive_indefinite_description as [x2].
      clear a i i3 e7.
      destruct a0 as [H18 [H19 [H20 H21]]].
      apply function_record_injective in H20; try congruence.
      subst.
      unfold inverse.
      destruct excluded_middle_informative.
      2: { exfalso; auto using cii_bijective. }
      destruct b, constructive_indefinite_description as [cii].
      repeat destruct a.
      rewrite <-(e9 (x2'' (crh_inv (cr_inv z)))) at 2.
      2: { rewrite cii_range.
           apply (complement_subset k n).
           rewrite <-H19.
           apply function_maps_domain_to_range.
           congruence. }
      destruct h as [h'' H''].
      unfold comb_inverse_image_incl.
      simpl.
      destruct Specify_classification, a,
      constructive_indefinite_description as [h'''].
      clear e7 e8 e9 i i3 i4 e10 a s.
      simpl in H12.
      destruct a0 as [H22 [H23 [H24 H25]]].
      replace h' with h'''; try congruence.
      apply function_record_injective; congruence.
  Qed.

  Theorem combinations_right_left :
    ∀ x, combinations_right (combinations_left x) = x.
  Proof.
    intros x.
    apply set_proj_injective.
    unfold combinations_right.
    destruct constructive_indefinite_description as [x1].
    destruct constructive_indefinite_description as [x2].
    clear e.
    repeat destruct a.
    simpl.
    unfold combinations_left in e.
    simpl in e.
    apply Ordered_pair_iff in e as [e e0].
    subst.
    pose proof proj2_sig x as H; simpl in H.
    apply Inverse_image_classification_domain in H as H0.
    2: { rewrite cp_range.
         apply (proj2_sig y). }
    rewrite cp_domain in H0.
    apply Specify_classification in H0 as [H0 [x' [H1 [H2 [H3 H4]]]]].
    rewrite <-H3.
    f_equal.
    apply func_ext.
    { rewrite inverse_domain; auto using combinations_right_helper_bijective.
      rewrite sets.functionify_range.
      congruence. }
    { rewrite inverse_range; auto using combinations_right_helper_bijective.
      rewrite sets.functionify_domain.
      congruence. }
    intros z H5.
    rewrite inverse_domain, sets.functionify_range in H5;
      auto using combinations_right_helper_bijective.
    assert (x' z ∈ n) as H6.
    { rewrite <-H2.
      apply function_maps_domain_to_range.
      congruence. }
    rewrite inverse_shift_right; auto using combinations_right_helper_bijective.
    2: { now rewrite sets.functionify_range. }
    2: { now rewrite sets.functionify_domain. }
    unfold sets.functionify.
    destruct constructive_indefinite_description as [crh].
    destruct a as [H7 [H8 H9]].
    set (ξ'ζ := exist _ _ H6 : elts n).
    replace (x' z) with (proj1_sig ξ'ζ) by auto.
    rewrite H9.
    clear H9.
    unfold combinations_right_helper.
    destruct excluded_middle_informative.
    + simpl.
      destruct Specify_classification, a,
      constructive_indefinite_description as [clh].
      destruct constructive_indefinite_description as [clh'].
      destruct a0 as [H9 [H10 H11]].
      destruct a1 as [H12 [H13 [H14 H15]]].
      clear a i2 i3 e.
      apply function_record_injective in H14; try congruence.
      subst.
      set (ξ'ζ' := exist _ _ i1 : elts k).
      replace (x' z) with (proj1_sig ξ'ζ') by auto.
      rewrite H11.
      unfold combinations_left_helper_k.
      destruct Specify_classification, a, Specify_classification, a0.
      simpl.
      destruct Specify_classification, a1,
      constructive_indefinite_description as [h'].
      destruct Specify_classification, a3,
      constructive_indefinite_description as [x''].
      clear a i2 i3 e a0 i4 i5 e0 a1 i6 i7 e1 a3 i8 i9 e2.
      destruct a2 as [H16 [H17 [H18 H19]]].
      destruct a4 as [H20 [H21 [H22 H23]]].
      replace x'' with x'.
      2: { apply function_record_injective; congruence. }
      rewrite left_inverse; auto; try congruence.
      symmetry.
      rewrite inverse_shift_right; auto using cii_bijective.
      2: { rewrite cii_range, <-H17.
           apply function_maps_domain_to_range.
           congruence. }
      2: { now rewrite cii_domain. }
      destruct h as [h'' H''].
      unfold comb_inverse_image_incl, functionify.
      destruct Specify_classification, a,
      constructive_indefinite_description as [h'''].
      clear a i2 i3 e.
      destruct a0 as [H24 [H25 [H26 H27]]].
      simpl in H18.
      f_equal.
      apply function_record_injective; congruence.
    + assert (proj1_sig ξ'ζ ∈ n \ k) as Z by
            now apply Complement_classification.
      simpl in *.
      destruct Specify_classification, a,
      constructive_indefinite_description as [clh].
      destruct constructive_indefinite_description as [clh'].
      destruct a0 as [H9 [H10 H11]].
      destruct a1 as [H12 [H13 [H14 H15]]].
      clear a i1 i2 e.
      apply function_record_injective in H14; try congruence.
      subst.
      set (ξ'ζ' := exist _ _ Z : elts (n \ k)).
      replace (x' z) with (proj1_sig ξ'ζ') by auto.
      rewrite H11.
      unfold combinations_left_helper_n_minus_k.
      destruct Specify_classification, a, Specify_classification, a0.
      simpl.
      destruct Specify_classification, a1,
      constructive_indefinite_description as [h'].
      destruct Specify_classification, a3,
      constructive_indefinite_description as [x''].
      clear a i2 i3 e a0 i4 i5 e0 a1 i6 i7 e1 a3 i8 i1 e2.
      destruct a2 as [H16 [H17 [H18 H19]]].
      destruct a4 as [H20 [H21 [H22 H23]]].
      replace x'' with x'.
      2: { apply function_record_injective; congruence. }
      rewrite left_inverse; auto; try congruence.
      symmetry.
      rewrite inverse_shift_right; auto using cii_bijective.
      2: { rewrite cii_range, <-H17.
           apply function_maps_domain_to_range.
           congruence. }
      2: { now rewrite cii_domain. }
      destruct h as [h'' H''].
      unfold comb_inverse_image_incl, functionify.
      destruct Specify_classification, a,
      constructive_indefinite_description as [h'''].
      clear a i1 i2 e.
      destruct a0 as [H24 [H25 [H26 H27]]].
      simpl in H18.
      f_equal.
      apply function_record_injective; congruence.
  Qed.

End Combinations_orbit_stabilizer.

Theorem combinations_orbit_stabilizer : ∀ n k : N,
    k ⊂ n → bijection_set n n ~ (set_of_combinations n k) ×
                          (bijection_set k k × bijection_set (n \ k) (n \ k)).
Proof.
  intros n k H.
  rewrite <-(cp_domain n k H), <-(cp_range n k H).
  apply orbit_stabilizer_cardinality.
  intros y H0.
  rewrite cp_range in H0.
  set (γ := exist _ _ H0 : elts (set_of_combinations n k)).
  replace y with (proj1_sig γ) in * by auto.
  apply two_sided_inverse_bijective.
  exists (combinations_left n k H γ), (combinations_right n k H γ).
  auto using combinations_left_right, combinations_right_left.
Qed.

Theorem binomials_are_finite : ∀ n k, finite (set_of_combinations n k).
Proof.
  intros n k.
  eauto using Specify_subset, subsets_of_finites_are_finite,
  powerset_finite, naturals_are_finite.
Qed.

Lemma binomial_coefficient_1 :
  ∀ n m, (n + m)! = (binomial (n + m) m * m! * n!)%Z.
Proof.
  intros n m.
  assert (m ⊂ n + m)%N as H.
  { rewrite <-le_is_subset, add_comm.
    now exists n. }
  pose proof (combinations_orbit_stabilizer (n+m) m) H as H0.
  rewrite add_comm, (naturals_sum_diff n m), add_comm in H0.
  apply equinumerous_cardinality in H0.
  rewrite ? finite_products_card, ? number_of_permutations_n, ? INZ_mul,
  <-mul_assoc in *; auto using permutations_are_finite, binomials_are_finite,
                    finite_products_are_finite.
  now apply INZ_eq.
Qed.

Theorem binomial_coefficient :
  ∀ n k, (k ≤ n)%N → n! = (binomial n k * k! * (n - k)!)%Z.
Proof.
  intros n k [m H].
  subst.
  rewrite (add_comm k), sub_abba.
  apply binomial_coefficient_1.
Qed.

Lemma factorial_ne_0 : ∀ k, k! ≠ 0%Z.
Proof.
  intros k H.
  induction k using Induction; unfold factorial in *.
  - unfold prod, iterate_with_bounds in H.
    destruct excluded_middle_informative.
    + pose proof l as H0.
      rewrite naturals.le_not_gt in H0.
      contradict H0.
      apply naturals.succ_lt.
    + contradiction integers.zero_ne_1.
  - rewrite prod_succ in H.
    + apply (cancellation_0_mul integer_order) in H as [H | H]; auto.
      apply INZ_eq in H.
      now contradiction (PA4 k).
    + exists k.
      now rewrite add_comm, add_1_r.
Qed.

Theorem binomial_coefficient_Q :
  ∀ n k, (k ≤ n)%N → (n! / (k! * (n - k)!))%Q = binomial n k.
Proof.
  intros n k H.
  assert ((k! * (n - k)!)%Z ≠ 0%Z) as H0.
  { apply (ne0_cancellation (integral_domain_OR integer_order));
      auto using factorial_ne_0. }
  apply binomial_coefficient in H.
  rewrite H, <-integers.M2, inv_div, <-IZQ_mul; auto.
  field_simplify; rewrite ? div_inv, ? inv_one; try ring; auto.
  contradict H0.
  now apply IZQ_eq in H0.
Qed.
