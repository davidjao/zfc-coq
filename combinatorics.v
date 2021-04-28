Set Warnings "-ambiguous-paths".
Require Export cardinality rationals.

Definition permutations (n : N) := size_of_bijections n n.

Definition factorial n := (prod_N id 1 n).

Notation "n !" := (factorial n) (at level 35, format "n '!'") : N_scope.

Definition set_of_combinations (n k : N) := {x in P n | # x = k}.

Definition binomial n k := # set_of_combinations n k.

(* The goal is to prove that the number of permutations of n is n!,
   and that (binomial n k) = n!/(k! (n-k)!). *)

Open Scope set_scope.

Section orbit_stabilizer_cardinality_theorem.

  Variable f : function.
  Variable x Y : set.
  Hypothesis Y_subset : image f ⊂ Y.
  Hypothesis Y_inv : ∀ y, y ∈ Y → inverse_image_of_element f y ~ x.

  Definition oschf : set → function.
  Proof.
    intros z.
    destruct (excluded_middle_informative (z ~ x)).
    - destruct (constructive_indefinite_description e) as [g [H1 [H2 H3]]].
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

  Theorem orbit_stabilizer_cardinality_helper : domain f ~ Y × x.
  Proof.
    destruct (function_construction
                (domain f) (Y × x)
                (λ x,
                 (f x, (oschf (inverse_image_of_element f (f x)) x))))
      as [g [H [H0 H1]]].
    { intros a H.
      unfold oschf.
      destruct excluded_middle_informative.
      - destruct constructive_indefinite_description as [g].
        repeat destruct a0.
        apply Product_classification.
        exists (f a), (g a).
        repeat split; auto using function_maps_domain_to_image.
        rewrite <-e1.
        apply function_maps_domain_to_range.
        rewrite -> e0.
        unfold inverse_image_of_element.
        now apply Specify_classification.
      - contradict n.
        auto using function_maps_domain_to_image. }
    exists g.
    repeat split; auto.
    - apply Injective_classification.
      intros u v H2 H3 H4.
      rewrite -> H in H2, H3.
      rewrite -> ? H1 in H4; auto.
      apply Ordered_pair_iff in H4 as [H4 H5].
      rewrite -> H4 in H5.
      unfold oschf in H5.
      destruct excluded_middle_informative;
        try (contradict n; auto using function_maps_domain_to_image).
      destruct constructive_indefinite_description as [h].
      repeat destruct a.
      destruct b.
      rewrite -> Injective_classification in H6.
      apply H6 in H5; auto; rewrite -> e0; unfold inverse_image_of_element;
          now apply Specify_classification.
    - rewrite -> Surjective_classification.
      intros y H2.
      rewrite -> H0 in H2.
      apply Product_classification in H2 as [a [b [H2 [H3 H4]]]].
      subst.
      pose proof oschf_bijective (inverse_image_of_element f a) (Y_inv a H2)
        as [H4 H5].
      rewrite -> Surjective_classification in H5.
      destruct (H5 b) as [z [H6 H7]].
      { rewrite -> oschf_range; auto. }
      rewrite -> oschf_domain in H6; auto.
      apply Specify_classification in H6.
      exists z.
      split; intuition; try congruence.
      rewrite -> H1; congruence.
  Qed.

End orbit_stabilizer_cardinality_theorem.

Theorem orbit_stabilizer_cardinality : ∀ f x,
    (∀ y, y ∈ range f → inverse_image_of_element f y ~ x) →
    domain f ~ range f × x.
Proof.
  intros f x H.
  auto using orbit_stabilizer_cardinality_helper, image_subset_range.
Qed.

Theorem orbit_stabilizer_cardinality_image : ∀ f x,
    (∀ y, y ∈ image f → inverse_image_of_element f y ~ x) →
    domain f ~ image f × x.
Proof.
  intros f x H.
  auto using orbit_stabilizer_cardinality_helper, Set_is_subset.
Qed.

Section permutation_succ_helper_functions.

  Variable n : N.
  Variable y : elts (S n).

  Section functionify_construction.

    Variable A B : set.
    Definition functionify : elts (bijection_set A B) → function.
    Proof.
      intros [f F].
      apply Specify_classification in F as [F F0].
      destruct (constructive_indefinite_description F0) as [f'].
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

    Theorem functionify_graph : ∀ f, graph (functionify f) = f.
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
      destruct (constructive_indefinite_description H0)
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
    rewrite -> e0, <-lt_is_in.
    apply naturals.succ_lt.
  Qed.

  Definition permutation_succ_proj : function.
  Proof.
    destruct (constructive_indefinite_description
                (function_construction
                   (bijection_set (S n) (S n)) (S n)
                   permutation_succ_helper permutation_succ_proj_construction))
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
    rewrite -> lt_is_in in H.
    exact (mkSet H).
  Defined.

  Theorem psp_action :
    ∀ x :  elts (bijection_set (S n) (S n)),
      permutation_succ_proj x = ((functionify (S n) (S n) x) n).
  Proof.
    intros x.
    unfold permutation_succ_proj.
    destruct constructive_indefinite_description as [f].
    destruct a as [H [H0 H1]].
    rewrite -> H1; auto using elts_in_set.
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
      auto using elts_in_set.
  Qed.

  Definition inverse_image_incl :
    elts (inverse_image_of_element permutation_succ_proj y) →
    elts (bijection_set (S n) (S n)).
  Proof.
    intros [f F].
    unfold inverse_image_of_element in F.
    apply Specify_classification in F as [F F0].
    rewrite -> psp_domain in F.
    exact (mkSet F).
  Defined.

  Lemma inverse_image_incl_value :
    ∀ f, (inverse_image_incl f : set) = (f : set).
  Proof.
    intros f.
    unfold inverse_image_incl, inverse_image_of_element in *.
    now destruct f, Specify_classification, a.
  Qed.

  Lemma inverse_image_classification:
    ∀ f : elts (inverse_image_of_element permutation_succ_proj y),
      ((functionify (S n) (S n) (inverse_image_incl f)) n) = y.
  Proof.
    intros f.
    unfold functionify, inverse_image_incl, inverse_image_of_element in *.
    destruct f.
    destruct Specify_classification, a, Specify_classification, a0,
    constructive_indefinite_description as [f'].
    destruct a1 as [H [H0 [H1 H2]]].
    apply Specify_classification in elts_in_set as [H3 H4]; auto.
    clear i a i1 i2 a0 e0.
    rewrite -> psp_domain in H3.
    set (ξ := mkSet H3 : elts (bijection_set (S n) (S n))).
    replace elt_to_set with (ξ : set) in * by auto.
    rewrite <-e, psp_action.
    f_equal.
    apply function_record_injective;
      now rewrite -> ? functionify_domain, ? functionify_range,
      ? functionify_graph; congruence.
  Qed.

  Theorem permutation_succ_left_helper_lemma :
    ∀ f (x : elts n), ((functionify (S n) (S n) (inverse_image_incl f))
                         x ∈ S n \ {y, y}).
  Proof.
    intros f x.
    apply Complement_classification.
    split.
    - rewrite <-(functionify_range (S n) (S n) (inverse_image_incl f)).
      apply function_maps_domain_to_range.
      rewrite -> functionify_domain, <-S_is_succ.
      apply Pairwise_union_classification.
      left.
      auto using elts_in_set.
    - rewrite -> Singleton_classification, <-(inverse_image_classification f).
      intros H.
      pose proof (functionify_bijective _ _ (inverse_image_incl f)) as [H0 H1].
      rewrite -> Injective_classification in H0.
      apply H0 in H.
      + contradiction (no_quines n).
        rewrite <-H at 1.
        auto using elts_in_set.
      + rewrite -> functionify_domain, <-S_is_succ.
        apply Pairwise_union_classification.
        left.
        auto using elts_in_set.
      + rewrite -> functionify_domain, <-lt_is_in.
        apply naturals.succ_lt.
  Qed.

  Definition permutation_succ_left_helper :
    elts (inverse_image_of_element permutation_succ_proj y) →
    elts n → elts (S n \ {y, y}).
  Proof.
    intros f x.
    exact (mkSet (permutation_succ_left_helper_lemma f x)).
  Defined.

  Theorem pslh_action : ∀ f (x : elts n),
      (functionify _ _ (inverse_image_incl f)) x =
      (permutation_succ_left_helper f x).
  Proof.
    intros f x.
    unfold permutation_succ_left_helper.
    now simpl.
  Qed.

  Theorem psl_bijective :
    ∀ f, bijective (sets.functionify (permutation_succ_left_helper f)).
  Proof.
    intros f.
    split.
    - rewrite -> Injective_classification.
      intros x1 x2 H H0 H1.
      unfold sets.functionify in *.
      destruct constructive_indefinite_description as [f'].
      destruct a as [H2 [H3 H4]].
      rewrite -> H2 in H, H0.
      set (ξ1 := (mkSet H : elts n)).
      set (ξ2 := (mkSet H0 : elts n)).
      replace x1 with (ξ1 : set) in * by auto.
      replace x2 with (ξ2 : set) in * by auto.
      rewrite -> ? H4, ? pslh_action in H1.
      pose proof functionify_bijective _ _ (inverse_image_incl f) as [H5 H6].
      rewrite -> Injective_classification in H5.
      apply H5; auto; rewrite -> functionify_domain, <-S_is_succ;
        apply Pairwise_union_classification; left; auto using elts_in_set.
    - apply Surjective_classification.
      intros z H.
      unfold sets.functionify in *.
      destruct constructive_indefinite_description as [f'].
      destruct a as [H0 [H1 H2]].
      rewrite -> H1 in H.
      apply Complement_classification in H as [H H3].
      rewrite -> Singleton_classification in H3.
      pose proof functionify_bijective _ _ (inverse_image_incl f) as [H4 H5].
      rewrite -> Surjective_classification, functionify_range,
      functionify_domain in H5.
      pose proof H as H6.
      apply H5 in H6 as [x [H6 H7]].
      exists x.
      assert (x ∈ n).
      { rewrite <-S_is_succ in H6.
        apply Pairwise_union_classification in H6 as [H6 | H6]; auto.
        apply Singleton_classification in H6; subst.
        now rewrite -> inverse_image_classification in H3. }
      split; try congruence.
      set (ξ := (mkSet H8 : elts n)).
      replace x with (ξ : set) by auto.
      now rewrite -> H2, <-pslh_action.
  Qed.

  Theorem permutation_succ_left_construction : ∀ f,
      graph (sets.functionify (permutation_succ_left_helper f))
            ∈ bijection_set n (S n \ {y, y}).
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
    - exists (sets.functionify (permutation_succ_left_helper f)).
      pose proof psl_bijective f.
      unfold sets.functionify in *.
      destruct constructive_indefinite_description.
      tauto.
  Qed.

  Definition permutation_succ_left :
    elts (inverse_image_of_element permutation_succ_proj y) →
    elts (bijection_set n (S n \ {y, y})).
  Proof.
    intros f.
    exact (mkSet (permutation_succ_left_construction f)).
  Defined.

  Definition permutation_succ_right_helper :
    elts (bijection_set n (S n \ {y, y})) → elts (S n) → elts (S n).
  Proof.
    intros f x.
    destruct (excluded_middle_informative ((x : set) = n)).
    - exact y.
    - assert ((functionify _ _ f) x ∈ S n \ {y, y}).
      { rewrite <-(functionify_range _ _ f).
        apply function_maps_domain_to_range.
        rewrite -> functionify_domain.
        pose proof elts_in_set x as H.
        simpl in *.
        rewrite <-S_is_succ in H.
        apply Pairwise_union_classification in H as [H | H]; auto.
        now apply Singleton_classification in H. }
      apply Complement_classification in H as [H H0].
      exact (mkSet H).
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
    ∀ f, bijective (sets.functionify (permutation_succ_right_helper f)).
  Proof.
    intros f.
    unfold sets.functionify.
    destruct constructive_indefinite_description as [f'].
    destruct a as [H [H0 H1]].
    split.
    - rewrite -> Injective_classification.
      intros x1 x2 H2 H3 H4.
      rewrite -> H in H2, H3.
      set (ξ1 := mkSet H2 : elts (S n)).
      set (ξ2 := mkSet H3 : elts (S n)).
      replace x1 with (ξ1 : set) in * by auto.
      replace x2 with (ξ2 : set) in * by auto.
      rewrite -> ? H1 in H4.
      unfold permutation_succ_right_helper in H4.
      repeat destruct excluded_middle_informative; simpl in *; try congruence;
        try (destruct Complement_classification, a;
             simpl in *; contradict n1; now rewrite Singleton_classification).
      repeat destruct Complement_classification.
      destruct a, a0.
      simpl in *.
      pose proof (functionify_bijective _ _ f) as [H5 H6].
      rewrite -> Injective_classification in H5.
      clear ξ1 ξ2.
      apply H5; auto; rewrite -> functionify_domain.
      + rewrite <-S_is_succ in H2.
        apply Pairwise_union_classification in H2 as [H2 | H2]; auto.
        now rewrite -> Singleton_classification in H2.
      + rewrite <-S_is_succ in H3.
        apply Pairwise_union_classification in H3 as [H3 | H3]; auto.
        now rewrite -> Singleton_classification in H3.
    - rewrite -> Surjective_classification.
      intros z H2.
      rewrite -> H0 in H2.
      set (ζ := mkSet H2 : elts (S n)).
      replace z with (ζ : set) in * by auto.
      destruct (classic (ζ = y)).
      + exists n.
        split.
        * rewrite -> H, <-S_is_succ.
          apply Pairwise_union_classification.
          rewrite -> Singleton_classification; tauto.
        * replace (n : set) with (n_in_Sn : set) by auto.
          rewrite -> H1, psrh_n.
          congruence.
      + pose proof (functionify_bijective _ _ f) as [H4 H5].
        rewrite -> Surjective_classification, functionify_range,
        functionify_domain in H5.
        assert (z ∈ S n \ {y, y}).
        { rewrite -> Complement_classification, Singleton_classification.
          split; auto.
          contradict H3.
          now apply set_proj_injective. }
        apply H5 in H6 as [x [H6 H7]].
        exists x.
        split.
        * rewrite -> H, <-S_is_succ.
          apply Pairwise_union_classification; tauto.
        * assert (x ∈ S n).
          { rewrite <-S_is_succ.
            apply Pairwise_union_classification; tauto. }
          set (ξ := mkSet H8 : elts (S n)).
          replace x with (ξ : set) in * by auto.
          rewrite -> H1.
          unfold permutation_succ_right_helper.
          destruct excluded_middle_informative.
          -- rewrite -> e in H6.
             contradiction (no_quines n).
          -- destruct Complement_classification, a.
             now simpl in *.
  Qed.

  Lemma permutation_succ_right_construction : ∀ f,
      graph (sets.functionify (permutation_succ_right_helper f)) ∈
            (inverse_image_of_element permutation_succ_proj y).
  Proof.
    intros.
    unfold inverse_image_of_element.
    apply Specify_classification.
    assert
        (graph (sets.functionify (permutation_succ_right_helper f))
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
        exists (sets.functionify (permutation_succ_right_helper f)).
        unfold sets.functionify in *.
        destruct constructive_indefinite_description.
        tauto. }
    split.
    - unfold permutation_succ_proj.
      destruct constructive_indefinite_description.
      destruct a as [H0 [H1 H2]].
      rewrite -> H0; auto.
    - set (γ := mkSet H : elts (bijection_set (S n) (S n))).
      replace (graph (sets.functionify (permutation_succ_right_helper f)))
        with (γ : set) in * by auto.
      rewrite -> psp_action.
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
        replace (n : set) with (n_in_Sn : set) by auto.
        now rewrite -> H6, psrh_n.
      + now rewrite -> sets.functionify_range.
  Qed.

  Definition permutation_succ_right :
    elts (bijection_set n (S n \ {y, y})) →
    elts (inverse_image_of_element permutation_succ_proj y).
  Proof.
    intros f.
    exact (mkSet (permutation_succ_right_construction f)).
  Defined.

End permutation_succ_helper_functions.

Theorem permutation_succ :
  ∀ n : N, bijection_set (S n) (S n) ~ (S n) × (bijection_set n n).
Proof.
  intros n.
  rewrite <-psp_domain, <-psp_range.
  apply orbit_stabilizer_cardinality.
  intros y H.
  rewrite -> psp_range in H.
  replace (n : set) with (S n \ {n,n}) at 2.
  2: { rewrite <-S_is_succ.
       apply complement_disjoint_union, disjoint_succ. }
  setoid_replace (S n \ {n,n}) with (S n \ {y,y}).
  2: { apply equivalence_minus_element; auto using cardinality_refl;
       apply lt_is_in, naturals.succ_lt. }
  apply two_sided_inverse_bijective.
  set (γ := mkSet H : elts (S n)).
  replace y with (γ : set) in * by auto.
  exists (permutation_succ_left _ γ), (permutation_succ_right _ γ).
  split.
  - intros a.
    pose proof (elts_in_set a) as H0; simpl in H0.
    apply set_proj_injective, (function_graph_equality (S n) (S n)); simpl in *.
    { pose proof func_hyp (sets.functionify
                             (permutation_succ_right_helper
                                _ _ (permutation_succ_left _ γ a))).
      now rewrite -> @sets.functionify_domain, @sets.functionify_range in *. }
    { pose proof elts_in_set a.
      simpl in *.
      apply Inverse_image_subset in H0.
      - rewrite -> psp_domain in H0.
        apply Specify_classification in H0 as [H0 [f H2]].
        pose proof func_hyp f.
        intuition; congruence.
      - now rewrite -> psp_range. }
    intros z H1.
    apply Graph_classification in H1 as [z1 [H1 H2]].
    subst.
    rewrite -> @sets.functionify_domain, (reify H1), functionify_action in *.
    unfold permutation_succ_right_helper; simpl.
    destruct excluded_middle_informative.
    * subst.
      apply Inverse_image_classification in H0 as H2.
      2: { apply Specify_classification in H0; tauto. }
      2: { now rewrite -> psp_range. }
      apply Specify_classification in H0 as [H0 H3].
      rewrite -> psp_domain in H0.
      set (α := mkSet H0 : elts (bijection_set (S n) (S n))).
      replace (a : set) with (α : set) in * by auto.
      rewrite -> psp_action in H2.
      simpl.
      pose proof H0 as H4.
      apply Specify_classification in H4 as [H4 [f' [H5 [H6 [H7 H8]]]]].
      assert (graph f' = α) as H9 by now rewrite -> H7.
      rewrite <-(functionify_graph (S n) (S n) α) in H9.
      apply function_record_injective in H9; try now rewrite functionify_range.
      rewrite <-H7, H9.
      apply Graph_classification.
      exists n.
      split; congruence.
    * destruct Complement_classification, a0, Specify_classification,
      a1, constructive_indefinite_description as [f'].
      simpl.
      clear n1 i0 i a0 e i2 i1 a1.
      destruct a2 as [H2 [H3 [H4 H5]]].
      assert ((z1, f' z1) ∈ graph f').
      { apply Graph_classification.
        exists z1.
        split; auto.
        rewrite <-S_is_succ in H1.
        apply Pairwise_union_classification in H1 as [H1 | H1]; try congruence.
        now apply Singleton_classification in H1. }
      rewrite -> H4 in H6.
      apply Graph_classification in H6 as [z1' [H6 H7]].
      apply Ordered_pair_iff in H7 as [H7 H8].
      subst.
      rewrite -> H8, @sets.functionify_domain, (reify H6),
      functionify_action in *.
      simpl.
      clear H8 H5 H3 H2 H1.
      rewrite -> Inverse_image_classification in H0.
      2: { rewrite -> psp_domain.
           pose proof (elts_in_set (inverse_image_incl n (mkSet H) a)).
           simpl in *.
           now rewrite -> inverse_image_incl_value in H1. }
      2: { now rewrite -> psp_range. }
      replace (a : set) with (inverse_image_incl n (mkSet H) a : set) in *.
      2: { now rewrite -> inverse_image_incl_value. }
      rewrite -> psp_action in H0.
      unfold functionify in H0.
      destruct inverse_image_incl, Specify_classification, a0,
      constructive_indefinite_description as [f].
      clear a0 i i0 e.
      simpl.
      destruct Specify_classification, a0,
      constructive_indefinite_description, a2 as [H1 [H2 [H3 H5]]].
      rewrite <-H3.
      apply Graph_classification.
      exists z1'.
      split; auto.
      rewrite -> H1, <-S_is_succ.
      apply Pairwise_union_classification; tauto.
  - intros b.
    pose proof (elts_in_set b) as H0; simpl in H0.
    apply set_proj_injective; simpl.
    apply (function_graph_equality n (S n \ {y,y})); auto.
    { pose proof (func_hyp (sets.functionify
                              (permutation_succ_left_helper
                                 _ _ (permutation_succ_right n γ b)))).
      now rewrite -> @sets.functionify_domain, @sets.functionify_range in *. }
    { apply Specify_classification in H0 as [H0 [f H2]].
      replace (b : set) with (graph f) by intuition.
      pose proof func_hyp f.
      intuition; congruence. }
    intros z H3.
    unfold sets.functionify in H3.
    destruct constructive_indefinite_description as [f].
    destruct a as [H4 [H5 H6]].
    apply Graph_classification in H3 as [z1 [H3 H7]].
    subst.
    rewrite -> H4 in H3.
    set (ζ := mkSet H3 : elts n).
    replace z1 with (ζ : set) in * by auto.
    rewrite -> H6.
    apply Specify_classification in H0 as [H0 [f' [H7 [H8 [H9 H10]]]]].
    rewrite <-H9.
    apply Graph_classification.
    exists ζ.
    split; try (simpl; congruence).
    rewrite <-(pslh_action n γ).
    apply Ordered_pair_iff.
    split; auto.
    clear f H4 H5 H6.
    unfold functionify, inverse_image_incl, permutation_succ_right.
    destruct Specify_classification, a, Specify_classification, a0,
    constructive_indefinite_description.
    clear e0 i2 i1 a0 e i0 i a.
    destruct a1 as [H1 [H2 [H4 H5]]].
    apply function_record_injective in H4;
      rewrite -> ? sets.functionify_domain, ? sets.functionify_range; auto.
    subst.
    unfold sets.functionify.
    destruct constructive_indefinite_description.
    destruct a as [H4 [H6 H11]].
    assert (z1 ∈ S n) as H12.
    { rewrite <-S_is_succ.
      apply Pairwise_union_classification; tauto. }
    set (ζ' := mkSet H12 : elts (S n)).
    replace (ζ : set) with (ζ' : set) by auto.
    rewrite -> H11.
    unfold permutation_succ_right_helper.
    destruct excluded_middle_informative.
    { simpl in e.
      subst.
      contradiction (no_quines n). }
    destruct Complement_classification, a.
    simpl.
    f_equal.
    apply function_record_injective;
      now rewrite -> ? functionify_domain, ? functionify_range,
      ? functionify_graph.
Qed.

Theorem bijection_empty_is_singleton : bijection_set 0%N 0%N = {∅, ∅}.
Proof.
  apply Extensionality.
  split; intros.
  - apply Singleton_classification.
    apply Specify_classification in H as [H H0].
    rewrite -> Empty_product_left, Powerset_classification in H.
    apply Extensionality.
    split; intros.
    + now apply H in H1.
    + contradiction (Empty_set_classification z0).
  - apply Singleton_classification in H.
    subst.
    apply Specify_classification.
    split; rewrite -> ? Empty_product_left; auto using Empty_set_in_powerset.
    exists empty_function.
    unfold empty_function, ssr_have.
    destruct constructive_indefinite_description; repeat split; intuition;
      rewrite ? Injective_classification ? Surjective_classification; intros.
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
  rewrite -> bijection_empty_is_singleton.
  apply singleton_card_1.
Qed.

Theorem bijections_of_one : bijection_set 1%N 1%N ~ 1%N.
Proof.
  unfold naturals.one.
  rewrite -> permutation_succ, bijections_of_empty_set.
  simpl.
  unfold succ.
  now rewrite Union_comm Union_empty singleton_products ? singleton_card_1.
Qed.

Theorem permutations_are_finite : ∀ n : N, finite (bijection_set n n).
Proof.
  intros n.
  induction n as [| n [m H]] using Induction.
  { exists 1%N.
    apply bijections_of_empty_set. }
  exists ((S n) * m)%N.
  symmetry.
  now rewrite -> permutation_succ, H, <-(card_of_natural (S n)),
  <-(card_of_natural m), <-natural_prod_card, <-card_equiv at 1;
    auto using finite_products_are_finite, naturals_are_finite.
Qed.

Theorem size_of_bijections_of_empty_set : size_of_bijections 0%N 0%N = 1%N.
Proof.
  apply natural_cardinality_uniqueness, cardinality_sym.
  rewrite <-bijections_of_empty_set.
  eauto using card_equiv, permutations_are_finite.
Qed.

Theorem size_of_bijections_of_one : size_of_bijections 1%N 1%N = 1%N.
Proof.
  unfold size_of_bijections.
  now rewrite -> bijections_of_one, card_of_natural.
Qed.

Theorem number_of_permutations_n : ∀ n, n! = permutations n.
Proof.
  intros n.
  induction n using Induction; unfold factorial, permutations in *.
  - rewrite -> prod_N_neg.
    + now rewrite -> size_of_bijections_of_empty_set.
    + apply naturals.lt_succ.
  - rewrite -> prod_N_succ, IHn.
    + rewrite /size_of_bijections permutation_succ.
      rewrite -> finite_products_card, card_of_natural, mul_comm;
        auto using naturals_are_finite, permutations_are_finite.
    + apply (succ_le _ n), zero_le.
Qed.

Theorem number_of_permutations :
  ∀ S (n : N), S ~ n → n! = size_of_bijections S S.
Proof.
  intros S n H.
  now rewrite -> H, number_of_permutations_n.
Qed.

Theorem binomials_are_finite : ∀ n k, finite (set_of_combinations n k).
Proof.
  eauto using Specify_subset, subsets_of_finites_are_finite,
  powerset_finite, naturals_are_finite.
Qed.

Theorem Pascal's_identity_bijection : ∀ n k,
    (1 ≤ k)%N → set_of_combinations n k ∪ set_of_combinations n (k-1) ~
                                    set_of_combinations (n+1) k.
Proof.
  intros n k H.
  symmetry.
  destruct (function_construction
              (set_of_combinations (n+1) k)
              (set_of_combinations n k ∪ set_of_combinations n (k-1))
              (λ x, If n ∈ x then x \ {n,n} else x)) as [f [H0 [H1 H2]]].
  { intros a H0.
    apply Specify_classification in H0 as [H0 H1].
    apply Powerset_classification in H0.
    destruct excluded_middle_informative;
      apply Pairwise_union_classification.
    - right.
      apply Specify_classification.
      split.
      + rewrite -> Powerset_classification.
        intros x H2.
        rewrite -> Complement_classification, Singleton_classification in H2.
        destruct H2 as [H2 H3].
        rewrite -> add_1_r, <-S_is_succ in H0.
        apply H0, Pairwise_union_classification in H2 as [H2 | H2]; auto.
        now rewrite -> Singleton_classification in H2.
      + replace a with ({n,n} ∪ (a \ {n,n})) in H1.
        2: { rewrite <-disjoint_union_complement, <-Union_subset.
             intros x H2.
             rewrite -> Singleton_classification in H2; congruence. }
        rewrite -> finite_union_cardinality, singleton_card in H1;
          eauto using disjoint_intersection_complement, singletons_are_finite,
          subsets_of_finites_are_finite, complement_subset, naturals_are_finite.
        now apply sub_spec in H1.
    - left.
      apply Specify_classification.
      split; auto.
      rewrite -> Powerset_classification.
      intros x H2.
      rewrite -> add_1_r, <-S_is_succ in H0.
      apply H0 in H2 as H3.
      apply Pairwise_union_classification in H3 as [H3 | H3]; auto.
      apply Singleton_classification in H3.
      now subst. }
  exists f.
  repeat split; auto.
  - rewrite -> Injective_classification.
    intros x y H3 H4 H5.
    rewrite -> ? H2 in H5; try congruence.
    repeat destruct excluded_middle_informative; auto.
    + apply Extensionality.
      split; intros H6; destruct (classic (z = n)) as [H7 | H7];
        try congruence.
      * eapply complement_subset.
        rewrite <-H5.
        now rewrite -> Complement_classification, Singleton_classification.
      * eapply complement_subset.
        rewrite -> H5.
        now rewrite -> Complement_classification, Singleton_classification.
    + unfold set_of_combinations in *.
      rewrite -> H0, Specify_classification in *.
      destruct H3 as [H3 H6], H4 as [H4 H7].
      rewrite -> Powerset_classification in *.
      rewrite <-H5 in H7.
      replace x with ({n,n} ∪ (x \ {n,n})) in H6.
      2: { rewrite <-disjoint_union_complement, <-Union_subset.
           intros z H8.
           rewrite -> Singleton_classification in H8; congruence. }
      rewrite -> finite_union_cardinality, singleton_card, H7,
      naturals.add_comm, add_1_r in H6;
          eauto using disjoint_intersection_complement, singletons_are_finite,
          subsets_of_finites_are_finite, complement_subset, naturals_are_finite.
      now contradiction (neq_succ k).
    + unfold set_of_combinations in *.
      rewrite -> H0, Specify_classification in *.
      destruct H3 as [H3 H6], H4 as [H4 H7].
      rewrite -> Powerset_classification in *.
      rewrite -> H5 in H6.
      replace y with ({n,n} ∪ (y \ {n,n})) in H7.
      2: { rewrite <-disjoint_union_complement, <-Union_subset.
           intros z H8.
           rewrite -> Singleton_classification in H8; congruence. }
      rewrite -> finite_union_cardinality, singleton_card, H6,
      naturals.add_comm, add_1_r in H7;
          eauto using disjoint_intersection_complement, singletons_are_finite,
          subsets_of_finites_are_finite, complement_subset, naturals_are_finite.
      now contradiction (neq_succ k).
  - rewrite -> Surjective_classification.
    intros y H3.
    rewrite -> H1 in H3.
    apply Pairwise_union_classification in H3 as [H3 | H3];
      apply Specify_classification in H3 as [H3 H4];
      apply Powerset_classification in H3.
    + exists y.
      assert (y ∈ domain f) as H5.
      { rewrite -> H0.
        apply Specify_classification.
        rewrite -> Powerset_classification.
        split; auto.
        intros z H5.
        apply H3 in H5.
        assert (n ⊂ n+1)%N.
        { apply le_is_subset.
          now exists 1%N. }
        auto. }
      split; auto.
      rewrite -> H2; try congruence.
      destruct excluded_middle_informative; auto.
      apply H3 in i.
      contradiction (no_quines n).
    + exists (y ∪ {n,n}).
      assert (y ∩ {n,n} = ∅) as H5.
      { apply Extensionality.
        split; intros H5; try contradiction (Empty_set_classification z).
        apply Pairwise_intersection_classification in H5 as [H5 H6].
        rewrite -> Singleton_classification in H6.
        subst.
        apply H3 in H5.
        contradiction (no_quines n). }
      assert (y ∪ {n,n} ∈ domain f) as H6.
      { rewrite -> H0.
        apply Specify_classification.
        rewrite -> Powerset_classification, add_1_r, <-S_is_succ.
        split.
        - intros z H6.
          apply Pairwise_union_classification.
          apply Pairwise_union_classification in H6 as [H6 | H6]; try tauto.
          left.
          auto.
        - rewrite -> finite_union_cardinality, H4, singleton_card,
          naturals.add_comm, sub_abab;
            eauto using singletons_are_finite,
            subsets_of_finites_are_finite, naturals_are_finite. }
      split; auto.
      rewrite -> H2; try congruence.
      destruct excluded_middle_informative.
      * rewrite -> complement_disjoint_union; auto.
      * contradiction n0.
        apply Pairwise_union_classification.
        right.
        now apply Singleton_classification.
Qed.

Theorem Pascal's_identity :
  ∀ n k, (1 ≤ k → binomial n k + binomial n (k-1) = binomial (n+1) k)%N.
Proof.
  intros n k H.
  unfold binomial.
  rewrite <-Pascal's_identity_bijection, finite_union_cardinality;
    auto using binomials_are_finite.
  apply Extensionality.
  split; intros H0; try contradiction (Empty_set_classification z).
  apply Pairwise_intersection_classification in H0 as [H0 H1].
  apply Specify_classification in H0 as [H0 H2].
  apply Specify_classification in H1 as [H1 H3].
  erewrite -> H2, <-sub_abab, (naturals.add_comm 1), add_1_r in H3 at 1; auto.
  now contradiction (neq_succ (k-1)).
Qed.

Theorem binomial_zero : ∀ n : N, binomial n 0 = 1%N.
Proof.
  move=> n.
  apply equivalence_to_card, cardinality_eq, Extensionality.
  split => [/Specify_classification [/Powerset_classification H
                                      /finite_empty ->]
           | /Pairwise_union_classification [/Empty_set_classification |
                                             /Singleton_classification ->]] //.
  - eauto using subsets_of_finites_are_finite, naturals_are_finite.
  - apply in_succ.
  - apply Specify_classification, conj, card_empty.
    apply Empty_set_in_powerset.
Qed.

Theorem binomial_full : ∀ n, binomial n n = 1%N.
Proof.
  move=> n.
  rewrite -(singleton_card n).
  apply equivalence_to_card, cardinality_sym.
  rewrite card_equiv_l; auto using singletons_are_finite.
  apply cardinality_eq , Extensionality.
  split => [/Singleton_classification -> |
            /Specify_classification [/Powerset_classification H H0]].
  - apply Specify_classification.
    auto using Set_in_powerset, card_of_natural.
  - apply Singleton_classification, Subset_equality_iff, conj; auto.
    apply Complement_subset, finite_empty;
      eauto using subsets_of_finites_are_finite,
      complement_subset, naturals_are_finite.
    rewrite complement_card ? H0 ? card_of_natural ? sub_diag;
      eauto using subsets_of_finites_are_finite, naturals_are_finite.
Qed.

Theorem combinations_overflow : ∀ n k, (n < k)%N → set_of_combinations n k = ∅.
Proof.
  intros n k H.
  apply Extensionality; split; intros H0;
    try now contradiction (Empty_set_classification z).
  apply Specify_classification in H0 as [H0 H1].
  apply Powerset_classification in H0.
  apply finite_subsets, naturals.le_not_gt in H0;
    eauto using naturals_are_finite, subsets_of_finites_are_finite.
  subst.
  now rewrite <-(card_of_natural n) in H.
Qed.

Theorem binomial_overflow : ∀ n k, (n < k)%N → binomial n k = 0%N.
Proof.
  intros n k H.
  unfold binomial.
  rewrite -> combinations_overflow, <-card_of_natural; auto.
Qed.

Theorem binomial_empty_set : ∀ k, k ≠ 0%N → binomial 0 k = 0%N.
Proof.
  move=> k /succ_0 [m ->].
  apply binomial_overflow, naturals.lt_succ.
Qed.

Lemma factorial_ne_0 : ∀ k, k! ≠ 0%N.
Proof.
  intros k H.
  induction k using Induction; unfold factorial in *.
  - rewrite -> prod_N_neg in H.
    + now contradiction (PA4 0).
    + apply naturals.succ_lt.
  - rewrite -> prod_N_succ in H.
    + apply naturals.cancellation_0_mul in H as [H | H]; auto.
      now contradiction (PA4 k).
    + apply (succ_le _ k), zero_le.
Qed.

Theorem zero_factorial : 0! = 1%N.
Proof.
  unfold factorial.
  rewrite -> prod_N_neg; auto; apply naturals.succ_lt.
Qed.

Theorem factorial_succ : ∀ n, S n! = (S n * n!)%N.
Proof.
  rewrite /factorial => n.
  rewrite prod_N_succ; auto using one_le_succ; ring.
Qed.

Theorem binomial_coefficient :
  ∀ n k, (k ≤ n)%N → (n! / (k! * (n - k)!))%Q = binomial n k.
Proof.
  induction n using Induction => k H.
  { have -> : k = 0%N by auto using naturals.le_antisymm, zero_le.
    rewrite sub_0_l ? zero_factorial binomial_zero -/integers.one
            integers.M3 -/rationals.one -[IZQ 1]/rationals.one //. }
  case (classic (k = 0%N)) => [-> | /succ_0 [m H0]].
  { rewrite sub_0_r zero_factorial -/integers.one integers.M3 binomial_zero
            inv_div -?[mul]/(rings.mul ℚ) ? (inv_r ℚ) ? IZQ_eq ? INZ_eq;
      auto using factorial_ne_0. }
  move: H0 IHn H -> =>
  IHn /(iffRL (succ_le m n)) /[dup] H /naturals.le_not_gt H0.
  rewrite -{3}add_1_r -Pascal's_identity; auto using one_le_succ.
  rewrite /naturals.one ? sub_succ sub_0_r.
  case (lt_trichotomy n m) => [H1 | [-> | /lt_le_succ H1]]; try tauto.
  { rewrite sub_diag zero_factorial binomial_overflow 1 ? integers.M1
            ? integers.M3 ? inv_div ? INZ_eq -?[mul]/(rings.mul ℚ)
            ? (inv_r ℚ) ? IZQ_eq ? INZ_eq ? add_0_l ? binomial_full;
      auto using factorial_ne_0, naturals.succ_lt. }
  rewrite -INZ_add -IZQ_add -? IHn ? factorial_succ //.
  (have: n ≠ 0%N by
      eapply nonzero_lt, naturals.lt_0_le_1, naturals.le_trans;
   eauto using one_le_succ) => /succ_0 [n' H2].
  move: H2 sub_succ H1 -> => -> /(iffRL (succ_le m n')) H1.
  rewrite ? sub_succ_l ? (factorial_succ (n' - m)) //.
  have H2: ((S m * m!)%N * (S (n' - m) * (n' - m)!)%N)%Z ≠ 0%Z.
  { rewrite -IZQ_eq -? INZ_mul -? IZQ_mul.
    repeat apply (ne0_cancellation (integral_domain_from_field ℚ));
      rewrite IZQ_eq INZ_eq; auto using PA4, neq_sym, factorial_ne_0. }
  apply (cancellation_mul_r (integral_domain_from_field ℚ)
                            ((S m * m!)%N *(S (n' - m) * (n' - m)!))).
  { contradict H2.
    rewrite -IZQ_eq -? IZQ_mul -? INZ_mul INZ_mul -IZQ_mul H2 //. }
  rewrite inv_div // /= -M2 ? IZQ_mul ? INZ_mul inv_l
  -INZ_mul ? IZQ_eq // D1 ? inv_div -? IZQ_mul -? INZ_mul -? IZQ_mul;
    repeat apply (ne0_cancellation ℤ_ID);
    rewrite ? INZ_eq; auto using eq_sym, PA4, factorial_ne_0.
  have -> : S n'! * (S m * m! * (n' - m)!)^-1 *
            (S m * m! * (S (n' - m) * (n' - m)!))
            = S n'! * S (n' - m) * ((S m * m! * (n' - m)!)^-1 *
                                    (S m * m! * (n' - m)!)) by ring.
  have -> : S n'! * (m! * (S (n' - m) * (n' - m)!))^-1 *
            (S m * m! * (S (n' - m) * (n' - m)!))
            = S n'! * S m * ((m! * (S (n' - m) * (n' - m)!))^-1 *
                             (m! * (S (n' - m) * (n' - m)!))) by ring.
  rewrite ? inv_l; try by rewrite ? IZQ_mul IZQ_eq;
    repeat apply (ne0_cancellation ℤ_ID);
    rewrite ? INZ_eq; auto using eq_sym, PA4, factorial_ne_0.
  rewrite -? (M1 1) ? M3 ? IZQ_mul IZQ_add IZQ_eq ? INZ_mul INZ_add
          INZ_eq -naturals.mul_distr_l -? add_1_r.
  have -> : (n' - m + 1 + (m + 1) = m + (n' - m) + 1 + 1)%N by ring.
  rewrite sub_abab // mul_comm //.
Qed.

Theorem one_factorial : 1! = 1%N.
Proof.
  apply prod_N_0.
Qed.

Theorem binomial_one : binomial 1 1 = 1%N.
Proof.
  rewrite -INZ_eq -IZQ_eq -binomial_coefficient; auto using naturals.le_refl.
  rewrite sub_diag zero_factorial one_factorial INZ_mul naturals.mul_1_r
          inv_div 1 ? M1 ? inv_l // ? IZQ_eq; apply integers.zero_ne_1.
Qed.

Theorem sum_card_0 : ∀ n X f,
    finite X → (∀ k, 0 ≤ k ≤ n → f k ⊂ X)%N →
    (∀ x, x ∈ X ↔ exists ! k : N, 0 ≤ k ≤ n ∧ x ∈ f k)%N →
    sum ℤ (λ k, # (f k) : Z) 0 n = (# X : Z).
Proof.
  induction n using Induction; intros X f H H0 H1.
  - rewrite -> sum_0.
    repeat f_equal.
    apply Extensionality.
    split; intros H2.
    + apply H1.
      exists 0%N.
      repeat split; eauto using naturals.le_refl.
      intros x' [[H3 H4] H5].
      auto using naturals.le_antisymm.
    + apply H1 in H2 as [y [[[H2 H3] H4] H5]].
      replace 0%N with y by now apply naturals.le_antisymm.
      auto.
  - rewrite -> sum_succ; auto using zero_le.
    simpl.
    rewrite -> (IHn (X \ (f (S n))) f);
      eauto using subsets_of_finites_are_finite, complement_subset,
      subsets_of_finites_are_finite.
    + rewrite -> INZ_add, <-finite_union_cardinality;
        eauto using subsets_of_finites_are_finite, complement_subset,
        subsets_of_finites_are_finite, zero_le, naturals.le_refl.
      * rewrite -> Union_comm, <-disjoint_union_complement.
        apply f_equal, f_equal, Union_subset, H0.
        split; eauto using zero_le, naturals.le_refl.
      * apply NNPP.
        intros H2.
        apply Nonempty_classification in H2 as [x H2].
        apply Pairwise_intersection_classification in H2 as [H2 H3].
        now apply Complement_classification in H2 as [H2 H4].
    + intros k [H2 H3] x H4.
      apply Complement_classification.
      split.
      * apply H0 in H4; auto.
        split; auto.
        eapply naturals.le_lt_trans; eauto using naturals.succ_lt.
      * intros H5.
        assert (x ∈ X).
        { apply H0 in H4; auto.
          split; auto.
          eapply naturals.le_lt_trans; eauto using naturals.succ_lt. }
        apply H1 in H6 as [y [[[H6 H7] H8] H9]].
        assert (y = S n).
        { apply H9.
          repeat split; auto using zero_le, naturals.le_refl. }
        assert (y = k).
        { apply H9.
          repeat split; auto.
          eapply naturals.le_lt_trans; eauto using naturals.succ_lt. }
        subst.
        rewrite -> naturals.le_not_gt in H3.
        contradict H3.
        auto using naturals.succ_lt.
    + split; intros H2.
      * apply Complement_classification in H2 as [H2 H3].
        apply H1 in H2 as [y [[[H2 H4] H5] H6]].
        exists y.
        repeat split; auto.
        -- rewrite -> naturals.le_not_gt.
           intros H7.
           apply squeeze_upper in H4; auto.
           now subst.
        -- intros x' [[H7 H8] H9].
           apply H6.
           repeat split; auto.
           eapply naturals.le_lt_trans; eauto using naturals.succ_lt.
      * destruct H2 as [y [[[H2 H3] H4] H5]].
        apply Complement_classification.
        assert (x ∈ X).
        { apply H0 in H4; auto.
          split; auto.
          eapply naturals.le_lt_trans; eauto using naturals.succ_lt. }
        split; auto.
        intros H7.
        apply H1 in H6 as [z [[[H6 H8] H9] H10]].
        assert (z = S n).
        { apply H10.
          repeat split; auto using zero_le, naturals.le_refl. }
        assert (z = y).
        { apply H10.
          repeat split; auto.
          eapply naturals.le_lt_trans; eauto using naturals.succ_lt. }
        subst.
        rewrite -> naturals.le_not_gt in H3.
        contradict H3.
        auto using naturals.succ_lt.
Qed.

Theorem sum_card : ∀ a b X f,
    finite X → (∀ k, a ≤ k ≤ b → f k ⊂ X)%N →
    (∀ x, x ∈ X ↔ exists ! k : N, a ≤ k ≤ b ∧ x ∈ f k)%N →
    sum ℤ (λ k, # (f k) : Z) a b = (# X : Z).
Proof.
  intros a b X f H H0 H1.
  destruct (classic (a ≤ b)%N) as [[c H2] | H2]; subst.
  - unfold sum.
    rewrite -> iterate_shift.
    apply sum_card_0; auto.
    + intros k [H2 H3].
      apply H0.
      split.
      * rewrite <-(add_0_l a) at 1.
        now apply O1_le.
      * rewrite -> (add_comm a).
        now apply O1_le.
    + split; intros H2.
      * apply H1 in H2 as [y [[[H2 H3] H4] H5]].
        exists (y-a)%N.
        repeat split; try apply zero_le.
        -- eapply O1_le_iff.
           rewrite -> (add_comm c).
           eapply naturals.le_trans; eauto.
           rewrite -> add_comm, sub_abab; auto using naturals.le_refl.
        -- rewrite -> add_comm, sub_abab; auto using naturals.le_refl.
        -- intros x' [H6 H7].
           replace y with (x'+a)%N; try now rewrite -> sub_abba.
           apply eq_sym, H5.
           repeat split; auto.
           ++ rewrite <-(add_0_l a) at 1.
              now apply O1_le.
           ++ rewrite -> (add_comm a).
              now apply O1_le.
      * destruct H2 as [y [[[H2 H3] H4] H5]].
        apply (H0 (y+a)%N); auto.
        repeat split; auto.
        -- rewrite <-(add_0_l a) at 1.
           now apply O1_le.
        -- rewrite -> (add_comm a).
           now apply O1_le.
  - rewrite <-naturals.lt_not_ge, sum_neg, naturals.lt_not_ge in *; auto.
    apply INZ_eq, eq_sym.
    replace X with ∅; auto using card_empty.
    apply Extensionality.
    split; intros H3; try contradiction (Empty_set_classification z).
    apply H1 in H3 as [y [[[H3 H4] H5] H6]].
    contradict H2.
    eauto using naturals.le_trans.
Qed.
