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

Section Combinations_orbit_stabilizer.

  Variable n k : N.
  Hypothesis nontriviality : k ⊂ n.

  Definition φ (f : elts (bijection_set n n)) :=
    {x in n | (functionify n n f x) ∈ k}.

  Definition combinations_proj_helper : set → set.
  Proof.
    intros f.
    destruct (excluded_middle_informative (f ∈ bijection_set n n)).
    - exact (φ (mkSet i)).
    - exact ∅.
  Defined.

  Theorem combinations_proj_construction : ∀ f,
      f ∈ bijection_set n n →
      combinations_proj_helper f ∈ set_of_combinations n k.
  Proof.
    intros f H.
    unfold combinations_proj_helper.
    destruct excluded_middle_informative; try tauto.
    set (η := mkSet i : elts (bijection_set n n)).
    replace f with (η : set) in * by auto.
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
      + rewrite -> Injective_classification in *.
        intros x y H5 H6 H7.
        rewrite -> ? H2 in H7; try congruence.
        apply H3; rewrite -> ? functionify_domain, H0 in *; try congruence.
        * apply Specify_classification in H5; tauto.
        * apply Specify_classification in H6; tauto.
      + rewrite -> Surjective_classification in *.
        intros y H5.
        assert (y ∈ n) as H6 by (apply nontriviality; congruence).
        rewrite <-(functionify_range n n η) in H6.
        apply H4 in H6 as [x [H6 H7]].
        rewrite -> functionify_domain in H6.
        exists x.
        split.
        * rewrite -> H0.
          apply Specify_classification.
          split; auto.
          rewrite -> H7.
          congruence.
        * rewrite -> H2; try congruence.
          apply Specify_classification.
          split; auto.
          rewrite -> H7.
          congruence.
  Qed.

  Definition combinations_proj : function.
  Proof.
    destruct
      (constructive_indefinite_description
         (function_construction
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

  Theorem cp_action : ∀ f, φ f = combinations_proj f.
  Proof.
    intros [f F].
    unfold combinations_proj.
    destruct constructive_indefinite_description.
    destruct a as [H [H0 H1]].
    rewrite -> H1; auto.
    unfold combinations_proj_helper.
    destruct excluded_middle_informative; try tauto.
    simpl in *.
    now replace i with F by now apply proof_irrelevance.
  Qed.

  Theorem combinations_proj_surj : surjective combinations_proj.
  Proof.
    rewrite -> Surjective_classification.
    intros y H.
    rewrite -> cp_range in H.
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
      rewrite -> ? finite_union_cardinality in H5;
        eauto using naturals_are_finite, subsets_of_finites_are_finite,
        disjoint_intersection_complement, complement_subset.
      apply equinumerous_cardinality in H4.
      rewrite -> H4 in H5.
      apply naturals.cancellation_add in H5.
      now apply finite_cardinality_equinumerous in H5;
        eauto using naturals_are_finite, subsets_of_finites_are_finite,
        disjoint_intersection_complement, complement_subset. }
    pose proof H5 as [g [H6 [H7 [H8 H9]]]].
    destruct (function_construction n n (λ x, If x ∈ y then f x else g x))
      as [h [H10 [H11 H12]]].
    { intros a H10.
      destruct excluded_middle_informative.
      - apply nontriviality.
        rewrite <-H1.
        apply function_maps_domain_to_range.
        congruence.
      - assert (g a ∈ range g) as H11.
        { apply function_maps_domain_to_range.
          rewrite -> H6.
          now apply Specify_classification. }
        rewrite -> H7 in H11.
        apply Complement_classification in H11.
        tauto. }
    exists (graph h).
    assert (graph h ∈ domain combinations_proj).
    { rewrite -> cp_domain.
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
        + rewrite -> Injective_classification in *.
          intros x1 x2 H13 H14 H15.
          rewrite -> ? H12 in H15; try congruence.
          repeat destruct excluded_middle_informative.
          * apply H2; congruence.
          * assert (g x2 ∈ n \ k).
            { rewrite <-H7.
              apply function_maps_domain_to_range.
              rewrite -> H6.
              apply Complement_classification; split; congruence. }
            apply Complement_classification in H16 as [H16 H17].
            contradict H17.
            rewrite <-H15, <-H1.
            apply function_maps_domain_to_range.
            congruence.
          * assert (g x1 ∈ n \ k).
            { rewrite <-H7.
              apply function_maps_domain_to_range.
              rewrite -> H6.
              apply Complement_classification; split; congruence. }
            apply Complement_classification in H16 as [H16 H17].
            contradict H17.
            rewrite -> H15, <-H1.
            apply function_maps_domain_to_range.
            congruence.
          * apply H8; try congruence; rewrite -> H6;
              apply Complement_classification; split; congruence.
        + rewrite -> Surjective_classification in *.
          intros z H13.
          rewrite -> H11 in H13.
          destruct (excluded_middle_informative (z ∈ k)).
          * rewrite <-H1 in i.
            apply H3 in i as [x [H14 H15]].
            exists x.
            rewrite -> H0 in H14.
            apply H in H14 as H16.
            rewrite -> H12; auto.
            destruct excluded_middle_informative; split; congruence.
          * destruct (H9 z) as [x [H14 H15]].
            { rewrite -> H7.
              now apply Specify_classification. }
            exists x.
            rewrite -> H6 in H14.
            apply Complement_classification in H14 as [H14 H16].
            rewrite -> H12; auto.
            destruct excluded_middle_informative; split; congruence. }
    split; auto.
    rewrite -> cp_domain in H13.
    replace (graph h)
      with ((mkSet H13 : elts (bijection_set n n)) : set) by auto.
    rewrite <-cp_action.
    apply Extensionality.
    split; intros H17.
    + apply Specify_classification in H17 as [H17 H18].
      unfold functionify in *.
      destruct Specify_classification, a,
      constructive_indefinite_description as [h' [H19 [H20 [H21 H22]]]].
      apply function_record_injective in H21; try congruence.
      subst.
      rewrite -> H12 in H18; auto.
      destruct excluded_middle_informative; try tauto.
      assert (g z ∈ n \ k) as H0.
      { rewrite <-H7.
        apply function_maps_domain_to_range.
        rewrite -> H6.
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
      rewrite -> H12; auto.
      destruct excluded_middle_informative; try tauto.
      rewrite <-H1.
      now apply function_maps_domain_to_range.
  Qed.

  Variable y : elts (set_of_combinations n k).

  Definition h : elts (inverse_image_of_element combinations_proj y).
  Proof.
    pose proof (elts_in_set y) as H; simpl in *.
    pose proof combinations_proj_surj as H0.
    rewrite <-? cp_range, ? Surjective_classification in *.
    apply H0 in H.
    destruct (constructive_indefinite_description H) as [h].
    assert (h ∈ inverse_image_of_element combinations_proj y) by
        now apply Specify_classification.
    exact (mkSet H1).
  Defined.

  Theorem image_of_comb_proj : ∀ x (f : elts (bijection_set n n)),
      (combinations_proj f = y) → x ∈ n → x ∈ y ↔ (functionify n n f) x ∈ k.
  Proof.
    split; intros H1.
    - rewrite <-H, <-cp_action in H1.
      now apply Specify_classification in H1 as [H1 H5].
    - rewrite <-H, <-cp_action.
      apply Specify_classification.
      split; auto.
  Qed.

  Lemma combinations_left_helper_k_construction_1 :
    ∀ (f1 f2 : elts (bijection_set n n)) (x : elts k),
      combinations_proj f1 = y →
      combinations_proj f2 = y →
      (functionify n n f1) (inverse (functionify n n f2) x) ∈ k.
  Proof.
    intros f1 f2 x H H0.
    unfold inverse.
    destruct excluded_middle_informative.
    2: { contradict n0.
         apply functionify_bijective. }
    destruct b; simpl.
    destruct constructive_indefinite_description as [f2_inv].
    destruct a as [H1 [H2 H3]].
    destruct f1 as [f1' H4].
    unfold functionify.
    destruct Specify_classification, a,
    constructive_indefinite_description as [f1''].
    destruct a0 as [H5 [H6 [H7 H8]]].
    assert (f2_inv x ∈ y) as H9.
    { rewrite -> image_of_comb_proj, H3; auto using elts_in_set.
      - rewrite -> functionify_range.
        eauto using elts_in_set.
      - rewrite <-(functionify_domain _ _ f2), <-H2.
        apply function_maps_domain_to_range.
        rewrite -> H1, functionify_range.
        eauto using elts_in_set. }
    replace f1' with ((mkSet H4 : elts (bijection_set n n)) : set)
      in * by auto.
    rewrite <-functionify_graph in H7.
    apply function_record_injective in H7; subst;
      rewrite -> ? functionify_domain, ? functionify_range; try congruence.
    apply image_of_comb_proj; auto.
    rewrite <-(functionify_domain _ _ f2), <-H2.
    apply function_maps_domain_to_range.
    rewrite -> H1, functionify_range.
    eauto using elts_in_set.
  Qed.

  Definition combinations_left_helper_k :
    elts (inverse_image_of_element combinations_proj y) →
    elts k → elts k.
  Proof.
    intros h0 x.
    pose proof (elts_in_set h) as H; simpl in *.
    pose proof (elts_in_set h0) as H0; simpl in *.
    apply Specify_classification in H as [H H1].
    rewrite -> cp_domain in H.
    apply Specify_classification in H0 as [H0 H2].
    rewrite -> cp_domain in H0.
    exact (mkSet (combinations_left_helper_k_construction_1
                    (mkSet H) (mkSet H0) x H1 H2)).
  Defined.

  Theorem image_of_comb_proj_2 : ∀ x (f : elts (bijection_set n n)),
      (combinations_proj f = y)
      → x ∈ n → x ∈ n \ y ↔ (functionify n n f) x ∈ n \ k.
  Proof.
    split; intros H1.
    - rewrite <-H, <-cp_action in H1.
      apply Complement_classification in H1 as [H1 H5].
      apply Complement_classification.
      split.
      + rewrite <-(functionify_range _ _ f).
        apply function_maps_domain_to_range.
        now rewrite -> functionify_domain.
      + contradict H5.
        now apply Specify_classification.
    - rewrite <-H, <-cp_action.
      unfold φ.
      rewrite -> Complement_classification, Specify_classification in *.
      split; auto; tauto.
  Qed.

  Lemma combinations_left_helper_k_construction_2 :
    ∀ (f1 f2 : elts (bijection_set n n)) (x : elts (n \ k)),
      combinations_proj f1 = y →
      combinations_proj f2 = y →
      (functionify n n f1) (inverse (functionify n n f2) x) ∈ (n \ k).
  Proof.
    intros f1 f2 x H H0.
    unfold inverse.
    destruct excluded_middle_informative.
    2: { contradict n0.
         apply functionify_bijective. }
    destruct b; simpl.
    destruct constructive_indefinite_description as [f2_inv].
    destruct a as [H1 [H2 H3]].
    destruct f1 as [f1' H4].
    unfold functionify.
    destruct Specify_classification, a,
    constructive_indefinite_description as [f1''].
    destruct a0 as [H5 [H6 [H7 H8]]].
    assert (f2_inv x ∈ n \ y) as H9.
    { rewrite -> image_of_comb_proj_2, H3; auto using elts_in_set.
      - rewrite -> functionify_range.
        apply (complement_subset k n); auto using elts_in_set.
      - rewrite <-(functionify_domain _ _ f2), <-H2.
        apply function_maps_domain_to_range.
        rewrite -> H1, functionify_range.
        apply (complement_subset k n), elts_in_set. }
    replace f1' with ((mkSet H4 : elts (bijection_set n n)) : set)
      in * by auto.
    rewrite <-functionify_graph in H7.
    apply function_record_injective in H7; subst;
      rewrite -> ? functionify_domain, ? functionify_range; try congruence.
    apply image_of_comb_proj_2; auto.
    rewrite <-(functionify_domain _ _ f2), <-H2.
    apply function_maps_domain_to_range.
    rewrite -> H1, functionify_range.
    apply (complement_subset k n), elts_in_set.
  Qed.

  Definition combinations_left_helper_n_minus_k :
    elts (inverse_image_of_element combinations_proj y) →
    elts (n \ k) → elts (n \ k).
  Proof.
    intros h0 x.
    pose proof (elts_in_set h) as H; simpl in *.
    pose proof (elts_in_set h0) as H0; simpl in *.
    apply Specify_classification in H as [H H1].
    rewrite -> cp_domain in H.
    apply Specify_classification in H0 as [H0 H2].
    rewrite -> cp_domain in H0.
    exact (mkSet (combinations_left_helper_k_construction_2
                    (mkSet H) (mkSet H0) x H1 H2)).
  Defined.

  Lemma combinations_left_helper_k_bijective : ∀ h',
      bijective (sets.functionify (combinations_left_helper_k h')).
  Proof.
    intros h'.
    unfold sets.functionify.
    destruct constructive_indefinite_description as [h'' [H [H0 H1]]].
    apply finite_set_injection_is_bijection.
    - rewrite -> H.
      apply naturals_are_finite.
    - now rewrite -> H, H0.
    - rewrite -> Injective_classification.
      intros x1 x2 H2 H3 H4.
      rewrite -> ? H, ? H0 in *.
      set (ξ1 := mkSet H2 : elts k).
      set (ξ2 := mkSet H3 : elts k).
      replace x1 with (ξ1 : set) in * by auto.
      replace x2 with (ξ2 : set) in * by auto.
      rewrite -> ? H1 in H4.
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
      rewrite -> Injective_classification in *.
      apply H8 in H4; try apply H14 in H4; auto.
      + rewrite -> inverse_domain; auto.
        rewrite -> H11; auto.
      + rewrite -> inverse_domain; auto.
        rewrite -> H11; auto.
      + rewrite -> H5, <-H10, <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite -> inverse_domain; auto.
        rewrite -> H11; auto.
      + rewrite -> H5, <-H10, <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite -> inverse_domain; auto.
        rewrite -> H11; auto.
  Qed.

  Lemma combinations_left_helper_n_minus_k_bijective : ∀ h',
      bijective (sets.functionify (combinations_left_helper_n_minus_k h')).
  Proof.
    intros h'.
    unfold sets.functionify.
    destruct constructive_indefinite_description as [h'' [H [H0 H1]]].
    apply finite_set_injection_is_bijection.
    - rewrite -> H.
      eauto using subsets_of_finites_are_finite,
      naturals_are_finite, complement_subset.
    - now rewrite -> H, H0.
    - rewrite -> Injective_classification.
      intros x1 x2 H2 H3 H4.
      rewrite -> ? H, ? H0 in *.
      set (ξ1 := mkSet H2 : elts (n \ k)).
      set (ξ2 := mkSet H3 : elts (n \ k)).
      replace x1 with (ξ1 : set) in * by auto.
      replace x2 with (ξ2 : set) in * by auto.
      rewrite -> ? H1 in H4.
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
      rewrite -> Injective_classification in *.
      apply H8 in H4; try apply H14 in H4; auto.
      + rewrite -> inverse_domain; auto.
        rewrite -> H11; auto.
        eapply complement_subset; eauto.
      + rewrite -> inverse_domain; auto.
        rewrite -> H11; auto.
        eapply complement_subset; eauto.
      + rewrite -> H5, <-H10, <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite -> inverse_domain; auto.
        rewrite -> H11; auto.
        eapply complement_subset; eauto.
      + rewrite -> H5, <-H10, <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite -> inverse_domain; auto.
        rewrite -> H11; auto.
        eapply complement_subset; eauto.
  Qed.

  Theorem combinations_left_construction : ∀ h0,
      (graph (sets.functionify (combinations_left_helper_k h0)),
       graph (sets.functionify (combinations_left_helper_n_minus_k h0)))
        ∈ bijection_set k k × bijection_set (n \ k) (n \ k).
  Proof.
    intros h0.
    apply Product_classification.
    exists (graph (sets.functionify (combinations_left_helper_k h0))),
    (graph (sets.functionify (combinations_left_helper_n_minus_k h0))).
    repeat split; auto.
    - apply Specify_classification.
      split.
      + pose proof func_hyp
             (sets.functionify (combinations_left_helper_k h0)) as [H].
        now rewrite -> sets.functionify_domain, sets.functionify_range,
        <-Powerset_classification in H.
      + exists (sets.functionify (combinations_left_helper_k h0)).
        rewrite -> sets.functionify_domain, sets.functionify_range.
        auto using combinations_left_helper_k_bijective.
    - apply Specify_classification.
      split.
      + pose proof func_hyp
             (sets.functionify (combinations_left_helper_n_minus_k h0)) as [H].
        now rewrite -> sets.functionify_domain, sets.functionify_range,
        <-Powerset_classification in H.
      + exists (sets.functionify (combinations_left_helper_n_minus_k h0)).
        rewrite -> sets.functionify_domain, sets.functionify_range.
        auto using combinations_left_helper_n_minus_k_bijective.
  Qed.

  Definition combinations_left :
    elts (inverse_image_of_element combinations_proj y) →
    elts (bijection_set k k × bijection_set (n \ k) (n \ k)).
  Proof.
    intros h0.
    exact (mkSet (combinations_left_construction h0)).
  Defined.

  Definition comb_inverse_image_incl :
    elts (inverse_image_of_element combinations_proj y) → function.
  Proof.
    intros [f F].
    apply Inverse_image_classification_left in F as H;
      apply Inverse_image_classification_domain in F as H0;
      try (rewrite -> cp_range; auto using elts_in_set).
    rewrite -> cp_domain in H0.
    exact (functionify n n (mkSet H0)).
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

  Theorem cii_graph : ∀ f, graph (comb_inverse_image_incl f) = f.
  Proof.
    intros [f F].
    simpl.
    destruct Specify_classification, a, constructive_indefinite_description.
    tauto.
  Qed.

  Theorem cii_bijection :
    ∀ f, graph (comb_inverse_image_incl f) ∈ bijection_set n n.
  Proof.
    intros [f F].
    pose proof F as H.
    apply Inverse_image_classification_domain in H.
    - rewrite -> cii_graph.
      simpl.
      now rewrite <-cp_domain.
    - rewrite -> cp_range.
      auto using elts_in_set.
  Qed.

  Theorem cii_bijective : ∀ f, bijective (comb_inverse_image_incl f).
  Proof.
    intros f.
    pose proof cii_bijection f as H.
    apply Specify_classification in H as [H [f' [H0 [H1 [H2 H3]]]]].
    apply function_record_injective in H2;
      rewrite -> ? cii_domain, ? cii_range; congruence.
  Qed.

  Lemma combinations_right_helper_0 :
    ∀ x, x ∈ n → x ∈ y ↔ comb_inverse_image_incl h x ∈ k.
  Proof.
    pose proof elts_in_set h as H.
    apply Inverse_image_classification_left in H as H1;
      apply Inverse_image_classification_domain in H as H0;
      try (rewrite -> cp_range; auto using elts_in_set).
    rewrite -> cp_domain in H0.
    replace (h : set)
      with ((mkSet H0 : elts (bijection_set n n)) : set) in H1 by auto.
    rewrite <-cp_action in H1.
    split; intros H6; destruct h; simpl in *.
    - destruct Specify_classification, a,
      constructive_indefinite_description as [h'].
      clear a i i0 e.
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
      clear a i i0 e.
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
      inverse (comb_inverse_image_incl h) (functionify k k z1 x) ∈ y.
  Proof.
    intros x z1 H.
    apply combinations_right_helper_0.
    { rewrite <-(cii_domain h), <-inverse_range; auto using cii_bijective.
      apply function_maps_domain_to_range.
      rewrite -> inverse_domain, cii_range; auto using cii_bijective.
      apply nontriviality.
      rewrite <-(functionify_range _ _ z1).
      apply function_maps_domain_to_range.
      now rewrite -> functionify_domain. }
    rewrite -> right_inverse; auto using cii_bijective.
    { rewrite <-(functionify_range _ _ z1).
      apply function_maps_domain_to_range.
      now rewrite -> functionify_domain. }
    rewrite -> inverse_domain; auto using cii_bijective.
    rewrite -> cii_range.
    apply nontriviality.
    rewrite <-(functionify_range _ _ z1).
    apply function_maps_domain_to_range.
    now rewrite -> functionify_domain.
  Qed.

  Lemma combinations_right_helper_l :
    ∀ x (z1 : elts (bijection_set k k)),
      x ∈ k →
      inverse (comb_inverse_image_incl h) (functionify k k z1 x) ∈ n.
  Proof.
    intros x z1 H.
    pose proof (elts_in_set y) as H0; simpl in *.
    apply Specify_classification in H0 as [H0 H1].
    apply Powerset_classification in H0.
    now apply H0, combinations_right_helper_l_1.
  Qed.

  Lemma combinations_right_helper_r_1 :
    ∀ x (z2 : elts (bijection_set (n \ k) (n \ k))),
      x ∈ n \ k →
      inverse (comb_inverse_image_incl h)
              (functionify (n \ k) (n \ k) z2 x) ∈ n \ y.
  Proof.
    intros x z2 H.
    apply Complement_classification in H as [H H0].
    apply Complement_classification.
    assert ((inverse (comb_inverse_image_incl h))
              ((functionify (n \ k) (n \ k) z2) x) ∈ n) as H1.
    { rewrite <-(cii_domain h), <-inverse_range; auto using cii_bijective.
      apply function_maps_domain_to_range.
      rewrite -> inverse_domain, cii_range; auto using cii_bijective.
      apply (complement_subset k n).
      rewrite <-(functionify_range _ _ z2).
      apply function_maps_domain_to_range.
      rewrite -> functionify_domain.
      now apply Complement_classification. }
    split; auto.
    intros H2.
    apply combinations_right_helper_0 in H2; auto.
    rewrite -> right_inverse in H2; auto using cii_bijective.
    2: { rewrite -> inverse_domain; auto using cii_bijective.
         rewrite -> cii_range.
         apply (complement_subset k n).
         rewrite <-(functionify_range _ _ z2).
         apply function_maps_domain_to_range.
         rewrite -> functionify_domain.
         now apply Complement_classification. }
    assert ((functionify (n \ k) (n \ k) z2) x ∈ n \ k) as H3.
    { rewrite <-(functionify_range _ _ z2).
      apply function_maps_domain_to_range.
      rewrite -> functionify_domain.
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
    now apply (complement_subset y n), combinations_right_helper_r_1.
  Qed.

  Definition combinations_right_helper :
    elts (bijection_set k k) → elts (bijection_set (n \ k) (n \ k)) →
    elts n → elts n.
  Proof.
    intros z1 z2 x.
    destruct (excluded_middle_informative (x ∈ k)).
    - exact (mkSet (combinations_right_helper_l x z1 i)).
    - assert (x ∈ n \ k) as H.
      { apply Complement_classification.
        split; auto using elts_in_set. }
      exact (mkSet (combinations_right_helper_r x z2 H)).
  Defined.

  Theorem combinations_right_helper_bijective : ∀ z1 z2,
      bijective (sets.functionify (combinations_right_helper z1 z2)).
  Proof.
    intros z1 z2.
    apply finite_set_injection_is_bijection.
    - rewrite -> sets.functionify_domain.
      apply naturals_are_finite.
    - now rewrite -> sets.functionify_domain, sets.functionify_range.
    - pose proof (cii_bijective h) as H.
      apply inverse_bijective in H as [H H0].
      rewrite -> Injective_classification in *.
      intros x1 x2 H1 H2 H3.
      rewrite -> @sets.functionify_domain in *.
      unfold sets.functionify in H3.
      destruct constructive_indefinite_description as [g].
      destruct a as [H4 [H5 H6]].
      set (ξ1 := mkSet H1 : elts n).
      set (ξ2 := mkSet H2 : elts n).
      replace x1 with (ξ1 : set) in * by auto.
      replace x2 with (ξ2 : set) in * by auto.
      rewrite -> ? H6 in H3.
      unfold combinations_right_helper in H3.
      repeat destruct excluded_middle_informative; simpl in *.
      + apply H in H3.
        2: { rewrite -> inverse_domain; auto using cii_bijective.
             rewrite -> cii_range.
             apply nontriviality.
             rewrite <-(functionify_range _ _ z1).
             apply function_maps_domain_to_range.
             now rewrite -> functionify_domain. }
        2: { rewrite -> inverse_domain; auto using cii_bijective.
             rewrite -> cii_range.
             apply nontriviality.
             rewrite <-(functionify_range _ _ z1).
             apply function_maps_domain_to_range.
             now rewrite -> functionify_domain. }
        pose proof functionify_bijective _ _ z1 as [H7 H8].
        rewrite -> Injective_classification in H7.
        now apply H7 in H3; try now rewrite -> functionify_domain.
      + assert (inverse (comb_inverse_image_incl h) (functionify _ _ z2 x2) ∈ _)
          as H7 by now apply combinations_right_helper_r_1,
                   Complement_classification.
        rewrite <-H3, Complement_classification in H7.
        destruct H7 as [H7 H8].
        contradiction H8.
        auto using combinations_right_helper_l_1.
      + assert (inverse (comb_inverse_image_incl h) (functionify _ _ z2 x1) ∈ _)
          as H7 by now apply combinations_right_helper_r_1,
                   Complement_classification.
        rewrite -> H3, Complement_classification in H7.
        destruct H7 as [H7 H8].
        contradiction H8.
        auto using combinations_right_helper_l_1.
      + apply H in H3.
        2: { rewrite -> inverse_domain; auto using cii_bijective.
             rewrite -> cii_range.
             apply (complement_subset k n).
             rewrite <-(functionify_range _ _ z2).
             apply function_maps_domain_to_range.
             now rewrite -> functionify_domain, Complement_classification. }
        2: { rewrite -> inverse_domain; auto using cii_bijective.
             rewrite -> cii_range.
             apply (complement_subset k n).
             rewrite <-(functionify_range _ _ z2).
             apply function_maps_domain_to_range.
             now rewrite -> functionify_domain, Complement_classification. }
        pose proof functionify_bijective _ _ z2 as [H7 H8].
        rewrite -> Injective_classification in H7.
        now apply H7 in H3;
          try now rewrite -> functionify_domain, Complement_classification.
  Qed.

  Theorem combinations_right_construction_proto : ∀ z1 z2,
      graph (inverse (sets.functionify (combinations_right_helper z1 z2)))
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
      (inverse (sets.functionify (combinations_right_helper z1 z2)) x1).
      repeat split.
      + rewrite -> inverse_domain, sets.functionify_range in H;
          auto using combinations_right_helper_bijective.
      + rewrite <-(sets.functionify_domain (combinations_right_helper z1 z2)),
        <-inverse_range; auto using combinations_right_helper_bijective.
        now apply function_maps_domain_to_range. }
    exists (inverse (sets.functionify (combinations_right_helper z1 z2))).
    rewrite -> inverse_domain, inverse_range, sets.functionify_domain,
    sets.functionify_range; intuition;
      auto using combinations_right_helper_bijective, inverse_bijective.
  Qed.

  Lemma combinatorics_right_construction_helper_2 : ∀ z1 z2 x,
      x ∈ n → x ∈ k ↔ sets.functionify (combinations_right_helper z1 z2) x ∈ y.
  Proof.
    split; intros H0.
    - unfold sets.functionify.
      destruct constructive_indefinite_description as [crh].
      destruct a as [H1 [H2 H3]].
      set (ξ := mkSet H : elts n).
      replace x with (ξ : set) in * by auto.
      rewrite -> H3.
      unfold combinations_right_helper.
      destruct excluded_middle_informative; try now contradict n0.
      simpl.
      replace x with (ξ : set) in * by auto.
      now apply combinations_right_helper_l_1.
    - unfold sets.functionify in *.
      destruct constructive_indefinite_description as [crh].
      destruct a as [H1 [H2 H3]].
      set (ξ := mkSet H : elts n).
      replace x with (ξ : set) in * by auto.
      rewrite -> H3 in H0.
      unfold combinations_right_helper in H0.
      destruct excluded_middle_informative; auto.
      simpl in *.
      assert (x ∈ n \ k) as H4 by now apply Complement_classification.
      apply (combinations_right_helper_r_1 x z2),
      Complement_classification in H4.
      tauto.
  Qed.

  Theorem combinations_right_construction : ∀ z1 z2,
      graph (inverse (sets.functionify (combinations_right_helper z1 z2)))
            ∈ inverse_image_of_element combinations_proj y.
  Proof.
    intros z1 z2.
    apply Specify_classification.
    split.
    - rewrite -> cp_domain.
      apply combinations_right_construction_proto.
    - set (g := (inverse (sets.functionify (combinations_right_helper z1 z2)))).
      assert (graph g ∈ bijection_set n n).
      { apply combinations_right_construction_proto. }
      replace (graph g) with ((mkSet H : elts (bijection_set n n)) : set);
        rewrite <-? cp_action; auto.
      apply Extensionality.
      split; intros H2.
      + apply Specify_classification in H2 as [H2 H3].
        unfold functionify in H3.
        destruct Specify_classification, a, constructive_indefinite_description
          as [crh_inv].
        clear a i0 i e.
        destruct a0 as [H4 [H5 [H6 H7]]].
        apply function_record_injective in H6; unfold g in *.
        2: { rewrite -> inverse_range, sets.functionify_domain;
             auto using combinations_right_helper_bijective. }
        subst.
        unfold inverse in H3.
        destruct excluded_middle_informative; simpl in *.
        2: { contradict n0.
             auto using combinations_right_helper_bijective. }
        destruct b, constructive_indefinite_description as [crh_inv].
        repeat destruct a.
        rewrite -> inverse_range, inverse_domain, @sets.functionify_domain,
        @sets.functionify_range in *;
          auto using combinations_right_helper_bijective.
        rewrite <-(e1 z); auto.
        apply combinatorics_right_construction_helper_2; auto.
      + apply Specify_classification.
        assert (z ∈ n) as H9.
        { pose proof elts_in_set y as H0; simpl in *.
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
        2: { rewrite -> inverse_range, sets.functionify_domain;
             auto using combinations_right_helper_bijective. }
        subst.
        unfold inverse.
        destruct excluded_middle_informative.
        2: { contradict n0.
             auto using combinations_right_helper_bijective. }
        destruct b; simpl.
        destruct constructive_indefinite_description as [crh_inv].
        repeat destruct a.
        rewrite -> inverse_range, inverse_domain, @sets.functionify_domain,
        @sets.functionify_range in *;
          auto using combinations_right_helper_bijective.
        rewrite <-(e1 z) in H2; auto.
        apply combinatorics_right_construction_helper_2 in H2; auto.
        rewrite <-e0.
        apply function_maps_domain_to_range.
        now rewrite -> e.
  Qed.

  Definition combinations_right :
    elts (bijection_set k k × bijection_set (n \ k) (n \ k)) →
    elts (inverse_image_of_element combinations_proj y).
  Proof.
    intros z.
    pose proof (elts_in_set z) as H; simpl in H.
    apply Product_classification in H.
    destruct (constructive_indefinite_description H) as [z1].
    destruct (constructive_indefinite_description e) as [z2 [H0 [H1 H2]]].
    exact (mkSet (combinations_right_construction (mkSet H0) (mkSet H1))).
  Defined.

  Theorem combinations_left_right :
    ∀ x, combinations_left (combinations_right x) = x.
  Proof.
    intros x.
    apply set_proj_injective.
    unfold combinations_left.
    simpl.
    pose proof elts_in_set x as H; simpl in H.
    apply Product_classification in H as [x1 [x2 [H [H0 H1]]]].
    rewrite -> H1.
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
      rewrite -> H6 in H9.
      set (ζ := mkSet H9 : elts k).
      replace z with (ζ : set) in * by auto.
      rewrite -> H8.
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
      destruct excluded_middle_informative; simpl; try tauto.
      destruct b; simpl.
      destruct constructive_indefinite_description as [cr_inv].
      repeat destruct a.
      pose proof H9 as Z.
      rewrite <-(e2 z) at 2; rewrite <-(e2 z) in Z;
        try (rewrite -> H15; auto).
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
      2: { rewrite -> H15, inverse_range, sets.functionify_domain;
           auto using combinations_right_helper_bijective. }
      clear H17 i s.
      subst.
      rewrite -> inverse_domain, inverse_range, @sets.functionify_domain,
      @sets.functionify_range in *;
        auto using combinations_right_helper_bijective.
      unfold inverse in Z |-*.
      destruct excluded_middle_informative.
      2: { exfalso; auto using combinations_right_helper_bijective. }
      destruct b; simpl in *.
      destruct constructive_indefinite_description as [crh_inv].
      repeat destruct a.
      rewrite -> ? inverse_domain, ? inverse_range, @sets.functionify_domain,
      @sets.functionify_range in *;
        auto using combinations_right_helper_bijective.
      clear i s.
      rewrite <-(e6 (cr_inv z)) at 1.
      2: { rewrite <-e1.
           apply function_maps_domain_to_range.
           rewrite -> e; auto. }
      unfold sets.functionify.
      destruct constructive_indefinite_description as [crh].
      destruct a as [H4 [H8 H16]].
      assert (crh_inv (cr_inv z) ∈ n) as H17.
      { rewrite <-e5.
        apply function_maps_domain_to_range.
        rewrite -> e3, <-e1.
        apply function_maps_domain_to_range.
        rewrite -> e; auto. }
      set (ζ' := mkSet H17 : elts n).
      replace (crh_inv (cr_inv z)) with (ζ' : set) by auto.
      rewrite -> H16.
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
      destruct b; simpl.
      destruct constructive_indefinite_description as [cii].
      repeat destruct a.
      rewrite <-(e9 (x1'' (crh_inv (cr_inv z)))) at 2.
      2: { rewrite -> cii_range.
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
      rewrite -> H6 in H9.
      set (ζ := mkSet H9 : elts (n \ k)).
      replace z with (ζ : set) in * by auto.
      rewrite -> H8.
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
      destruct excluded_middle_informative; simpl; try tauto.
      destruct b; simpl.
      destruct constructive_indefinite_description as [cr_inv].
      repeat destruct a.
      pose proof H9 as Z.
      rewrite <-(e2 z) at 2; rewrite <-(e2 z) in Z;
        try (rewrite -> H15; apply (complement_subset k n); auto).
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
      2: { rewrite -> H15, inverse_range, sets.functionify_domain;
           auto using combinations_right_helper_bijective. }
      clear H17 i s.
      subst.
      rewrite -> inverse_domain, inverse_range, @sets.functionify_domain,
      @sets.functionify_range in *;
        auto using combinations_right_helper_bijective.
      unfold inverse in Z |-*.
      destruct excluded_middle_informative; simpl in *.
      2: { exfalso; auto using combinations_right_helper_bijective. }
      destruct b; simpl.
      destruct constructive_indefinite_description as [crh_inv].
      repeat destruct a.
      rewrite -> ? inverse_domain, ? inverse_range, @sets.functionify_domain,
      @sets.functionify_range in *;
        auto using combinations_right_helper_bijective.
      clear i s.
      rewrite <-(e6 (cr_inv z)) at 1.
      2: { rewrite <-e1.
           apply function_maps_domain_to_range.
           rewrite -> e; apply (complement_subset k n); auto. }
      unfold sets.functionify.
      destruct constructive_indefinite_description as [crh].
      destruct a as [H4 [H8 H16]].
      assert (crh_inv (cr_inv z) ∈ n) as H17.
      { rewrite <-e5.
        apply function_maps_domain_to_range.
        rewrite -> e3, <-e1.
        apply function_maps_domain_to_range.
        rewrite -> e; apply (complement_subset k n); auto. }
      set (ζ' := mkSet H17 : elts n).
      replace (crh_inv (cr_inv z)) with (ζ' : set) by auto.
      rewrite -> H16.
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
      destruct b; simpl.
      destruct constructive_indefinite_description as [cii].
      repeat destruct a.
      rewrite <-(e9 (x2'' (crh_inv (cr_inv z)))) at 2.
      2: { rewrite -> cii_range.
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
    pose proof elts_in_set x as H; simpl in H.
    apply Inverse_image_classification_domain in H as H0.
    2: { rewrite -> cp_range.
         auto using elts_in_set. }
    rewrite -> cp_domain in H0.
    apply Specify_classification in H0 as [H0 [x' [H1 [H2 [H3 H4]]]]].
    rewrite <-H3.
    f_equal.
    apply func_ext.
    { rewrite -> inverse_domain; auto using combinations_right_helper_bijective.
      rewrite -> sets.functionify_range.
      congruence. }
    { rewrite -> inverse_range; auto using combinations_right_helper_bijective.
      rewrite -> sets.functionify_domain.
      congruence. }
    intros z H5.
    rewrite -> inverse_domain, sets.functionify_range in H5;
      auto using combinations_right_helper_bijective.
    assert (x' z ∈ n) as H6.
    { rewrite <-H2.
      apply function_maps_domain_to_range.
      congruence. }
    rewrite inverse_shift_right; auto using combinations_right_helper_bijective.
    2: { now rewrite -> sets.functionify_range. }
    2: { now rewrite -> sets.functionify_domain. }
    unfold sets.functionify.
    destruct constructive_indefinite_description as [crh].
    destruct a as [H7 [H8 H9]].
    set (ξ'ζ := mkSet H6 : elts n).
    replace (x' z) with (ξ'ζ : set) by auto.
    rewrite -> H9.
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
      set (ξ'ζ' := mkSet i1 : elts k).
      replace (x' z) with (ξ'ζ' : set) by auto.
      rewrite -> H11.
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
      rewrite -> left_inverse; auto; try congruence.
      symmetry.
      rewrite -> inverse_shift_right; auto using cii_bijective.
      2: { rewrite -> cii_range, <-H17.
           apply function_maps_domain_to_range.
           congruence. }
      2: { now rewrite -> cii_domain. }
      destruct h as [h'' H''].
      unfold comb_inverse_image_incl, functionify.
      destruct Specify_classification, a,
      constructive_indefinite_description as [h'''].
      clear a i2 i3 e.
      destruct a0 as [H24 [H25 [H26 H27]]].
      simpl in H18.
      f_equal.
      apply function_record_injective; congruence.
    + assert (ξ'ζ ∈ n \ k) as Z by
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
      set (ξ'ζ' := mkSet Z : elts (n \ k)).
      replace (x' z) with (ξ'ζ' : set) by auto.
      rewrite -> H11.
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
      rewrite -> left_inverse; auto; try congruence.
      symmetry.
      rewrite -> inverse_shift_right; auto using cii_bijective.
      2: { rewrite -> cii_range, <-H17.
           apply function_maps_domain_to_range.
           congruence. }
      2: { now rewrite -> cii_domain. }
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
  rewrite -> cp_range in H0.
  set (γ := mkSet H0 : elts (set_of_combinations n k)).
  replace y with (γ : set) in * by auto.
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

Lemma binomial_coefficient_plus_form :
  ∀ n m, (n + m)! = (binomial (n + m) m * m! * n!)%N.
Proof.
  intros n m.
  assert (m ⊂ n + m)%N as H.
  { rewrite <-le_is_subset, add_comm.
    now exists n. }
  pose proof (combinations_orbit_stabilizer (n+m) m) H as H0.
  rewrite -> add_comm, (naturals_sum_diff n m), add_comm in H0.
  apply equinumerous_cardinality in H0.
  rewrite -> ? finite_products_card, ? number_of_permutations_n, <-mul_assoc
    in *; auto using permutations_are_finite, binomials_are_finite,
          finite_products_are_finite.
Qed.

Theorem binomial_coefficient :
  ∀ n k, (k ≤ n → n! = binomial n k * k! * (n - k)!)%N.
Proof.
  intros n k [m H].
  subst.
  rewrite -> (add_comm k), sub_abba.
  apply binomial_coefficient_plus_form.
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

Theorem binomial_zero : ∀ n : N, binomial n 0 = 1%N.
Proof.
  intros n.
  assert (0 ≤ n)%N as H by auto using zero_le.
  apply binomial_coefficient in H.
  rewrite -> sub_0_r, ? zero_factorial, mul_1_r, <-(mul_1_l (n!)) in H at 1.
  apply cancellation_mul in H; auto using factorial_ne_0.
Qed.

Theorem binomial_coefficient_Q :
  ∀ n k, (k ≤ n)%N → (n! / (k! * (n - k)!))%Q = binomial n k.
Proof.
  intros n k H.
  apply binomial_coefficient in H.
  assert (k! * (n - k)! ≠ 0)%Z as H0.
  - apply (ne0_cancellation ℤ_ID); intro; eapply factorial_ne_0, INZ_eq; eauto.
  - rewrite -> H, <-? INZ_mul, <-integers.M2, inv_div, <-IZQ_mul; auto.
    field_simplify; rewrite -> ? div_inv, ? inv_one; try ring.
    contradict H0.
    now apply IZQ_eq.
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
  intros k H.
  apply binomial_overflow.
  rewrite -> naturals.lt_def.
  exists k.
  split; auto.
  ring.
Qed.

Theorem one_factorial : 1! = 1%N.
Proof.
  apply prod_N_0.
Qed.

Theorem binomial_one : binomial 1 1 = 1%N.
Proof.
  pose proof binomial_coefficient 1 1 as H.
  rewrite -> ? one_factorial, sub_diag, zero_factorial in H.
  rewrite -> H at 3; try ring.
  eauto using naturals.le_refl.
Qed.

Theorem binomial_n_n : ∀ n, binomial n n = 1%N.
Proof.
  intros n.
  pose proof binomial_coefficient n n as H.
  rewrite -> sub_diag, zero_factorial, mul_1_r, <-(mul_1_l (n!)) in H at 1.
  eapply cancellation_mul; eauto using factorial_ne_0.
  rewrite -> H; auto using naturals.le_refl.
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
