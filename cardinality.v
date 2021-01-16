Require Export naturals.

Open Scope set_scope.

Definition equinumerous A B := ∃ f, domain f = A ∧ range f = B ∧ bijective f.

Infix "~" := equinumerous (at level 70) : set_scope.

Theorem cardinality_refl : ∀ A, A ~ A.
Proof.
  intros A.
  exists (functionify A A (λ x, x)).
  unfold functionify.
  destruct constructive_indefinite_description as [f a].
  destruct a as [H [H0 H1]].
  subst.
  repeat split; auto.
  - intros [a1 A1] [a2 A2] H2.
    apply set_proj_injective.
    inversion H2.
    now rewrite <-(H1 (exist _ _ A1)), <-(H1 (exist _ _ A2)).
  - apply Surjective_classification.
    intros y H.
    exists y.
    split; try congruence.
    rewrite H0 in H.
    now replace y with (proj1_sig (exist (λ x, x ∈ domain f) _ H)).
Qed.

Theorem cardinality_sym : ∀ A B, A ~ B → B ~ A.
Proof.
  intros A B [f [H [H0 [H1 H2]]]].
  pose proof H2 as H3.
  apply right_inverse_iff_surjective in H3 as [g [H3 [H4 H5]]].
  exists g; subst.
  repeat split; try congruence.
  - apply Injective_classification.
    intros x y H H0 H6.
    rewrite <-H5, <-H6, H5; congruence.
  - apply Surjective_classification.
    intros y H.
    exists (f y).
    split.
    + rewrite H3.
      apply function_maps_domain_to_range.
      congruence.
    + rewrite Injective_classification in H1.
      apply H1; try rewrite <-H4; auto.
      * apply function_maps_domain_to_range.
        rewrite H3.
        apply function_maps_domain_to_range.
        congruence.
      * rewrite H5; auto.
        apply function_maps_domain_to_range.
        congruence.
Qed.

Theorem cardinality_trans : ∀ A B C, A ~ B → B ~ C → A ~ C.
Proof.
  intros A B C [f [H [H0 [H1 H2]]]] [g [H3 [H4 [H5 H6]]]]; subst.
  destruct (Composition_classification g f) as [H [H0 H4]]; try congruence.
  exists (g ∘ f).
  repeat split; try congruence.
  - now apply composition_injective.
  - now apply composition_surjective.
Qed.

Theorem cardinality_is_equivalence :
  ∀ X, is_equivalence (P X) {z in P X × P X |
                              proj1 (P X) (P X) z ~ proj2 (P X) (P X) z}.
Proof.
  repeat split.
  - intros A H.
    apply Specify_classification.
    split.
    + apply Product_classification.
      now exists A, A.
    + rewrite proj1_eval, proj2_eval; auto using cardinality_refl.
  - intros A B H H0 H1.
    apply Specify_classification in H1 as [H1 H2].
    apply Specify_classification.
    rewrite proj1_eval, proj2_eval in *; auto.
    split; auto using cardinality_sym.
    apply Product_classification.
    now exists B, A.
  - intros A B C H H0 H1 H2 H3.
    apply Specify_classification in H2 as [H2 H4].
    apply Specify_classification in H3 as [H3 H5].
    apply Specify_classification.
    rewrite proj1_eval, proj2_eval in *; auto.
    split; eauto using cardinality_trans.
    apply Product_classification.
    now exists A, C.
Qed.

Theorem injective_into_image : ∀ f, injective f → domain f ~ image f.
Proof.
  intros f H.
  destruct (function_construction (domain f) (image f) (λ x, f x))
    as [f' [H0 [H1 H2]]].
  - intros a H0.
    apply Specify_classification.
    split; auto using function_maps_domain_to_range.
    now (exists a).
  - exists f'.
    repeat split; auto.
    + apply Injective_classification.
      intros x y H3 H4 H5.
      rewrite ? H2 in H5; try congruence.
      rewrite Injective_classification in H.
      apply H; congruence.
    + apply Surjective_classification.
      intros y H3.
      rewrite H1 in H3.
      apply Specify_classification in H3 as [H3 [x [H4 H5]]].
      exists x.
      split; try congruence.
      now rewrite H2.
Qed.

Theorem cardinality_of_subsets_of_n :
  ∀ m (n : N), m ⊊ n → ∃ n', n' < n ∧ m ~ n'.
Proof.
  intros m n H.
  revert m H.
  induction n using Induction; intros m H.
  - apply proper_subset_inhab in H as [z [H H0]].
    contradiction (Empty_set_classification z).
  - pose proof H as H0.
    apply proper_subset_inhab in H0 as [z [H0 H1]].
    destruct (classic (n ∈ m)).
    + destruct
        (function_construction
           m n (λ x, if (excluded_middle_informative (x = n)) then z else x))
        as [f [H3 [H4 H5]]].
      { intros a H3.
        destruct excluded_middle_informative.
        - rewrite <-S_is_succ in H0.
          apply Pairwise_union_classification in H0 as [H0 | H0]; auto.
          apply Singleton_classification in H0.
          now subst.
        - destruct H as [H H4].
          apply H in H3.
          rewrite <-S_is_succ in H3.
          apply Pairwise_union_classification in H3 as [H3 | H3]; auto.
          now apply Singleton_classification in H3. }
      assert (injective f) as H6.
      { apply Injective_classification.
        intros x y H6 H7 H8.
        rewrite ? H5 in H8; try congruence.
        repeat destruct excluded_middle_informative; congruence. }
      destruct (classic (image f = n)).
      * exists n.
        split; auto using succ_lt.
        rewrite <-H3, <-H7.
        auto using injective_into_image.
      * destruct (IHn (image f)) as [n' [H8 H9]].
        { split; auto.
          rewrite <-H4.
          apply image_subset_range. }
        exists n'.
        split; eauto using lt_trans, succ_lt.
        rewrite <-H3.
        eauto using injective_into_image, cardinality_trans.
    + destruct (classic (m = n)).
      * exists n.
        split; subst; eauto using lt_trans, succ_lt, cardinality_refl.
      * assert (m ⊊ n).
        { destruct H as [H H4].
          split; auto.
          intros x H5.
          apply H in H5 as H6.
          rewrite <-S_is_succ in H6.
          apply Pairwise_union_classification in H6 as [H6 | H6]; auto.
          apply Singleton_classification in H6.
          now subst. }
        apply IHn in H4 as [n' [H4 H5]].
        exists n'.
        split; eauto using lt_trans, succ_lt.
Qed.

Lemma equivalence_minus_element_singular : ∀ A x y,
    x ∈ A → y ∈ A → A \ {x,x} ~ A \ {y,y}.
Proof.
  intros A x y H H0.
  destruct (classic (x = y)); subst; auto using cardinality_refl.
  destruct (function_construction
              (A \ {x,x}) (A \ {y,y})
              (λ z, if (excluded_middle_informative (z = y)) then x else z))
    as [f' [H2 [H3 H4]]].
  { intros a0 H2.
    destruct excluded_middle_informative; apply Complement_classification;
      rewrite Singleton_classification; auto.
    - apply Complement_classification in H2.
      tauto. }
  exists f'.
  repeat split; auto.
  - apply Injective_classification.
    intros x0 y0 H5 H6 H7.
    destruct (classic (x = x0)), (classic (x = y0)); rewrite ? H4 in *;
      try repeat destruct excluded_middle_informative; subst; try congruence.
    + rewrite H2 in H5.
      apply Complement_classification in H5 as [H5 H10].
      now rewrite Singleton_classification in H10.
    + rewrite H2 in H6.
      apply Complement_classification in H6 as [H6 H10].
      now rewrite Singleton_classification in H10.
  - apply Surjective_classification.
    intros y0 H5.
    destruct (classic (x = y0)).
    + exists y.
      assert (y ∈ A \ {x,x}) as H8.
      { apply Complement_classification.
        rewrite Singleton_classification.
        intuition. }
      split; try congruence.
      rewrite H4; auto.
      destruct excluded_middle_informative; congruence.
    + exists y0.
      assert (y0 ∈ A \ {x,x}) as H7.
      { apply Complement_classification.
        rewrite Singleton_classification.
        rewrite H3 in H5.
        apply Complement_classification in H5.
        intuition. }
      split; try congruence.
      rewrite H4; auto.
      destruct excluded_middle_informative; auto.
      subst.
      rewrite H3 in H5.
      apply Complement_classification in H5.
      rewrite Singleton_classification in H5.
      intuition.
Qed.

Theorem equivalence_minus_element : ∀ A B x y,
    A ~ B → x ∈ A → y ∈ B → A \ {x,x} ~ B \ {y,y}.
Proof.
  intros A B x y [f [H [H0 [H1 H2]]]] H3 H4.
  rewrite Injective_classification in H1.
  rewrite Surjective_classification in H2.
  assert (A \ {x,x} ~ B \ {f x, f x}) as H5.
  { destruct (function_construction (A \ {x,x}) (B \ {f x, f x}) (λ x, f x))
      as [f' [H5 [H6 H7]]].
    { intros a H5.
      apply Complement_classification in H5 as [H5 H6].
      apply Complement_classification.
      split.
      - rewrite <-H0.
        apply function_maps_domain_to_range.
        congruence.
      - rewrite Singleton_classification.
        intros H7.
        apply H1 in H7; try congruence.
        now rewrite Singleton_classification in H6. }
    exists f'.
    repeat split; auto.
    - apply Injective_classification.
      intros x0 y0 H8 H9 H10.
      rewrite ? H7 in H10; try congruence.
      apply H1; auto; rewrite H, H5, Complement_classification in *; tauto.
    - apply Surjective_classification.
      intros y0 H8.
      destruct (H2 y0) as [x0 [H9 H10]].
      { rewrite H0, H6 in *.
        apply Complement_classification in H8.
        tauto. }
      exists x0.
      split.
      + rewrite H, H5 in *.
        apply Complement_classification.
        split; auto.
        rewrite Singleton_classification.
        intros H11.
        subst.
        rewrite H6 in H8.
        apply Complement_classification in H8 as [H8 H10].
        now rewrite Singleton_classification in H10.
      + rewrite H7; auto.
        apply Complement_classification.
        split; try congruence.
        rewrite Singleton_classification.
        intros H11.
        subst.
        rewrite H6 in H8.
        apply Complement_classification in H8 as [H8 H10].
        now rewrite Singleton_classification in H10. }
  eapply cardinality_trans; eauto.
  apply equivalence_minus_element_singular; auto.
  rewrite <-H0.
  apply function_maps_domain_to_range.
  congruence.
Qed.

Theorem proper_subsets_of_natural_numbers : ∀ m (n : N), m ⊊ n → ¬ n ~ m.
Proof.
  intros m n H.
  revert m H.
  induction n using Induction; intros m H.
  - apply proper_subset_inhab in H as [z [H H0]].
    contradiction (Empty_set_classification z).
  - intros [f [H0 [H1 [H2 H3]]]].
    assert (S n \ {n,n} = n) as H4.
    { apply Extensionality.
      split; intros H4.
      - apply Complement_classification in H4 as [H4 H5].
        rewrite <-S_is_succ in H4.
        apply Pairwise_union_classification in H4 as [H4 | H4]; tauto.
      - apply Complement_classification.
        split.
        + rewrite <-S_is_succ.
          apply Pairwise_union_classification.
          tauto.
        + rewrite Singleton_classification.
          intros H5.
          subst.
          contradiction (no_quines n). }
    destruct (classic (n ∈ m)) as [H5 | H5].
    + apply (IHn (m \ {n,n})); repeat split.
      * intros x H6.
        apply Complement_classification in H6 as [H6 H7].
        destruct H as [H H8].
        apply H in H6.
        rewrite <-S_is_succ in H6.
        apply Pairwise_union_classification in H6 as [H6 | H6]; tauto.
      * intros H6.
        rewrite <-S_is_succ in H.
        unfold succ in H.
        rewrite <-H6 in H at 1.
        destruct H as [H H7].
        contradiction H7.
        apply Extensionality; split; intros H8.
        -- apply Pairwise_union_classification.
           destruct (classic (z = n)) as [H9 | H9].
           ++ right.
              now apply Singleton_classification.
           ++ left.
              apply Complement_classification.
              now rewrite Singleton_classification.
        -- apply Pairwise_union_classification in H8 as [H8 | H8].
           ++ apply Complement_classification in H8; intuition.
           ++ apply Singleton_classification in H8.
              now subst.
      * rewrite <-H4 at 1.
        apply equivalence_minus_element; auto.
        -- exists f.
           repeat split; auto.
        -- rewrite <-S_is_succ.
           apply Pairwise_union_classification.
           rewrite Singleton_classification.
           tauto.
    + apply (IHn (m \ {f n, f n})).
      * apply (subsetneq_subset_trans _ m); repeat split.
        -- intros x H6.
           now apply Complement_classification in H6 as [H6 H7].
        -- intros H6.
           assert (f n ∈ m \ {f n, f n}) as H7.
           { rewrite H6, <-H1.
             apply function_maps_domain_to_range.
             rewrite H0, <-S_is_succ.
             now apply Pairwise_union_classification,
             or_intror, Singleton_classification. }
           apply Complement_classification in H7 as [H7 H8].
           now rewrite Singleton_classification in H8.
        -- destruct H as [H H6].
           intros x H7.
           apply H in H7 as H8.
           rewrite <-S_is_succ in H8.
           apply Pairwise_union_classification in H8 as [H8 | H8]; auto.
           apply Singleton_classification in H8.
           now subst.
      * rewrite <-H4 at 1.
        apply equivalence_minus_element.
        ++ exists f.
           repeat split; auto.
        ++ rewrite <-S_is_succ.
           apply Pairwise_union_classification.
           rewrite Singleton_classification.
           tauto.
        ++ rewrite <-H1.
           apply function_maps_domain_to_range.
           rewrite H0, <-S_is_succ.
           apply Pairwise_union_classification.
           rewrite Singleton_classification.
           tauto.
Qed.

Theorem equiv_proper_subset_ω : ∃ S, S ⊊ ω ∧ S ~ ω.
Proof.
  exists (ω \ {0,0}).
  repeat split.
  - intros x H.
    now apply Complement_classification in H as [H H0].
  - intros H.
    assert (0 ∈ ω \ {0,0}) as H0.
    { rewrite H.
      apply PA1_ω. }
    apply Complement_classification in H0 as [H0 H1].
    now rewrite Singleton_classification in H1.
  - apply cardinality_sym.
    set (f := functionify ω ω (λ x, x + 1)).
    destruct (function_construction ω (ω \ {0,0}) (λ x, f x))
      as [f' [H [H0 H1]]].
    + intros a H.
      unfold functionify in f.
      destruct constructive_indefinite_description
        as [f' [H0 [H1 H2]]].
      replace a with (proj1_sig (exist (λ x, x ∈ ω) _ H)) by auto.
      rewrite H2.
      apply Complement_classification.
      split.
      * apply (proj2_sig ((exist (λ x, x ∈ ω) _ H) + 1)).
      * rewrite Singleton_classification.
        intros H3.
        apply set_proj_injective in H3.
        rewrite add_1_r in H3.
        symmetry in H3.
        now apply PA4 in H3.
    + exists f'.
      repeat split; auto.
      * apply Injective_classification.
        intros x y H2 H3 H4.
        rewrite H in *.
        rewrite ? H1 in H4; auto.
        unfold f, functionify in H4.
        destruct constructive_indefinite_description as [f'' [H5 [H6 H7]]].
        replace x with (proj1_sig (exist (λ x, x ∈ ω) _ H2)) in * by auto.
        replace y with (proj1_sig (exist (λ x, x ∈ ω) _ H3)) in * by auto.
        rewrite ? H7, ? (add_comm _ 1) in H4.
        apply set_proj_injective, cancellation_add in H4.
        now f_equal.
      * intros y.
        assert (proj1_sig y ∈ ω) as H2.
        { pose proof proj2_sig y as H2.
          simpl in H2.
          rewrite H0 in H2.
          apply Complement_classification in H2.
          tauto. }
        set (γ := (exist (λ x, x ∈ ω) _ H2) : N).
        assert (γ ≠ 0) as H3.
        { intros H3.
          assert (γ ∈ ω \ {0,0}) as H4.
          { rewrite <-H0.
            unfold γ.
            simpl.
            apply (proj2_sig y). }
          rewrite H3 in H4.
          apply Complement_classification in H4.
          rewrite Singleton_classification in H4.
          tauto. }
        apply succ_0 in H3 as [m H3].
        assert (m ∈ domain f') as H5.
        { rewrite H.
          apply (proj2_sig m). }
        exists (exist (λ x, x ∈ domain f') _ H5).
        simpl.
        apply set_proj_injective.
        simpl.
        replace (proj1_sig y) with (proj1_sig γ) by auto.
        rewrite H1; try apply (proj2_sig m).
        unfold f, functionify.
        destruct constructive_indefinite_description as [f'' [H4 [H6 H7]]].
        now rewrite H7, H3, add_1_r.
Qed.

Definition finite S := ∃ n : N, S ~ n.

Definition infinite S := ¬ finite S.

Theorem infinite_ω : infinite ω.
Proof.
  intros [n H].
  pose proof H as H0.
  destruct H0 as [f [H0 [H1 [H2 H3]]]].
  destruct equiv_proper_subset_ω as [S [H4 H5]].
  pose proof H4 as [H6 H7].
  contradiction (proper_subsets_of_natural_numbers
                   {x in n | ∃ s, s ∈ S ∧ x = f s} n); repeat split.
  - intros x H8.
    now apply Specify_classification in H8 as [H8 H9].
  - intros H8.
    apply proper_subset_inhab in H4 as [z [H9 H10]].
    assert (f z ∉ n) as H11.
    { intros H11.
      rewrite <-H8 in H11.
      apply Specify_classification in H11 as [H11 [s [H12 H13]]].
      rewrite Injective_classification in H2.
      apply H2 in H13; rewrite H0 in *; auto.
      now subst. }
    contradiction H11.
    rewrite <-H1.
    apply function_maps_domain_to_range.
    congruence.
  - apply (cardinality_trans _ ω); auto using cardinality_sym.
    apply (cardinality_trans _ S); auto using cardinality_sym.
    destruct (function_construction
                S {x in n | ∃ s : set, s ∈ S ∧ x = f s} (λ x, f x))
      as [f' [H8 [H9 H10]]].
    + intros a H8.
      apply Specify_classification.
      split.
      * rewrite <-H1.
        apply function_maps_domain_to_range.
        rewrite H0.
        auto.
      * now (exists a).
    + exists f'.
      repeat split; auto.
      * rewrite Injective_classification in *.
        intros x y H11 H12 H13.
        rewrite ? H10 in H13; try congruence.
        apply H2; auto; rewrite H0, H8 in *; auto.
      * rewrite Surjective_classification.
        intros y H11.
        rewrite H9 in H11.
        apply Specify_classification in H11 as [H11 [s [H12 H13]]].
        rewrite <-H8 in H12.
        exists s.
        split; auto.
        rewrite H10; congruence.
Qed.
