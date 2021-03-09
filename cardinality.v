Require Export naturals Setoid.
Set Warnings "-notation-overridden".

Open Scope set_scope.

Definition equinumerous A B := ∃ f, domain f = A ∧ range f = B ∧ bijective f.

Infix "~" := equinumerous (at level 70) : set_scope.

Theorem cardinality_refl : ∀ A, A ~ A.
Proof.
  intros A.
  exists (functionify A A id).
  unfold bijective.
  rewrite Injective_classification, Surjective_classification,
  functionify_domain, functionify_range.
  repeat split; auto; intros.
  - now rewrite <-(setify_action _ _ H), <-(setify_action _ _ H0),
    ? functionify_action in H1.
  - exists y.
    now rewrite <-(setify_action _ _ H), functionify_action.
Qed.

Theorem cardinality_eq : ∀ A B, A = B → A ~ B.
Proof.
  intros A B H.
  subst.
  auto using cardinality_refl.
Qed.

Theorem cardinality_sym : ∀ A B, A ~ B → B ~ A.
Proof.
  intros A B [f [H [H0 H1]]].
  exists (inverse f).
  rewrite inverse_domain, inverse_range; auto using inverse_bijective.
Qed.

Theorem cardinality_trans : ∀ A B C, A ~ B → B ~ C → A ~ C.
Proof.
  intros A B C [f [H [H0 [H1 H2]]]] [g [H3 [H4 [H5 H6]]]]; subst.
  destruct (Composition_classification g f) as [H [H0 H4]]; try congruence.
  exists (g ∘ f).
  repeat split; auto using composition_injective, composition_surjective.
Qed.

Theorem cardinality_is_equivalence :
  ∀ X, is_equivalence (P X) {z in P X × P X |
                              proj1 (P X) (P X) z ~ proj2 (P X) (P X) z}.
Proof.
  repeat split.
  - intros A H.
    apply Specify_classification.
    split.
    + apply Product_classification; eauto.
    + rewrite proj1_eval, proj2_eval; auto using cardinality_refl.
  - intros A B H H0 H1.
    apply Specify_classification in H1 as [H1 H2].
    apply Specify_classification.
    rewrite proj1_eval, proj2_eval in *; auto.
    split; auto using cardinality_sym.
    apply Product_classification; eauto.
  - intros A B C H H0 H1 H2 H3.
    apply Specify_classification in H2 as [H2 H4].
    apply Specify_classification in H3 as [H3 H5].
    apply Specify_classification.
    rewrite proj1_eval, proj2_eval in *; auto.
    split; eauto using cardinality_trans.
    apply Product_classification; eauto.
Qed.

Add Parametric Relation : set equinumerous
      reflexivity proved by (cardinality_refl)
      symmetry proved by (cardinality_sym)
      transitivity proved by (cardinality_trans) as set_equivalence.

Theorem injective_into_image : ∀ f, injective f → domain f ~ image f.
Proof.
  intros f H.
  exists (restriction_Y _ _ (Set_is_subset (image f))).
  rewrite restriction_Y_domain, restriction_Y_range.
  repeat split; auto.
  - rewrite Injective_classification in *.
    intros x y H0 H1 H2.
    rewrite restriction_Y_domain, ? restriction_Y_action in *; auto.
  - apply Surjective_classification.
    intros y H0.
    rewrite restriction_Y_domain, restriction_Y_range in *.
    apply Specify_classification in H0 as [H0 [x [H1 H2]]].
    exists x.
    now rewrite restriction_Y_action.
Qed.

Theorem injection_restriction :
  ∀ f S, injective f → S ⊂ domain f → S ~ push_forward f S.
Proof.
  intros f S H H0.
  assert (image (restriction f S) ⊂ push_forward f S).
  { intros y H1.
    apply Specify_classification.
    apply Specify_classification in H1 as [H1 [x [H2 H3]]].
    rewrite restriction_range, restriction_domain,
    <-restriction_action in *; eauto. }
  exists (restriction_Y _ _ H1).
  rewrite restriction_Y_domain, restriction_Y_range, restriction_domain.
  repeat split; auto.
  - now apply Intersection_subset.
  - rewrite Injective_classification in *.
    intros x y H2 H3 H4.
    rewrite restriction_Y_domain, ? restriction_Y_action, restriction_domain,
    <-? restriction_action in *; auto.
    apply Intersection_right in H2, H3; auto.
  - apply Surjective_classification.
    intros y H2.
    rewrite restriction_Y_range, ? restriction_Y_action, restriction_Y_domain,
    restriction_domain, <-? restriction_action in *; auto.
    apply Specify_classification in H2 as [H2 [x [H3 H4]]].
    exists x.
    rewrite restriction_Y_action, <-restriction_action; auto.
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
    + destruct (classic (m = n)); subst.
      * eauto using lt_trans, succ_lt, cardinality_refl.
      * assert (m ⊊ n) as H4.
        { destruct H as [H H4].
          split; auto.
          intros x H5.
          apply H in H5 as H6.
          rewrite <-S_is_succ in H6.
          apply Pairwise_union_classification in H6 as [H6 | H6]; auto.
          apply Singleton_classification in H6.
          now subst. }
        apply IHn in H4 as [n' [H4 H5]].
        eauto using lt_trans, succ_lt.
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
      repeat destruct excluded_middle_informative; subst; try congruence;
        now rewrite H2, Complement_classification,
        Singleton_classification in *.
  - apply Surjective_classification.
    intros y0 H5.
    destruct (classic (x = y0)).
    + exists y.
      assert (y ∈ A \ {x,x}) as H8.
      { rewrite Complement_classification, Singleton_classification.
        intuition. }
      split; try congruence.
      rewrite H4; auto.
      destruct excluded_middle_informative; congruence.
    + exists y0.
      assert (y0 ∈ A \ {x,x}) as H7.
      { rewrite Complement_classification, Singleton_classification,
        H3, Complement_classification in *.
        intuition. }
      split; try congruence.
      rewrite H4; auto.
      destruct excluded_middle_informative; auto.
      now rewrite e, H3, Complement_classification,
      Singleton_classification in H5.
Qed.

Theorem equivalence_minus_element : ∀ A B x y,
    A ~ B → x ∈ A → y ∈ B → A \ {x,x} ~ B \ {y,y}.
Proof.
  intros A B x y [f [H [H0 [H1 H2]]]] H3 H4.
  rewrite Injective_classification, Surjective_classification in *.
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
      { rewrite H0, H6, Complement_classification in *.
        tauto. }
      exists x0.
      split.
      + rewrite H, H5, Complement_classification, Singleton_classification in *.
        split; auto.
        intros H11.
        subst.
        now rewrite H6, Complement_classification,
        Singleton_classification in H8.
      + rewrite H7; auto.
        rewrite Complement_classification, Singleton_classification.
        split; try congruence.
        intros H11.
        subst.
        now rewrite H6, Complement_classification,
        Singleton_classification in H8. }
  eapply cardinality_trans; eauto.
  apply equivalence_minus_element_singular; auto.
  rewrite <-H0.
  apply function_maps_domain_to_range.
  congruence.
Qed.

Lemma two_sided_inverse_bijective : ∀ A B,
  (∃ (f : elts A → elts B) (g : elts B → elts A),
      ((∀ a : elts A, g (f a) = a) ∧ (∀ b : elts B, f (g b) = b))) → A ~ B.
Proof.
  intros A B [f [g [H H0]]].
  exists (functionify _ _ f).
  unfold bijective.
  rewrite Injective_classification, Surjective_classification,
  functionify_range, functionify_domain.
  repeat split; auto.
  - intros x y H1 H2 H3.
    rewrite <-(setify_action _ _ H1), <-(setify_action _ _ H2),
    ? functionify_action in *.
    apply set_proj_injective in H3.
    f_equal.
    now rewrite <-H, <-H3, H.
  - intros y H1.
    rewrite <-(setify_action _ _ H1) in *.
    exists (g (exist _ _ H1)).
    rewrite functionify_action, H0.
    auto using elts_in_set.
Qed.

Theorem two_sided_inverse_bijective_set:
  ∀ A B, (∃ f g, (∀ a, a ∈ A → (f a ∈ B ∧ g (f a) = a)) ∧
                 (∀ b, b ∈ B → (g b ∈ A ∧ f (g b) = b))) → A ~ B.
Proof.
  intros A B [f [g [H H0]]].
  destruct (function_construction A B f) as [f' [H1 [H2 H3]]].
  { intros a H1.
    apply H in H1.
    tauto. }
  exists f'.
  repeat split; auto.
  - apply Injective_classification.
    intros x y H4 H5 H6.
    rewrite H1 in *.
    rewrite ? H3 in H6; auto.
    apply (f_equal g) in H6.
    apply H in H4 as [H4 H7].
    apply H in H5 as [H5 H8].
    now rewrite H7, H8 in H6.
  - apply Surjective_classification.
    intros y H4.
    rewrite H1, H2 in *.
    exists (g y).
    split.
    + apply H0 in H4; tauto.
    + rewrite H3.
      * now apply H0 in H4 as [H4 H5].
      * apply H0 in H4; tauto.
Qed.

Theorem proper_subsets_of_natural_numbers : ∀ m (n : N), m ⊊ n → ¬ n ~ m.
Proof.
  intros m n H.
  revert m H.
  induction n using Induction; intros m H.
  { apply proper_subset_inhab in H as [z [H H0]].
    contradiction (Empty_set_classification z). }
  intros [f [H0 [H1 [H2 H3]]]].
  assert (S n \ {n,n} = n) as H4.
  { rewrite <-S_is_succ.
    apply complement_disjoint_union, disjoint_succ. }
  destruct (classic (n ∈ m)) as [H5 | H5].
  - apply (IHn (m \ {n,n})); repeat split.
    + intros x H6.
      apply Complement_classification in H6 as [H6 H7].
      destruct H as [H H8].
      apply H in H6.
      rewrite <-S_is_succ in H6.
      apply Pairwise_union_classification in H6 as [H6 | H6]; tauto.
    + intros H6.
      rewrite <-S_is_succ in H.
      unfold succ in H.
      rewrite <-H6 in H at 1.
      destruct H as [H H7].
      contradiction H7.
      apply Extensionality; split; intros H8.
      * destruct (classic (z = n));
          rewrite Pairwise_union_classification, Complement_classification,
          Singleton_classification; intuition.
      * rewrite Pairwise_union_classification, Complement_classification,
        Singleton_classification in H8; intuition; congruence.
    + rewrite <-H4 at 1.
      apply equivalence_minus_element; auto.
      * exists f.
        repeat split; auto.
      * apply lt_is_in, succ_lt.
  - apply (IHn (m \ {f n, f n})).
    + apply (subsetneq_subset_trans _ m); repeat split.
      * intros x H6.
        now apply Complement_classification in H6 as [H6 H7].
      * intros H6.
        assert (f n ∈ m \ {f n, f n}) as H7.
        { rewrite H6, <-H1.
          apply function_maps_domain_to_range.
          rewrite H0.
          apply lt_is_in, succ_lt. }
        now rewrite Complement_classification, Singleton_classification in *.
      * destruct H as [H H6].
        intros x H7.
        apply H in H7 as H8.
        rewrite <-S_is_succ in *.
        apply Pairwise_union_classification in H8 as [H8 | H8]; auto.
        apply Singleton_classification in H8.
        now subst.
    + rewrite <-H4 at 1.
      apply equivalence_minus_element.
      * exists f.
        repeat split; auto.
      * apply lt_is_in, succ_lt.
      * rewrite <-H1.
        apply function_maps_domain_to_range.
        rewrite H0.
        apply lt_is_in, succ_lt.
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
      auto using PA1_ω. }
    now rewrite Complement_classification, Singleton_classification in *.
  - apply cardinality_sym.
    set (f := functionify ω ω (λ x, x + 1)).
    destruct (function_construction ω (ω \ {0,0}) (λ x, f x))
      as [f' [H [H0 H1]]].
    { intros a H.
      unfold f.
      rewrite <-(setify_action _ _ H), functionify_action,
      Complement_classification, Singleton_classification.
      split; auto using elts_in_set.
      intros H0.
      rewrite add_1_r in H0.
      now apply set_proj_injective, eq_sym, PA4 in H0. }
    exists f'.
    repeat split; unfold f in *; auto.
    + apply Injective_classification.
      intros x y H2 H3 H4.
      rewrite H, ? H1, <-(setify_action _ _ H2), <-(setify_action _ _ H3),
      ? functionify_action in *; auto.
      rewrite ? (add_comm _ 1) in H4.
      apply set_proj_injective, cancellation_add in H4.
      now inversion H4.
    + apply Surjective_classification.
      intros y H2.
      rewrite H0, H, Complement_classification, Singleton_classification in *.
      destruct H2 as [H2 H3].
      rewrite <-(setify_action _ _ H2).
      set (γ := exist _ _ H2 : N) in *.
      assert (γ ≠ 0) by (contradict H3; now inversion H3).
      exists (γ - 1).
      rewrite H1, functionify_action; repeat split; auto using N_in_ω.
      apply f_equal.
      apply succ_0 in H4 as [m H4].
      rewrite add_comm, sub_abab; auto.
      exists m.
      now rewrite H4, <-add_1_r, add_comm.
Qed.

Definition finite S := ∃ n : N, S ~ n.

Definition infinite S := ¬ finite S.

Theorem naturals_are_finite : ∀ n : N, finite n.
Proof.
  intros n.
  exists n.
  auto using cardinality_refl.
Qed.

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
    absurd (f z ∈ n).
    + intros H11.
      rewrite <-H8 in H11.
      apply Specify_classification in H11 as [H11 [s [H12 H13]]].
      rewrite Injective_classification in H2.
      apply H2 in H13; rewrite H0, H13 in *; auto.
    + rewrite <-H1.
      apply function_maps_domain_to_range.
      congruence.
  - rewrite <-H, <-H5 at 1.
    destruct (function_construction
                S {x in n | ∃ s : set, s ∈ S ∧ x = f s} (λ x, f x))
      as [f' [H8 [H9 H10]]].
    { intros a H8.
      apply Specify_classification.
      split; eauto.
      rewrite <-H1.
      apply function_maps_domain_to_range.
      rewrite H0.
      auto. }
    exists f'.
    repeat split; auto.
    + rewrite Injective_classification in *.
      intros x y H11 H12 H13.
      rewrite ? H10 in H13; try congruence.
      apply H2; auto; rewrite H0, H8 in *; auto.
    + rewrite Surjective_classification.
      intros y H11.
      rewrite H9 in H11.
      apply Specify_classification in H11 as [H11 [s [H12 H13]]].
      rewrite <-H8 in H12.
      exists s.
      split; auto.
      rewrite H10; congruence.
Qed.

Theorem natural_cardinality_uniqueness : ∀ m n : N, m ~ n → m = n.
Proof.
  intros m n H.
  apply NNPP.
  intros H0.
  destruct (lt_trichotomy m n) as [H1 | [H1 | H1]]; auto; rewrite lt_is_in in *.
  - apply (proper_subsets_of_natural_numbers m n); repeat split; intuition.
    + apply elements_of_naturals_are_subsets; eauto using elts_in_set.
    + contradict H0; now apply set_proj_injective.
  - apply (proper_subsets_of_natural_numbers n m); repeat split; intuition.
    + apply elements_of_naturals_are_subsets; eauto using elts_in_set.
    + contradict H0; now apply set_proj_injective.
Qed.

Theorem finite_cardinality_uniqueness : ∀ S, finite S → exists ! n : N, S ~ n.
Proof.
  intros S [n H].
  exists n.
  split; auto.
  intros x H0.
  apply natural_cardinality_uniqueness.
  now rewrite <-H, <-H0.
Qed.

Definition finite_cardinality : set → N.
Proof.
  intros S.
  destruct (excluded_middle_informative (finite S)).
  - apply finite_cardinality_uniqueness in f.
    destruct (constructive_definite_description _ f) as [n H].
    exact n.
  - exact 0.
Defined.

Notation " # E " := (finite_cardinality E) (at level 45) : set_scope.

Add Morphism finite with signature equinumerous ==> iff as finiteness_equiv.
Proof.
  intros x y H.
  split; intros [n H0]; exists n.
  - now rewrite <-H.
  - now rewrite H.
Qed.

Add Morphism finite_cardinality with signature
    equinumerous ==> eq as finite_cardinality_equiv.
Proof.
  intros x y H.
  destruct (classic (finite x)).
  - unfold finite_cardinality.
    repeat destruct excluded_middle_informative; rewrite ? H in *; try tauto.
    repeat destruct constructive_definite_description.
    apply natural_cardinality_uniqueness.
    now rewrite <-e, <-e0.
  - unfold finite_cardinality.
    repeat destruct excluded_middle_informative; try tauto;
      now rewrite H in *.
Qed.

Theorem card_of_natural : ∀ n : N, # n = n.
Proof.
  intros n.
  unfold finite_cardinality.
  destruct excluded_middle_informative; try tauto.
  - destruct constructive_definite_description.
    now apply natural_cardinality_uniqueness.
  - contradiction (naturals_are_finite n).
Qed.

Theorem equivalence_to_card : ∀ S (n : N), S ~ n → # S = n.
Proof.
  intros S n H.
  rewrite H.
  apply card_of_natural.
Qed.

Theorem equivalence_to_bijection : ∀ S (n : N),
    finite S → # S = n → ∃ f, domain f = S ∧ range f = n ∧ bijective f.
Proof.
  intros S n H H0.
  unfold finite_cardinality in H0.
  destruct excluded_middle_informative as [H1 | H1]; try tauto.
  destruct constructive_definite_description as [k [f [H2 [H3 H4]]]].
  subst; eauto.
Qed.

Lemma subset_equinumerosity :
  ∀ A B C D, A ~ B → B ⊂ C → C ~ D → ∃ E, E ⊂ D ∧ A ~ E.
Proof.
  intros A B C D [f [H [H0 [H1 H2]]]] H3 [g [H4 [H5 [H6 H7]]]].
  exists ({d in D | ∃ a, a ∈ A ∧ g (f a) = d}).
  split.
  - intros d H8.
    apply Specify_classification in H8; tauto.
  - destruct (function_construction
                A {d in D | ∃ a : set, a ∈ A ∧ g (f a) = d} (λ x, g (f x)))
      as [h [H8 [H9 H10]]].
    { intros a H8.
      apply Specify_classification.
      split; eauto.
      rewrite <-H5.
      apply function_maps_domain_to_range.
      rewrite H4.
      apply H3.
      rewrite <-H0.
      apply function_maps_domain_to_range.
      congruence. }
    exists h.
    repeat split; auto.
    + rewrite Injective_classification in *.
      intros x y H11 H12 H13.
      rewrite ? H10 in *; try congruence; apply H6 in H13;
        try apply H1 in H13; auto; try congruence; rewrite H4; apply H3;
          rewrite <-H0; apply function_maps_domain_to_range; congruence.
    + rewrite Surjective_classification.
      intros y H11.
      rewrite H9 in H11.
      apply Specify_classification in H11 as [H11 [a [H12 H13]]].
      exists a.
      rewrite H10; repeat split; congruence.
Qed.

Theorem card_empty : # ∅ = 0.
Proof.
  now rewrite <-card_of_natural.
Qed.

Theorem empty_card : ∀ S, S ~ 0 → S = ∅.
Proof.
  intros S H.
  symmetry in H.
  destruct H as [f [H [H0 [H1 H2]]]].
  apply Extensionality.
  split; intros H3.
  - rewrite Surjective_classification, <-H0, H in *.
    apply H2 in H3 as [x [H3 H4]].
    contradiction (Empty_set_classification x).
  - contradiction (Empty_set_classification z).
Qed.

Theorem card_equiv : ∀ S, finite S → # S ~ S.
Proof.
  intros S H.
  unfold finite_cardinality.
  destruct excluded_middle_informative; try tauto.
  destruct constructive_definite_description.
  now symmetry.
Qed.

Lemma finite_subsets_precursor :
  ∀ E F, finite F → E ⊂ F → ∃ n : N, E ~ n ∧ n ≤ # F.
Proof.
  intros E F H H0.
  destruct (classic (E = F)) as [| H1]; subst.
  { exists (# F).
    eauto using cardinality_sym, card_equiv, le_refl. }
  assert (E ⊊ F) as H2 by (split; auto).
  destruct H as [n H].
  pose proof H as H3.
  destruct H3 as [f [H3 [H4 H5]]].
  destruct (cardinality_of_subsets_of_n {y in n | ∃ x, x ∈ E ∧ f x = y} n)
    as [n' [H6 [g [H7 [H8 H9]]]]].
  { split.
    - intros x H6.
      apply Specify_classification in H6 as [H6 [z [H7 H8]]].
      rewrite <-H4, <-H8.
      apply function_maps_domain_to_range.
      subst; auto.
    - intros H6.
      destruct (proper_subset_inhab _ _ H2) as [x [H7 H8]].
      contradict H8.
      rewrite <-H3 in H7.
      apply function_maps_domain_to_range in H7 as H8.
      rewrite H4, <-H6 in H8.
      apply Specify_classification in H8 as [H8 [z [H9 H10]]].
      destruct H5 as [H5].
      rewrite Injective_classification, <-H3 in *.
      apply H5 in H10; subst; auto. }
  exists n'.
  split.
  2: { eapply lt_le_trans; eauto.
       replace n with (# F); auto using le_refl, equivalence_to_card. }
  apply (cardinality_trans _ (domain g)).
  - destruct (function_construction E (domain g) (λ x, f x))
      as [f' [H10 [H11 H12]]].
    { intros a H10.
      rewrite H7.
      apply Specify_classification.
      split; eauto.
      rewrite <-H4.
      apply function_maps_domain_to_range.
      subst; auto. }
    exists f'.
    destruct H5 as [H5 H13].
    repeat split; auto.
    + rewrite Injective_classification in *.
      intros x y H14 H15 H16.
      rewrite ? H12 in H16; try congruence.
      apply H5; subst; auto.
    + rewrite Surjective_classification in *.
      intros y H14.
      rewrite H11, H7, <-H4, Specify_classification in H14.
      destruct H14 as [H14 [x [H15 H16]]].
      exists x.
      rewrite H12; repeat split; congruence.
  - now exists g.
Qed.

Theorem subsets_of_finites_are_finite : ∀ E F, finite F → E ⊂ F → finite E.
Proof.
  intros E F H H0.
  apply finite_subsets_precursor in H0 as [n [H0 H1]]; eauto.
  now exists n.
Qed.

Theorem finite_subsets : ∀ E F, finite F → E ⊂ F → # E ≤ # F.
Proof.
  intros E F H H0.
  apply subsets_of_finites_are_finite in H0 as H1; auto.
  apply finite_subsets_precursor in H0 as [n [H0 H2]]; auto.
  replace (# E) with n; auto using eq_sym, equivalence_to_card.
Qed.

Theorem naturals_sum_diff : ∀ n m, (m + n) \ m ~ n.
Proof.
  intros n m.
  induction n using Induction.
  - replace ((m + 0) \ m) with ∅; auto using cardinality_refl.
    apply Extensionality.
    split; intros H.
    + contradiction (Empty_set_classification z).
    + now rewrite add_0_r, Complement_classification in H.
  - rewrite add_succ_r.
    destruct IHn as [f [H [H0 [H1 H2]]]].
    destruct
      (function_construction
         (S (m + n) \ m) (S n)
         (λ x, if (excluded_middle_informative (x = m + n)) then n else (f x)))
      as [f' [H3 [H4 H5]]].
    { intros a H3.
      destruct excluded_middle_informative.
      - apply lt_is_in, succ_lt.
      - rewrite <-S_is_succ in *.
        apply Pairwise_union_classification.
        left.
        rewrite <-H0.
        apply function_maps_domain_to_range.
        rewrite H, Complement_classification in *.
        split; try tauto.
        destruct H3 as [H3].
        apply Pairwise_union_classification in H3 as [H3 | H3]; auto.
        now apply Singleton_classification in H3. }
    exists f'.
    assert (∀ z, z ∈ domain f' → z ≠ m + n → z ∈ domain f) as H6.
    { intros z H6 H7.
      rewrite H, H3, <-S_is_succ, Complement_classification in *.
      destruct H6 as [H6].
      apply Pairwise_union_classification in H6 as [H6 | H6]; auto.
      now apply Singleton_classification in H6. }
    repeat split; auto.
    + rewrite Injective_classification in *.
      intros x y H7 H8 H9.
      rewrite ? H5 in H9; try congruence.
      repeat destruct excluded_middle_informative; try congruence; auto;
        contradiction (no_quines n);
        [ rewrite H9, <-H0 at 1 | rewrite <-H9, <-H0 at 1 ];
        auto using function_maps_domain_to_range.
    + rewrite Surjective_classification in *.
      intros y H7.
      rewrite H4, <-S_is_succ in H7.
      apply Pairwise_union_classification in H7 as [H7 | H7].
      * rewrite <-H0 in H7.
        apply H2 in H7 as [x [H7 H8]].
        exists x.
        split.
        -- rewrite <-S_is_succ, H, H3, Complement_classification in *.
           split; try tauto.
           destruct H7 as [H7].
           now apply subset_succ.
        -- rewrite H5.
           ++ destruct excluded_middle_informative; auto.
              subst.
              rewrite H, Complement_classification in H7.
              contradiction (no_quines (m+n)); tauto.
           ++ rewrite H, Complement_classification, <-S_is_succ in *.
              split; try tauto.
              destruct H7 as [H7].
              apply Pairwise_union_classification; tauto.
      * apply Singleton_classification in H7.
        subst.
        exists (m+n).
        assert (m+n ∈ domain f') as H7.
        { rewrite H3, Complement_classification, <-S_is_succ.
          split.
          - apply Pairwise_union_classification.
            rewrite Singleton_classification.
            tauto.
          - intros H7.
            destruct (classic (n = 0)).
            + subst.
              rewrite add_0_r in H7.
              contradiction (no_quines m).
            + apply lt_is_in, le_not_gt in H7; auto.
              now exists n. }
        split; auto.
        rewrite H5.
        -- destruct excluded_middle_informative; intuition.
        -- now rewrite <-H3.
Qed.

Theorem finite_union_equinumerosity : ∀ E F,
    finite E → finite F → E ∩ F = ∅ → (E ∪ F) ~ # E + # F.
Proof.
  intros E F [n H] [m H0] H1.
  rewrite (equivalence_to_card E n); auto.
  rewrite (equivalence_to_card F m); auto.
  pose proof (naturals_sum_diff m n).
  symmetry in H, H0 |-*.
  pose proof H as [f [H3 [H4 [H5 H6]]]].
  pose proof H0 as [g [H7 [H8 [H9 H10]]]].
  pose proof H2 as [h [H11 [H12 [H13 H14]]]].
  destruct (function_construction
              (n + m) (E ∪ F)
              (λ x, if (excluded_middle_informative (x ∈ n))
                    then (f x) else (g (h x)))) as [f' [H15 [H16 H17]]].
  { intros a H15.
    destruct excluded_middle_informative;
      apply Pairwise_union_classification.
    - left.
      rewrite <-H4.
      apply function_maps_domain_to_range.
      congruence.
    - right.
      rewrite <-H8.
      apply function_maps_domain_to_range.
      rewrite H7, <-H12.
      apply function_maps_domain_to_range.
      now rewrite H11, Complement_classification. }
  exists f'.
  repeat split; auto.
  - rewrite Injective_classification in *.
    intros x y H18 H19 H20.
    rewrite ? H17 in H20; try congruence.
    repeat destruct excluded_middle_informative.
    + apply H5; congruence.
    + contradiction (Empty_set_classification (f x)).
      rewrite <-H1.
      apply Pairwise_intersection_classification.
      split.
      * rewrite <-H4.
        apply function_maps_domain_to_range.
        congruence.
      * rewrite H20, <-H8.
        apply function_maps_domain_to_range.
        rewrite H7, <-H12.
        apply function_maps_domain_to_range.
        rewrite H11, Complement_classification.
        split; congruence.
    + contradiction (Empty_set_classification (f y)).
      rewrite <-H1.
      apply Pairwise_intersection_classification.
      split.
      * rewrite <-H4.
        apply function_maps_domain_to_range.
        congruence.
      * rewrite <-H20, <-H8.
        apply function_maps_domain_to_range.
        rewrite H7, <-H12.
        apply function_maps_domain_to_range.
        rewrite H11, Complement_classification.
        split; congruence.
    + apply H13;
        try (rewrite H11, Complement_classification; split; congruence).
      apply H9; auto;
        rewrite H7, <-H12;
        apply function_maps_domain_to_range;
        rewrite H11, Complement_classification;
        split; congruence.
  - rewrite Surjective_classification in *.
    intros y H18.
    rewrite H16, <-H4, <-H8 in *.
    apply Pairwise_union_classification in H18 as [H18 | H18].
    + apply H6 in H18 as [x [H18 H19]].
      assert (n ⊂ n + m).
      { apply le_is_subset.
        now exists m. }
      exists x.
      split.
      * rewrite H3, H15 in *; auto.
      * rewrite H17; try destruct excluded_middle_informative; auto;
          try congruence.
        rewrite H3 in *; auto.
    + apply H10 in H18 as [z [H18 H19]].
      rewrite H7, <-H12 in H18.
      apply H14 in H18 as [x [H20 H21]].
      exists x.
      split.
      * rewrite H15, H11 in *.
        now apply Complement_classification in H20 as [H20].
      * rewrite H17; try destruct excluded_middle_informative; auto;
          try congruence; rewrite H11, Complement_classification in H20; tauto.
Qed.

Theorem finite_union_cardinality : ∀ E F,
    finite E → finite F → E ∩ F = ∅ → # (E ∪ F) = # E + # F.
Proof.
  eauto using equivalence_to_card, finite_union_equinumerosity.
Qed.

Theorem finite_disjoint_unions_are_finite : ∀ E F,
    finite E → finite F → E ∩ F = ∅ → finite (E ∪ F).
Proof.
  intros E F H H0 H1.
  exists (# E + # F).
  eauto using finite_union_equinumerosity.
Qed.

Theorem singleton_card_1 : ∀ x, {x,x} ~ 1.
Proof.
  intros x.
  destruct (function_construction {x,x} 1 (λ x, 0)) as [f [H [H0 H1]]].
  { intros a H.
    apply lt_is_in, succ_lt. }
  exists f.
  repeat split; auto.
  - rewrite Injective_classification.
    intros a b H2 H3 H4.
    rewrite H, Singleton_classification in *.
    congruence.
  - rewrite Surjective_classification.
    intros y H2.
    exists x.
    split.
    + now rewrite H, Singleton_classification.
    + rewrite H1; try now apply Singleton_classification.
      unfold one in *.
      rewrite H0, <-S_is_succ in H2.
      apply Pairwise_union_classification in H2 as [H2 | H2].
      * contradiction (Empty_set_classification y).
      * now rewrite Singleton_classification in H2.
Qed.

Theorem singletons_are_finite : ∀ x, finite {x,x}.
Proof.
  intros x.
  exists 1.
  apply singleton_card_1.
Qed.

Lemma singleton_times_natural_equiv_natural : ∀ n m : N, ({n,n} × m ~ m).
Proof.
  intros n m.
  apply cardinality_sym.
  destruct (function_construction m ({n,n} × m) (λ x, (n,x)))
    as [f [H [H0 H1]]].
  { intros a H.
    apply Product_classification.
    exists n, a.
    now rewrite Singleton_classification. }
  exists f.
  repeat split; auto.
  - rewrite Injective_classification.
    intros x y H2 H3 H4.
    rewrite ? H1 in H4; try congruence.
    now apply Ordered_pair_iff in H4.
  - rewrite Surjective_classification.
    intros y H2.
    rewrite H0 in H2.
    apply Product_classification in H2 as [a [b [H2 [H3 H4]]]].
    exists b.
    split; try congruence.
    rewrite H1; auto.
    rewrite H4, Singleton_classification in *.
    now apply Ordered_pair_iff.
Qed.

Lemma singleton_times_natural_is_finite : ∀ n m : N, finite ({n,n} × m).
Proof.
  intros n m.
  exists m.
  auto using singleton_times_natural_equiv_natural.
Qed.

Lemma singleton_times_m_card : ∀ n m : N, # ({n,n} × m) = m.
Proof.
  intros n m.
  apply equivalence_to_card, singleton_times_natural_equiv_natural.
Qed.

Theorem natural_products_are_finite : ∀ n m : N, finite (n × m).
Proof.
  intros n m.
  induction n using Induction.
  - rewrite Empty_product_left.
    exists 0.
    apply cardinality_refl.
  - rewrite <-S_is_succ.
    unfold succ.
    rewrite Product_union_distr_l.
    apply finite_disjoint_unions_are_finite;
      auto using singleton_times_natural_is_finite.
    now rewrite <-Product_intersection, disjoint_succ, Empty_product_left.
Qed.

Theorem finite_empty : ∀ S, finite S → # S = 0 → S = ∅.
Proof.
  intros S H H0.
  apply empty_card.
  apply card_equiv in H.
  now rewrite H0 in H.
Qed.

Theorem singleton_card : ∀ n, # {n,n} = 1.
Proof.
  intros n.
  apply equivalence_to_card, singleton_card_1.
Qed.

Theorem natural_prod_card : ∀ n m : N, # (n × m) = (# n) * (# m).
Proof.
  intros n m.
  induction n using Induction.
  - now rewrite Empty_product_left, card_empty, ? card_of_natural, mul_0_l.
  - rewrite <-S_is_succ.
    unfold succ.
    rewrite Product_union_distr_l, ? finite_union_cardinality, IHn, mul_distr_r,
    singleton_times_m_card, ? card_of_natural, singleton_card, mul_1_l;
      auto using naturals_are_finite, natural_products_are_finite,
      singletons_are_finite, singleton_times_natural_is_finite, disjoint_succ.
    now rewrite <-Product_intersection, disjoint_succ, Empty_product_left.
Qed.

Theorem Inclusion_Exclusion : ∀ E F,
    finite E → finite F → # (E ∪ F) + # (E ∩ F) = # E + # F.
Proof.
  intros E F H H0.
  rewrite disjoint_union_complement, finite_union_cardinality, <-add_assoc,
  <-finite_union_cardinality, complement_union_intersection;
    eauto using disjoint_intersection_complement, complement_subset,
    subsets_of_finites_are_finite, complement_disjoint_intersection,
    Intersection_left.
Qed.

Theorem finite_unions_are_finite : ∀ E F, finite E → finite F → finite (E ∪ F).
Proof.
  intros E F H H0.
  rewrite disjoint_union_complement.
  apply finite_disjoint_unions_are_finite;
    eauto using disjoint_intersection_complement, complement_subset,
    subsets_of_finites_are_finite.
Qed.

Theorem finite_union_card_bound : ∀ E F, # (E ∪ F) ≤ # E + # F.
Proof.
  intros E F.
  destruct (classic (finite E))
    as [H | H], (classic (finite F)) as [H0 | H0];
  try (now rewrite <-Inclusion_Exclusion; unfold le; eauto);
  unfold finite_cardinality at 1; destruct excluded_middle_informative;
    auto using zero_le; exfalso;
      eauto using subsets_of_finites_are_finite, Union_right, Union_left.
Qed.

Add Morphism product with signature
    equinumerous ==> equinumerous ==> equinumerous as product_equiv.
Proof.
  intros E n H F m H0.
  destruct H as [f [H [H1 [H2 H3]]]], H0 as [g [H0 [H4 [H5 H6]]]].
  destruct (function_construction
              (E × F) (n × m)
              (λ z, (f (proj1 E F z), g (proj2 E F z)))) as [h [H7 [H8 H9]]].
  { intros z H7.
    apply Product_classification in H7 as [a [b [H7 [H8 H9]]]].
    subst.
    rewrite proj1_eval, proj2_eval; auto.
    apply Product_classification.
    exists (f a), (g b).
    repeat split; auto; rewrite <-? H1, <-? H4;
      now apply function_maps_domain_to_range. }
  exists h.
  repeat split; auto.
  - rewrite Injective_classification in *.
    intros x y H10 H11 H12.
    rewrite ? H9, H7 in *; try congruence.
    apply Product_classification in H10 as [a [b [H10 [H13 H14]]]].
    apply Product_classification in H11 as [c [d [H11 [H15 H16]]]].
    subst.
    rewrite ? proj1_eval, ? proj2_eval, Ordered_pair_iff in *; intuition.
  - rewrite Surjective_classification in *.
    intros y H10.
    rewrite H8, Product_classification in H10.
    destruct H10 as [a [b [H10 [H11 H12]]]].
    subst.
    apply H3 in H10 as [x [H10 H12]].
    apply H6 in H11 as [y [H11 H13]].
    exists (x,y).
    split.
    + rewrite H7, Product_classification; eauto.
    + rewrite H9, proj1_eval, proj2_eval, Ordered_pair_iff; auto.
      apply Product_classification; eauto.
Qed.

Theorem finite_products_are_finite :
  ∀ E F, finite E → finite F → finite (E × F).
Proof.
  intros E F [n H] [m H0].
  rewrite H, H0.
  apply natural_products_are_finite.
Qed.

Theorem finite_products_card :
  ∀ E F, finite E → finite F → # (E × F) = (# E) * (# F).
Proof.
  intros E F [n H] [m H0].
  now rewrite H, H0, natural_prod_card.
Qed.

Theorem power_union_r : ∀ A B C, B ∩ C = ∅ → A ^ (B ∪ C) ~ A ^ B × A ^ C.
Proof.
  assert (∀ A B C z, z ∈ A ^ (B ∪ C) →
                     {x in z | proj1 (B ∪ C) A x ∈ B} ∈ A ^ B) as Z.
  { intros A B C z H.
    apply Specify_classification in H as [H [H0 H1]].
    apply Specify_classification.
    rewrite Powerset_classification.
    assert ({x in z | proj1 (B ∪ C) A x ∈ B} ⊂ B × A).
    { intros x H2.
      apply Specify_classification in H2 as [H2 H3].
      apply H0, Product_classification in H2 as [b [a [H2 [H4 H5]]]].
      subst.
      rewrite proj1_eval, Product_classification in *; eauto. }
    repeat split; auto.
    intros x H3.
    destruct (H1 x) as [y [[H4 H5] H6]];
      try (apply Pairwise_union_classification; tauto).
    exists y.
    repeat split; auto.
    + rewrite Specify_classification, proj1_eval; auto.
      apply Pairwise_union_classification; tauto.
    + intros x' [H7 H8].
      rewrite Specify_classification in H8.
      intuition. }
  intros A B C H.
  destruct (function_construction
              (A ^ (B ∪ C)) (A ^ B × A ^ C)
              (λ z, ({x in z | proj1 (B ∪ C) A x ∈ B},
                     {x in z | proj1 (B ∪ C) A x ∈ C})))
    as [f [H0 [H1 H2]]].
  { intros z H0.
    apply Product_classification.
    exists {x in z | proj1 (B ∪ C) A x ∈ B}, {x in z | proj1 (B ∪ C) A x ∈ C}.
    repeat split; auto.
    rewrite Union_comm in *; auto. }
  exists f.
  repeat split; auto.
  - rewrite Injective_classification.
    intros u v H3 H4 H5.
    rewrite ? H2 in H5; try congruence.
    apply Extensionality.
    rewrite H0 in *.
    apply Specify_classification in H3 as [H3 _].
    apply Specify_classification in H4 as [H4 _].
    rewrite Powerset_classification in *.
    apply Ordered_pair_iff in H5 as [H5 H6].
    split; intros H7.
    + pose proof H7 as H8.
      apply H3, Product_classification in H8 as [y [x [H8 [H9 H10]]]].
      apply Pairwise_union_classification in H8 as [H8 | H8].
      * assert (z ∈ {x in v | proj1 (B ∪ C) A x ∈ B}) as H11.
        { rewrite <-H5.
          apply Specify_classification.
          subst.
          rewrite proj1_eval; auto.
          apply Pairwise_union_classification; auto. }
        apply Specify_classification in H11; tauto.
      * assert (z ∈ {x in v | proj1 (B ∪ C) A x ∈ C}) as H11.
        { rewrite <-H6.
          apply Specify_classification.
          subst.
          rewrite proj1_eval; auto.
          apply Pairwise_union_classification; auto. }
        apply Specify_classification in H11; tauto.
    + pose proof H7 as H8.
      apply H4, Product_classification in H8 as [y [x [H8 [H9 H10]]]].
      apply Pairwise_union_classification in H8 as [H8 | H8].
      * assert (z ∈ {x in u | proj1 (B ∪ C) A x ∈ B}) as H11.
        { rewrite H5.
          apply Specify_classification.
          subst.
          rewrite proj1_eval; auto.
          apply Pairwise_union_classification; auto. }
        apply Specify_classification in H11; tauto.
      * assert (z ∈ {x in u | proj1 (B ∪ C) A x ∈ C}) as H11.
        { rewrite H6.
          apply Specify_classification.
          subst.
          rewrite proj1_eval; auto.
          apply Pairwise_union_classification; auto. }
        apply Specify_classification in H11; tauto.
  - rewrite Surjective_classification.
    intros y H3.
    rewrite H1, Product_classification in H3.
    destruct H3 as [u [v [H3 [H4 H5]]]].
    exists (u ∪ v).
    apply Specify_classification in H3 as [H3 [H6 H7]].
    apply Specify_classification in H4 as [H4 [H8 H9]].
    assert (u ∪ v ∈ A ^ (B ∪ C)) as H10.
    { apply Specify_classification.
      rewrite Powerset_classification.
      assert (u ∪ v ⊂ (B ∪ C) × A) as H10.
      { intros z H10.
        apply Pairwise_union_classification in H10 as [H10 | H10].
        + apply H6 in H10 as H11.
           apply Product_classification in H11 as [b [a [H11 [H12 H13]]]].
           apply Product_classification.
           exists b, a.
           repeat split; auto.
           apply Pairwise_union_classification; auto.
        + apply H8 in H10 as H11.
           apply Product_classification in H11 as [b [a [H11 [H12 H13]]]].
           apply Product_classification.
           exists b, a.
           repeat split; auto.
           apply Pairwise_union_classification; auto. }
      repeat split; auto.
      intros a H11.
      apply Pairwise_union_classification in H11 as [H11 | H11].
      - apply H7 in H11 as [z [[H11 H12] H13]].
        exists z.
        repeat split; auto.
        + apply Pairwise_union_classification; auto.
        + intros x' [H14 H15].
          apply H13.
          apply Pairwise_union_classification in H15 as [H15 | H15];
            try tauto.
          contradiction (Empty_set_classification a).
          rewrite <-H.
          apply Pairwise_intersection_classification.
          apply H6, Product_classification in H12 as [c [d [H12 [H16 H17]]]].
          apply H8, Product_classification in H15 as [e [g [H15 [H18 H19]]]].
          rewrite Ordered_pair_iff in *.
          intuition; subst; auto.
      - apply H9 in H11 as [z [[H11 H12] H13]].
        exists z.
        repeat split; auto.
        + apply Pairwise_union_classification; auto.
        + intros x' [H14 H15].
          apply H13.
          apply Pairwise_union_classification in H15 as [H15 | H15];
            try tauto.
          contradiction (Empty_set_classification a).
          rewrite <-H.
          apply Pairwise_intersection_classification.
          apply H8, Product_classification in H12 as [c [d [H12 [H16 H17]]]].
          apply H6, Product_classification in H15 as [e [g [H15 [H18 H19]]]].
          rewrite Ordered_pair_iff in *.
          intuition; subst; auto. }
    repeat split; try congruence.
    rewrite H2; subst; auto.
    enough (∀ X Y W a b : set, Y ∩ W = ∅ → a ⊂ Y × X → b ⊂ W × X →
                               a = {x in a ∪ b | proj1 (Y ∪ W) X x ∈ Y}).
    { replace {x in u ∪ v | proj1 (B ∪ C) A x ∈ B} with u; auto.
      replace {x in u ∪ v | proj1 (B ∪ C) A x ∈ C} with v;
        rewrite (Union_comm B C), Union_comm, Intersection_comm in *; auto. }
    clear.
    intros X Y W a b H H0 H1.
    apply Extensionality.
    split; intros H2.
    + apply Specify_classification.
      split.
      * apply Pairwise_union_classification; auto.
      * apply H0, Product_classification in H2 as [x [y [H2 [H3 H4]]]].
        subst.
        rewrite proj1_eval; auto.
        apply Pairwise_union_classification; tauto.
    + apply Specify_classification in H2 as [H2 H3].
      apply Pairwise_union_classification in H2 as [H2 | H2]; auto.
      contradiction (Empty_set_classification (proj1 (Y ∪ W) X z)).
      rewrite <-H, Pairwise_intersection_classification.
      split; auto.
      apply H1, Product_classification in H2 as [x [y [H2 [H4 H5]]]].
      subst.
      rewrite proj1_eval in *; auto;
        apply Pairwise_union_classification; auto.
Qed.

Theorem power_1_r : ∀ m n, m^{n,n} ~ m.
Proof.
  intros m n.
  symmetry.
  destruct (function_construction m (m^{n,n}) (λ x, {(n,x),(n,x)}))
    as [f [H [H0 H1]]].
  { intros a H.
    apply Specify_classification.
    rewrite Powerset_classification.
    assert ({(n,a),(n,a)} ⊂ {n,n} × m) as H0.
    { intros x H0.
      rewrite Singleton_classification, Product_classification in *.
      exists n, a.
      now rewrite Singleton_classification. }
    repeat split; auto.
    intros a' H1.
    apply Singleton_classification in H1.
    subst.
    exists a.
    repeat split; auto.
    - now apply Singleton_classification.
    - intros x' [H1 H2].
      now apply Singleton_classification, Ordered_pair_iff in H2. }
  exists f.
  repeat split; auto.
  - rewrite Injective_classification.
    intros x y H2 H3 H4.
    rewrite ? H1 in H4; try congruence.
    assert ((n,x) ∈ {(n,y),(n,y)}) as H5.
    { rewrite <-H4.
      now apply Singleton_classification. }
    now apply Singleton_classification, Ordered_pair_iff in H5.
  - rewrite Surjective_classification.
    intros y H2.
    rewrite H0 in H2.
    apply Specify_classification in H2 as [H2 [H3 H4]].
    destruct (H4 n) as [a [[H5 H6] H7]]; try now apply Singleton_classification.
    exists a.
    split; try congruence.
    rewrite H1; auto.
    apply Extensionality.
    split; intros H8; try (apply Singleton_classification in H8; congruence).
    apply H3 in H8 as H9.
    apply Product_classification in H9 as [c [d [H9 [H10 H11]]]].
    rewrite Singleton_classification, (H7 d) in *; subst; intuition.
Qed.

Theorem natural_powers_are_finite : ∀ m n : N, finite (m^n).
Proof.
  intros m n.
  induction n as [| n [x H]] using Induction.
  - rewrite power_0_r, <-(setify_action _ _ PA1_ω).
    apply (naturals_are_finite 1).
  - rewrite <-S_is_succ.
    unfold succ.
    rewrite power_union_r, H, power_1_r;
      auto using disjoint_succ, finite_products_are_finite, naturals_are_finite.
Qed.

Theorem natural_powers_card : ∀ m n : N, # (m^n) = ((# m)^(# n))%N.
Proof.
  intros m n.
  induction n using Induction.
  - now rewrite ? card_of_natural, power_0_r, pow_0_r, <-(card_of_natural 1).
  - rewrite <-S_is_succ.
    unfold succ.
    now rewrite power_union_r, finite_union_cardinality, singleton_card,
    pow_add_r, pow_1_r, power_1_r, finite_products_card, IHn;
      auto using naturals_are_finite, disjoint_succ, singletons_are_finite,
      natural_powers_are_finite.
Qed.

Add Morphism power with signature
    equinumerous ==> equinumerous ==> equinumerous as power_equiv.
Proof.
  intros A C [f [H [H0 [H1 H2]]]] B D [g [H3 [H4 [H5 H6]]]].
  rewrite Injective_classification, Surjective_classification in *.
  destruct (function_construction
              (A^B) (C^D)
              (λ S, {z in D × C | ∃ x, x ∈ S ∧ g (proj1 B A x) = proj1 D C z ∧
                                       f (proj2 B A x) = proj2 D C z}))
    as [h [H7 [H8 H9]]]; subst.
  { intros φ H.
    apply Specify_classification in H as [H [H0 H3]].
    apply Specify_classification.
    repeat split.
    - apply Powerset_classification.
      intros z H4.
      apply Specify_classification in H4.
      tauto.
    - intros z H4.
      apply Specify_classification in H4.
      tauto.
    - intros d H4.
      apply H6 in H4 as [x' [H4 H7]].
      apply H3 in H4 as [y [[H4 H8] H9]].
      exists (f y).
      assert (x' ∈ domain g) as H10.
      { apply H0 in H8.
        apply Product_classification in H8 as [a [b [H8 [H10 H11]]]].
        apply Ordered_pair_iff in H11 as [H11 H12].
        congruence. }
      repeat split.
      + now apply function_maps_domain_to_range.
      + apply function_maps_domain_to_range in H10 as H11.
        rewrite H7 in H11.
        apply function_maps_domain_to_range in H4 as H12.
        apply Specify_classification.
        repeat split.
        * apply Product_classification; eauto.
        * exists (x', y).
          repeat split; auto; rewrite ? proj1_eval, ? proj2_eval; auto.
      + intros z [H11 H12].
        apply Specify_classification in H12 as [H12 [x [H13 [H14 H15]]]].
        apply H0 in H13 as H16.
        apply Product_classification in H16 as [a [b [H16 [H17 H18]]]].
        subst.
        rewrite ? proj1_eval, ? proj2_eval in *; auto;
          try now apply function_maps_domain_to_range.
        apply H5 in H14; auto.
        subst.
        rewrite (H9 b); auto. }
  exists h.
  repeat split; auto.
  - rewrite Injective_classification.
    intros x y H H0 H3.
    rewrite ? H9 in H3; try congruence.
    pose proof H as H4.
    pose proof H0 as H10.
    rewrite H7 in H4, H10.
    apply Specify_classification in H4 as [H4 [H11 H12]].
    apply Specify_classification in H10 as [H10 [H13 H14]].
    apply Extensionality.
    split; intros H15.
    + apply H11 in H15 as H16.
      apply Product_classification in H16 as [a [b [H16 [H17 H18]]]].
      subst.
      assert
        ((g a, f b)
           ∈ {z in range g × range f | ∃ x0 : set,
                x0 ∈ x
                ∧ g (proj1 (domain g) (domain f) x0) =
                  proj1 (range g) (range f) z
                ∧ f (proj2 (domain g) (domain f) x0) =
                  proj2 (range g) (range f) z}) as H18.
      { apply Specify_classification.
        split.
        - apply Product_classification.
          exists (g a), (f b).
          repeat split; auto; now apply function_maps_domain_to_range.
        - exists (a, b).
          rewrite ? proj1_eval, ? proj2_eval; auto;
            now apply function_maps_domain_to_range. }
      rewrite H3 in H18.
      apply Specify_classification in H18 as [H18 [z [H19 [H20 H21]]]].
      apply H13 in H19 as H22.
      apply Product_classification in H22 as [a' [b' [H22 [H23 H24]]]].
      subst.
      rewrite ? proj1_eval, ? proj2_eval in *; auto;
        try now apply function_maps_domain_to_range.
      apply H1 in H21; apply H5 in H20; subst; auto.
    + apply H13 in H15 as H16.
      apply Product_classification in H16 as [a [b [H16 [H17 H18]]]].
      subst.
      assert
        ((g a, f b)
           ∈ {z in range g × range f | ∃ x0 : set,
                x0 ∈ y
                ∧ g (proj1 (domain g) (domain f) x0) =
                  proj1 (range g) (range f) z
                ∧ f (proj2 (domain g) (domain f) x0) =
                  proj2 (range g) (range f) z}) as H18.
      { apply Specify_classification.
        split.
        - apply Product_classification.
          exists (g a), (f b).
          repeat split; auto; now apply function_maps_domain_to_range.
        - exists (a, b).
          rewrite ? proj1_eval, ? proj2_eval; auto;
            now apply function_maps_domain_to_range. }
      rewrite <-H3 in H18.
      apply Specify_classification in H18 as [H18 [z [H19 [H20 H21]]]].
      apply H11 in H19 as H22.
      apply Product_classification in H22 as [a' [b' [H22 [H23 H24]]]].
      subst.
      rewrite ? proj1_eval, ? proj2_eval in *; auto;
        try now apply function_maps_domain_to_range.
      apply H1 in H21; apply H5 in H20; subst; auto.
  - rewrite Surjective_classification.
    intros y H.
    rewrite H8 in H.
    apply Specify_classification in H as [H [H0 H3]].
    exists {z in domain g × domain f |
             (g (proj1 (domain g) (domain f) z),
              f (proj2 (domain g) (domain f) z)) ∈ y}.
    split.
    + rewrite H7.
      apply Specify_classification.
      repeat split.
      * apply Powerset_classification.
        intros z H4.
        apply Specify_classification in H4; tauto.
      * intros z H4.
        apply Specify_classification in H4; tauto.
      * intros a H4.
        destruct (H3 (g a)) as [x [[H10 H11] H12]];
          try now apply function_maps_domain_to_range.
        apply H2 in H10 as [z [H10 H13]].
        exists z.
        repeat split; auto.
        -- rewrite Specify_classification, Product_classification.
           split; eauto.
           rewrite proj1_eval, proj2_eval, H13; auto.
        -- intros x' [H14 H15].
           apply Specify_classification in H15 as [H15 H16].
           rewrite proj1_eval, proj2_eval in H16; auto.
           destruct (H3 (g a)) as [y' [[H18 H19] H20]];
             try now apply function_maps_domain_to_range.
           assert (y' = f x').
           { apply H20.
             split; auto; now apply function_maps_domain_to_range. }
           assert (y' = f z).
           { apply H20.
             split; auto; try now apply function_maps_domain_to_range.
             now rewrite H13. }
           apply H1; try congruence.
    + rewrite H9.
      * apply Extensionality.
        split; intros H10.
        -- apply Specify_classification in H10 as [H10 [x [H11 [H12 H13]]]].
           apply Specify_classification in H11 as [H11 H14].
           rewrite H12, H13 in H14.
           apply Product_classification in H10 as [a [b [H10 [H15 H16]]]].
           subst.
           rewrite proj1_eval, proj2_eval in *; auto.
        -- apply Specify_classification.
           split; auto.
           apply H0 in H10 as H11.
           apply Product_classification in H11 as [a [b [H12 [H13 H14]]]].
           subst.
           apply H6 in H12 as [c [H12 H14]].
           apply H2 in H13 as [d [H15 H16]].
           subst.
           exists (c, d).
           repeat split;
             rewrite ? Specify_classification, ? Product_classification,
             ? proj1_eval, ? proj2_eval; repeat split; eauto;
               now apply function_maps_domain_to_range.
      * apply Specify_classification.
        repeat split.
        -- apply Powerset_classification.
           intros z H4.
           apply Specify_classification in H4; tauto.
        -- intros z H4.
           apply Specify_classification in H4; tauto.
        -- intros a H4.
           destruct (H3 (g a)) as [b [[H10 H11] H12]];
             try now apply function_maps_domain_to_range.
           apply H2 in H10 as [x [H10 H13]].
           exists x.
           subst.
           repeat split; auto.
           ++ rewrite Specify_classification, Product_classification,
              proj1_eval, proj2_eval; repeat split; eauto.
           ++ intros x' [H13 H14].
              apply Specify_classification in H14 as [H14 H16].
              apply H1; auto.
              apply H12.
              split; rewrite ? proj1_eval, ? proj2_eval in *; auto.
              now apply function_maps_domain_to_range.
Qed.

Theorem finite_powers_are_finite : ∀ E F, finite E → finite F → finite (E^F).
Proof.
  intros E F [n H] [m H0].
  rewrite H, H0; auto using natural_powers_are_finite.
Qed.

Theorem finite_power_card : ∀ E F, finite E → finite F → #(E^F) = ((#E)^(#F))%N.
Proof.
  intros E F [n H] [m H0].
  now rewrite H, H0, natural_powers_card.
Qed.

Definition bijection_set A B :=
  { f in P (A × B) |
    ∃ f', domain f' = A ∧ range f' = B ∧ graph f' = f ∧ bijective f'}.

Definition size_of_bijections A B := # (bijection_set A B).

Theorem equinumerous_cardinality : ∀ A B, A ~ B → # A = # B.
Proof.
  intros A B H.
  now rewrite H.
Qed.

Theorem finite_cardinality_equinumerous :
  ∀ A B, finite A → finite B → # A = # B → A ~ B.
Proof.
  intros A B H H0 H1.
  apply (card_equiv A) in H.
  apply (card_equiv B) in H0.
  now rewrite <-H, <-H0, H1.
Qed.

Definition inverse_function_out : set → set → set → set.
Proof.
  intros A B f.
  destruct (excluded_middle_informative (f ∈ bijection_set A B)).
  - apply Specify_classification in i as [H H0].
    destruct (constructive_indefinite_description _ H0)
      as [f' [H1 [H2 [H3 H4]]]].
    exact (graph (inverse f')).
  - exact ∅.
Defined.

Theorem bijection_set_sym :
  ∀ A B, bijection_set A B ~ bijection_set B A.
Proof.
  intros A B.
  destruct (function_construction
              (bijection_set A B) (bijection_set B A)
              (λ x, inverse_function_out A B x)) as [f [H [H0 H1]]].
  { intros a H.
    unfold inverse_function_out.
    destruct excluded_middle_informative; try tauto.
    destruct Specify_classification, a0.
    destruct constructive_indefinite_description as [g].
    repeat destruct a1.
    apply Specify_classification.
    split.
    - apply Powerset_classification.
      intros z H0.
      apply graph_elements_are_pairs in H0.
      rewrite inverse_domain, inverse_range in H0; congruence.
    - exists (inverse g).
      rewrite inverse_domain, inverse_range; auto using inverse_bijective. }
  exists f.
  repeat split; auto.
  - rewrite Injective_classification.
    intros x y H2 H3 H4.
    rewrite H in *.
    rewrite ? H1 in H4; auto.
    unfold inverse_function_out in H4.
    repeat destruct excluded_middle_informative; try tauto.
    repeat destruct Specify_classification.
    destruct a, a0.
    repeat destruct constructive_indefinite_description.
    repeat destruct a1, a2.
    rewrite <-e5, <-e6.
    replace x0 with x1; auto.
    rewrite <-(function_inv_inv x0), <-(function_inv_inv x1); auto.
    f_equal.
      apply function_record_injective; auto.
    rewrite ? inverse_range; congruence.
  - rewrite Surjective_classification.
    intros y H2.
    rewrite H0 in H2.
    unfold bijection_set in H2.
    apply Specify_classification in H2 as [H2 [g [H3 [H4 [H5 H6]]]]].
    exists (graph (inverse g)).
    assert (graph (inverse g) ∈ bijection_set A B) as H7.
    { unfold bijection_set.
      apply Specify_classification.
      split.
      - apply Powerset_classification.
        intros x H7.
        apply graph_elements_are_pairs in H7.
          rewrite inverse_domain, inverse_range in *; congruence.
      - exists (inverse g).
        rewrite inverse_domain, inverse_range; auto using inverse_bijective. }
    split; try now rewrite H.
    rewrite H1; auto.
    unfold inverse_function_out.
    destruct excluded_middle_informative; try tauto.
    destruct Specify_classification, a.
    destruct constructive_indefinite_description as [h].
    repeat destruct a0.
    rewrite <-H5.
    replace h with (inverse g).
    + rewrite function_inv_inv; auto.
    + apply function_record_injective; auto.
      rewrite inverse_range; congruence.
Qed.

Theorem size_of_bijections_sym :
  ∀ A B, size_of_bijections A B = size_of_bijections B A.
Proof.
  intros A B.
  apply equinumerous_cardinality, bijection_set_sym.
Qed.

Section inverse_function_sideload.

  Variable C : set.
  Variable f : function.
  Hypothesis H : bijective f.
  Variable x : set.
  Definition inverse_function_shift : set.
  Proof.
    destruct (excluded_middle_informative (x ∈ bijection_set (range f) C)).
    - apply Specify_classification in i as [H0 H1].
      destruct (constructive_indefinite_description _ H1)
        as [g [H2 [H3 [H4 H5]]]].
      exact (graph (g ∘ f)).
    - exact ∅.
  Defined.

  Lemma inverse_function_shift_in_A_C :
    x ∈ bijection_set (range f) C →
    inverse_function_shift ∈ bijection_set (domain f) C.
  Proof.
    intros H0.
    unfold inverse_function_shift.
    destruct excluded_middle_informative; try tauto.
    destruct Specify_classification.
    repeat destruct a.
    - apply Specify_classification.
      split; auto.
    - destruct constructive_indefinite_description.
      repeat destruct a.
      apply Specify_classification.
      destruct (Composition_classification x0 f) as [H3 [H4 H5]];
        try congruence.
      split.
      + apply Powerset_classification.
        intros z H6.
        apply graph_elements_are_pairs in H6.
        congruence.
      + exists (x0 ∘ f).
        destruct H, b.
        repeat split; try congruence.
        * apply composition_injective; auto; congruence.
        * apply composition_surjective; auto; congruence.
  Qed.

End inverse_function_sideload.

Lemma bijection_set_wf : ∀ A B C,
    A ~ B → bijection_set A C ~ bijection_set B C.
Proof.
  intros A B C [f [H [H0 H1]]].
  apply cardinality_sym.
  destruct (function_construction
              (bijection_set B C) (bijection_set A C)
              (λ x, inverse_function_shift C f x)) as [h [H2 [H3 H4]]].
  { intros G H2.
    rewrite <-H, <-H0 in *.
    now apply inverse_function_shift_in_A_C. }
  exists h.
  repeat split; auto.
  - rewrite Injective_classification.
    intros x y H5 H6 H7.
    subst.
    rewrite ? H4 in H7; try congruence.
    rewrite H2 in H5, H6.
    unfold inverse_function_shift in H7.
    repeat destruct excluded_middle_informative; try tauto.
    repeat destruct Specify_classification.
    destruct a, a0.
    repeat destruct constructive_indefinite_description.
    repeat destruct a1, a2.
    rewrite <-e5, <-e6.
    destruct (Composition_classification x0 f) as [H8 [H9 H10]]; try congruence.
    destruct (Composition_classification x1 f) as [H11 [H12 H13]];
      try congruence.
    assert (x0 ∘ f = x1 ∘ f) as H14.
    { apply function_record_injective; congruence. }
    replace x0 with x1; auto.
    apply func_ext; try congruence.
    intros z H15.
    pose proof H1 as [H16 H17].
    rewrite Surjective_classification in H17.
    destruct (H17 z) as [w [H18 H19]]; try congruence.
    subst.
    rewrite <-H10, <-H13, H14; auto.
  - rewrite Surjective_classification.
    intros y H5.
    rewrite H3 in H5.
    assert (bijective (inverse f)) as H6 by now apply inverse_bijective.
    exists (inverse_function_shift C (inverse f) y).
    split.
    { rewrite H2, <-H0, <-inverse_domain; auto.
      apply inverse_function_shift_in_A_C; auto.
      rewrite inverse_range; auto; congruence. }
    rewrite H4;
      try (rewrite <-H0, <-inverse_domain; auto;
           apply inverse_function_shift_in_A_C; auto;
           rewrite inverse_range; auto; congruence).
    unfold inverse_function_shift at 1.
    repeat destruct excluded_middle_informative;
    try (contradict n; rewrite <-inverse_domain; auto;
         apply inverse_function_shift_in_A_C; auto;
         rewrite inverse_range; auto; congruence).
    destruct Specify_classification, a, constructive_indefinite_description.
    repeat destruct a0.
    unfold inverse_function_shift in e2.
    destruct excluded_middle_informative;
      try now rewrite inverse_range, H in n.
    destruct Specify_classification, a0, constructive_indefinite_description.
    repeat destruct a1.
    rewrite <-e6.
    f_equal.
    destruct (Composition_classification x0 (inverse f)) as [H7 [H8 H9]];
      try congruence.
    destruct (Composition_classification x f) as [H10 [H11 H12]];
      try congruence.
    destruct (Composition_classification (x0 ∘ inverse f) f)
      as [H13 [H14 H15]]; try congruence.
    { now rewrite H7, inverse_domain. }
    replace x with (x0 ∘ inverse f).
    + apply func_ext; try congruence.
      * now rewrite H13, e4, inverse_range.
      * intros x1 H16.
        rewrite H15, H9, ? left_inverse; auto; try congruence.
        rewrite inverse_domain; auto.
        apply function_maps_domain_to_range.
        congruence.
    + apply function_record_injective; try congruence.
Qed.
  
Lemma size_of_bijections_wf : ∀ A B C,
    A ~ B → size_of_bijections A C = size_of_bijections B C.
Proof.
  intros A B C H.
  now apply equinumerous_cardinality, bijection_set_wf.
Qed.

Add Morphism bijection_set with signature
    equinumerous ==> equinumerous ==> equinumerous as bijection_set_equiv.
Proof.
  intros x y H x0 y0 H0.
  eapply (bijection_set_wf x y x0) in H.
  rewrite (bijection_set_sym y), (bijection_set_sym x) in *.
  eapply (bijection_set_wf x0 y0 y) in H0.
  now rewrite H, H0.
Qed.

Add Morphism size_of_bijections with signature
    equinumerous ==> equinumerous ==> eq as size_of_bijections_equiv.
Proof.
  intros x y H x0 y0 H0.
  eapply (size_of_bijections_wf x y x0) in H.
  rewrite (size_of_bijections_sym y), (size_of_bijections_sym x) in *.
  eapply (size_of_bijections_wf x0 y0 y) in H0.
  congruence.
Qed.

Lemma finite_subsets_bijective : ∀ E F, finite F → E ⊂ F → E ~ F → E = F.
Proof.
  intros E F H H0 H1.
  apply Subset_equality_iff.
  split; auto.
  apply equinumerous_cardinality in H1.
  apply Union_subset in H0 as H2.
  rewrite <-H2, disjoint_union_complement, finite_union_cardinality in H1;
    eauto using disjoint_intersection_complement,
    subsets_of_finites_are_finite, complement_subset.
  rewrite <-(add_0_r (# E)) in H1 at 1.
  apply naturals.cancellation_add, eq_sym in H1.
  assert (# (F \ E) ~ 0%N) as H3 by now rewrite H1.
  rewrite card_equiv in H3;
    eauto using subsets_of_finites_are_finite, complement_subset.
  apply empty_card in H3.
  intros x H4.
  apply NNPP.
  intros H5.
  contradiction (Empty_set_classification x).
  now rewrite <-H3, Complement_classification.
Qed.

Lemma finite_set_injection_is_bijection :
  ∀ f, finite (domain f) → domain f ~ range f → injective f → bijective f.
Proof.
  intros f H H0 H1.
  apply injective_into_image in H1 as H2.
  assert (image f = range f) as H3.
  { apply finite_subsets_bijective.
    - now rewrite <-H0.
    - apply image_subset_range.
    - now rewrite <-H2, H0. }
  split; auto.
  rewrite Surjective_classification.
  intros z H4.
  rewrite <-H3 in H4.
  apply Specify_classification in H4 as [H4 [x H5]].
  now (exists x).
Qed.

Section Powerset_powers.

  Variable X : set.

  Definition powerset_bijection_helper : elts (2^X) → elts (P X).
  Proof.
    intros [x H].
    apply Specify_classification in H as [H H0].
    set (f := mkFunc _ _ _ H0).
    assert ({x in X | f x = 1} ∈ P X).
    { apply Powerset_classification.
      intros z H1.
      apply Specify_classification in H1.
      tauto. }
    exact (exist _ _ H1).
  Defined.

  Theorem powerset_powers : 2^X ~ P X.
  Proof.
    exists (functionify _ _ powerset_bijection_helper).
    rewrite functionify_domain, functionify_range.
    repeat split; auto.
    - apply Injective_classification.
      intros x y H H0 H1.
      rewrite functionify_domain, <-(setify_action _ _ H),
      <-(setify_action _ _ H0), ? functionify_action in *.
      unfold powerset_bijection_helper in *.
      repeat destruct Specify_classification.
      destruct a, a0.
      simpl in H1 |-*.
      set (f := (mkFunc _ _ _ i2)).
      set (g := (mkFunc _ _ _ i4)).
      assert (x = graph f) as H2 by auto.
      assert (y = graph g) as H3 by auto.
      rewrite H2, H3.
      f_equal.
      apply func_ext; auto.
      intros z H4; simpl in H4.
      replace ({| domain := X; range := succ (succ ∅);
                  graph := x; func_hyp := i2 |}) with f in H1 by auto.
      replace ({| domain := X; range := succ (succ ∅);
                  graph := y; func_hyp := i4 |}) with g in H1 by auto.
      assert (f z ∈ range f) by now apply function_maps_domain_to_range.
      assert (g z ∈ range g) by now apply function_maps_domain_to_range.
      simpl in H5, H6.
      unfold succ in H5, H6, H1.
      rewrite Pairwise_union_classification, Union_comm, Union_empty,
      Singleton_classification in H5, H6.
      rewrite Union_comm, Union_empty in H1.
      destruct H5, H6; rewrite ? Singleton_classification in *; try congruence.
      + assert (z ∈ {x in X | g x = {∅,∅}}) as H7
            by now apply Specify_classification.
        rewrite <-H1 in H7.
        apply Specify_classification in H7 as [H7 H8].
        congruence.
      + assert (z ∈ {x in X | f x = {∅,∅}}) as H7
            by now apply Specify_classification.
        rewrite H1 in H7.
        apply Specify_classification in H7 as [H7 H8].
        congruence.
    - rewrite Surjective_classification.
      assert (1 ∈ 2) as Z.
      { now apply Pairwise_union_classification, or_intror,
        Singleton_classification. }
      assert (0 ∈ 2) as Z0.
      { now apply Pairwise_union_classification, or_introl,
        Pairwise_union_classification, or_intror, Singleton_classification. }
      intros y H.
      rewrite functionify_range, functionify_domain in *.
      exists {z in X × 2 | proj2 X 2 z = 1 ↔ proj1 X 2 z ∈ y}.
      assert ({z in X × 2 | proj2 X 2 z = 1 ↔ proj1 X 2 z ∈ y} ∈ 2 ^ X) as Z1.
      { apply Specify_classification.
        rewrite Powerset_classification.
        repeat split; intros z H0;
          try (apply Specify_classification in H0; tauto).
        exists (if (excluded_middle_informative (z ∈ y)) then 1 else 0).
        destruct excluded_middle_informative; split.
        - rewrite Specify_classification, proj1_eval, proj2_eval,
          Product_classification; repeat split; eauto.
        - intros x' [H1 H2].
          apply Specify_classification in H2 as [H2 H3].
          rewrite proj1_eval, proj2_eval in H3; intuition.
        - rewrite Specify_classification, proj1_eval, proj2_eval,
          Product_classification; repeat split; eauto; intros H1; try tauto.
          now apply set_proj_injective, neq_succ in H1.
        - intros x' [H1 H2].
          apply Specify_classification in H2 as [H2 H3].
          rewrite proj1_eval, proj2_eval in H3; intuition.
          apply Pairwise_union_classification in H1 as [H1 | H1].
          * unfold succ in H1.
            now rewrite Union_comm, Union_empty,
            Singleton_classification in H1.
          * rewrite Singleton_classification in H1.
            now apply H4 in H1. }
      split; auto.
      rewrite <-(setify_action _ _ Z1), functionify_action.
      unfold powerset_bijection_helper.
      destruct Specify_classification, a.
      simpl.
      clear a i.
      apply Extensionality.
      set (f := mkFunc _ _ _ i1).
      split; intros H0.
      + apply Specify_classification in H0 as [H0 H1].
        assert (f z = 1) as H2 by auto.
        apply function_maps_domain_to_graph in H2; simpl in H2 |-*; auto.
        apply Specify_classification in H2 as [H2 H3].
        rewrite proj1_eval, proj2_eval in H3; tauto.
      + apply Specify_classification.
        apply Powerset_classification in H.
        split; auto.
        assert (f z = 1); auto.
        apply function_maps_domain_to_graph; auto; simpl.
        apply Specify_classification.
        split.
        * apply Product_classification.
          exists z, 1.
          split; auto.
        * rewrite proj1_eval, proj2_eval; intuition.
  Qed.

End Powerset_powers.

Theorem powerset_finite : ∀ X, finite X → finite (P X).
Proof.
  intros X H.
  rewrite <-powerset_powers.
  auto using finite_powers_are_finite, naturals_are_finite.
Qed.

Theorem powerset_card : ∀ X, finite X → # P X = (2^(# X))%N.
Proof.
  intros X H.
  rewrite <-powerset_powers, finite_power_card, card_of_natural;
    auto using naturals_are_finite.
Qed.

Theorem complement_card : ∀ E F, E ⊂ F → finite E → # (F \ E) = # F - # E.
Proof.
  intros E F H H0.
  apply Union_subset in H as H1.
  destruct (classic (finite F)) as [H2 | H2].
  - rewrite <-H1 at 2.
    rewrite disjoint_union_complement, finite_union_cardinality,
    naturals.add_comm, sub_abba;
      eauto using subsets_of_finites_are_finite, complement_subset,
      disjoint_intersection_complement.
  - unfold finite_cardinality at 2.
    destruct excluded_middle_informative; try tauto.
    rewrite sub_0_l.
    unfold finite_cardinality.
    destruct excluded_middle_informative; auto.
    contradict n.
    rewrite <-H1, disjoint_union_complement.
    now apply finite_unions_are_finite.
Qed.

Theorem pairing_card : ∀ x y, x ≠ y → {x,y} ~ 2.
Proof.
  intros x y H.
  apply Pairing_intersection_disjoint in H.
  now rewrite Pairing_union_singleton, finite_union_equinumerosity,
  ? singleton_card, add_1_r; eauto using singletons_are_finite.
Qed.
