Require Export naturals Setoid.
Set Warnings "-notation-overridden".

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
    now replace y with (elt_to_set _ (exist _ _ H)).
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

Add Parametric Relation : set equinumerous
      reflexivity proved by (cardinality_refl)
      symmetry proved by (cardinality_sym)
      transitivity proved by (cardinality_trans) as set_equivalence.

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

Lemma two_sided_inverse_bijective : ∀ A B,
  (∃ (f : elts A → elts B) (g : elts B → elts A),
      ((∀ a : elts A, g (f a) = a) ∧ (∀ b : elts B, f (g b) = b))) → A ~ B.
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
    replace x with (elt_to_set _ (exist _ _ H1)) in * by auto.
    replace y with (elt_to_set _ (exist _ _ H2)) in * by auto.
    now rewrite ? H6, ? H3, ? H in H8.
  - rewrite Surjective_classification.
    intros y H1.
    exists (g' y).
    split.
    + rewrite H4.
      apply function_maps_domain_to_range.
      congruence.
    + rewrite H5 in H1.
      replace y with (elt_to_set _ (exist _ _ H1)) in * by auto.
      now rewrite H3, H6, H0.
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
      * apply Pairwise_union_classification.
        destruct (classic (z = n)) as [H9 | H9].
        -- right.
           now apply Singleton_classification.
        -- left.
           apply Complement_classification.
           now rewrite Singleton_classification.
      * apply Pairwise_union_classification in H8 as [H8 | H8].
        -- apply Complement_classification in H8; now (subst; intuition).
        -- apply Singleton_classification in H8; now (subst; intuition).
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
        apply Complement_classification in H7 as [H7 H8].
        now rewrite Singleton_classification in H8.
      * destruct H as [H H6].
        intros x H7.
        apply H in H7 as H8.
        rewrite <-S_is_succ in H8.
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
      replace a with (elt_to_set _ (exist _ _ H)) by auto.
      rewrite H2.
      apply Complement_classification.
      split; auto using elts_in_set.
      rewrite Singleton_classification.
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
        replace x with (elt_to_set _ (exist _ _ H2)) in * by auto.
        replace y with (elt_to_set _ (exist _ _ H3)) in * by auto.
        rewrite ? H7, ? (add_comm _ 1) in H4.
        apply set_proj_injective, cancellation_add in H4.
        now f_equal.
      * intros y.
        assert (y ∈ ω) as H2.
        { pose proof elts_in_set _ y as H2.
          simpl in H2.
          rewrite H0 in H2.
          apply Complement_classification in H2.
          tauto. }
        set (γ := (exist _ _ H2) : N).
        assert (γ ≠ 0) as H3.
        { intros H3.
          assert (γ ∈ ω \ {0,0}) as H4.
          { rewrite <-H0.
            unfold γ.
            simpl.
            auto using elts_in_set. }
          rewrite H3 in H4.
          apply Complement_classification in H4.
          rewrite Singleton_classification in H4.
          tauto. }
        apply succ_0 in H3 as [m H3].
        assert (m ∈ domain f') as H5.
        { rewrite H.
          eauto using elts_in_set. }
        exists (exist (λ x, x ∈ domain f') _ H5).
        simpl.
        apply set_proj_injective.
        simpl.
        replace (elt_to_set _ y) with (elt_to_set _ γ) by auto.
        rewrite H1; auto using N_in_ω.
        unfold f, functionify.
        destruct constructive_indefinite_description as [f'' [H4 [H6 H7]]].
        now rewrite H7, H3, add_1_r.
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

Theorem natural_cardinality_uniqueness : ∀ m n : N, m ~ n → m = n.
Proof.
  intros m n H.
  apply NNPP.
  intros H0.
  destruct (lt_trichotomy m n) as [H1 | [H1 | H1]]; auto;
    rewrite lt_is_in in H1.
  - apply (proper_subsets_of_natural_numbers m n); repeat split.
    + apply elements_of_naturals_are_subsets; eauto using elts_in_set.
    + contradict H0; now apply set_proj_injective.
    + eauto using cardinality_trans, cardinality_sym.
  - apply (proper_subsets_of_natural_numbers n m); repeat split.
    + apply elements_of_naturals_are_subsets; eauto using elts_in_set.
    + contradict H0; now apply set_proj_injective.
    + eauto using cardinality_trans, cardinality_sym.
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
  split; intros [n H0].
  - exists n.
    now rewrite <-H.
  - exists n.
    now rewrite H.
Qed.

Add Morphism finite_cardinality with signature
    equinumerous ==> eq as finite_cardinality_equiv.
Proof.
  intros x y H.
  destruct (classic (finite x)).
  - pose proof H0 as [n H1].
    assert (finite y) by now rewrite <-H.
    unfold finite_cardinality.
    repeat destruct excluded_middle_informative; try tauto.
    repeat destruct constructive_definite_description.
    apply natural_cardinality_uniqueness.
    now rewrite <-e, <-e0.
  - assert (¬ finite y) by now rewrite <-H.
    unfold finite_cardinality.
    repeat destruct excluded_middle_informative; tauto.
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
  subst.
  now exists f.
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
    + intros a H8.
      apply Specify_classification.
      split.
      * rewrite <-H5.
        apply function_maps_domain_to_range.
        rewrite H4.
        apply H3.
        rewrite <-H0.
        apply function_maps_domain_to_range.
        congruence.
      * now (exists a).
    + exists h.
      repeat split; auto.
      * rewrite Injective_classification in *.
        intros x y H11 H12 H13.
        rewrite ? H10 in *; try congruence; apply H6 in H13;
          try apply H1 in H13; auto; try congruence; rewrite H4; apply H3;
            rewrite <-H0; apply function_maps_domain_to_range; congruence.
      * rewrite Surjective_classification.
        intros y H11.
        rewrite H9 in H11.
        apply Specify_classification in H11 as [H11 [a [H12 H13]]].
        exists a.
        split; try congruence.
        now rewrite H10.
Qed.

Theorem finite_subsets : ∀ E F,
    finite E → finite F → E ⊂ F → # E ≤ # F.
Proof.
  intros E F H H0 H1.
  unfold finite_cardinality.
  repeat destruct excluded_middle_informative; try tauto.
  repeat destruct constructive_definite_description.
  destruct (subset_equinumerosity x E F x0) as [m [H2 H3]];
    auto using cardinality_sym.
  destruct (le_trichotomy x x0); auto.
  apply le_is_subset in H4.
  apply le_not_gt.
  intros [H5 H6].
  destruct H3 as [g [H3 [H7 H8]]].
  apply (proper_subsets_of_natural_numbers
           {z in x0 | ∃ y, y ∈ x0 ∧ g y = z} x0); repeat split; auto.
  - intros z H9.
    apply Specify_classification in H9 as [H9 [y [H10 H11]]].
    now subst.
  - assert (x0 ⊊ x) as H9.
    { split; auto.
      contradict H6.
      now apply set_proj_injective. }
    apply proper_subset_inhab in H9 as [z [H9 H10]].
    assert (g z ∈ x0) as H11.
    { apply H2.
      rewrite <-H7.
      apply function_maps_domain_to_range.
      congruence. }
    intros H12.
    rewrite <-H12 in H11.
    apply Specify_classification in H11 as [H11 [z' [H13 H14]]].
    destruct H8 as [H8 H15].
    rewrite Injective_classification in H8.
    apply H8 in H14; try (now subst); rewrite H3; auto.
  - destruct (function_construction
                x0 {z in x0 | ∃ y : set, y ∈ x0 ∧ g y = z}
                (λ x, g x)) as [g' [H9 [H10 H11]]].
    { intros a H9.
      apply Specify_classification.
      split.
      - apply H2.
        rewrite <-H7.
        apply function_maps_domain_to_range.
        rewrite H3.
        auto.
      - now (exists a). }
    exists g'.
    destruct H8 as [H8 H12].
    repeat split; auto.
    + rewrite Injective_classification in *.
      intros x1 x2 H13 H14 H15.
      rewrite ? H11 in H15; try congruence.
      apply H8 in H15; auto.
      * rewrite H3.
        apply H4.
        congruence.
      * rewrite H3.
        apply H4.
        congruence.
    + rewrite Surjective_classification.
      intros y H13.
      rewrite H10 in H13.
      apply Specify_classification in H13 as [H13 [z [H14 H15]]].
      exists z.
      split; try congruence.
      now rewrite H11.
Qed.

Theorem naturals_sum_diff : ∀ n m, (m + n) \ m ~ n.
Proof.
  intros n m.
  induction n using Induction.
  - replace ((m + 0) \ m) with ∅; auto using cardinality_refl.
    apply Extensionality.
    split; intros H.
    + contradiction (Empty_set_classification z).
    + rewrite add_0_r, Complement_classification in H.
      tauto.
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
        rewrite H.
        rewrite Complement_classification in *.
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
           apply Pairwise_union_classification; tauto.
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
            + apply lt_is_in in H7.
              contradiction (lt_antisym (m+n) m).
              rewrite <-(add_0_r m), ? (add_comm m) at 1.
              apply O1.
              apply succ_0 in H8 as [k H8].
              subst.
              apply lt_succ. }
        split; auto.
        rewrite H5.
        -- destruct excluded_middle_informative; intuition.
        -- now rewrite <-H3.
Qed.

Theorem finite_union_cardinality : ∀ E F,
    finite E → finite F → E ∩ F = ∅ → # (E ∪ F) = # E + # F.
Proof.
  intros E F [n H] [m H0] H1.
  rewrite (equivalence_to_card E n); auto.
  rewrite (equivalence_to_card F m); auto.
  cut (E ∪ F ~ n + m).
  { intros H2.
    apply equivalence_to_card; auto. }
  pose proof (naturals_sum_diff m n).
  apply cardinality_sym in H.
  apply cardinality_sym in H0.
  apply cardinality_sym.
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

Theorem card_empty : # ∅ = 0.
Proof.
  now rewrite <-card_of_natural.
Qed.

Theorem empty_card : ∀ S, S ~ 0 → S = ∅.
Proof.
  intros S H.
  apply cardinality_sym in H.
  destruct H as [f [H [H0 [H1 H2]]]].
  apply Extensionality.
  split; intros H3.
  - rewrite Surjective_classification in H2.
    rewrite <-H0 in H3.
    apply H2 in H3 as [x [H3 H4]].
    rewrite H in H3.
    contradiction (Empty_set_classification x).
  - contradiction (Empty_set_classification z).
Qed.

Theorem finite_disjoint_unions_are_finite : ∀ E F,
    finite E → finite F → E ∩ F = ∅ → finite (E ∪ F).
Proof.
  intros E F H H0 H1.
  apply NNPP.
  intros H2.
  pose proof (finite_union_cardinality E F) H H0 H1.
  unfold finite_cardinality in H3.
  repeat destruct excluded_middle_informative; auto.
  repeat destruct constructive_definite_description.
  apply eq_sym, cancellation_0_add in H3 as [H3 H4].
  subst.
  contradict n.
  exists 0.
  apply empty_card in e.
  apply empty_card in e0.
  subst.
  rewrite Union_empty.
  apply cardinality_refl.
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
    rewrite H4.
    apply Ordered_pair_iff.
    split; auto.
    now apply Singleton_classification in H2.
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
  pose proof singleton_times_natural_is_finite n m as H.
  unfold finite_cardinality.
  destruct excluded_middle_informative; try tauto.
  destruct constructive_definite_description.
  pose proof (singleton_times_natural_equiv_natural n m).
  apply natural_cardinality_uniqueness.
  now rewrite <-H0, <-e.
Qed.

Theorem natural_products_are_finite : ∀ n m : N, finite (n × m).
Proof.
  intros n m.
  induction n using Induction.
  - replace (0 × m) with ∅.
    + exists 0.
      apply cardinality_refl.
    + apply Extensionality.
      split; intros H.
      * contradiction (Empty_set_classification z).
      * apply Product_classification in H as [a [b [H H0]]].
        contradiction (Empty_set_classification a).
  - rewrite <-S_is_succ.
    unfold succ.
    rewrite Product_union_distr_l, ? finite_union_cardinality.
    apply finite_disjoint_unions_are_finite;
      auto using singleton_times_natural_is_finite.
    apply NNPP.
    intros H.
    apply Nonempty_classification in H as [z H].
    apply Pairwise_intersection_classification in H as [H H0].
    apply Product_classification in H as [a [b [H [H1 H2]]]].
    apply Product_classification in H0 as [c [d [H0 [H3 H4]]]].
    subst.
    apply Ordered_pair_iff in H4 as [H4 H5].
    subst.
    apply Singleton_classification in H0.
    subst.
    contradiction (no_quines n).
Qed.

Theorem card_equiv : ∀ S, finite S → # S ~ S.
Proof.
  intros S H.
  unfold finite_cardinality.
  destruct excluded_middle_informative; try tauto.
  destruct constructive_definite_description.
  now apply cardinality_sym.
Qed.

Theorem singleton_card : ∀ n, # {n,n} = 1.
Proof.
  intros n.
  pose proof singletons_are_finite n as H.
  unfold finite_cardinality.
  destruct excluded_middle_informative; try tauto.
  destruct constructive_definite_description.
  apply natural_cardinality_uniqueness.
  now rewrite <-e, singleton_card_1.
Qed.

Theorem natural_prod_card : ∀ n m : N, # (n × m) = (# n) * (# m).
Proof.
  intros n m.
  induction n using Induction.
  - replace (INS 0) with ∅ by auto.
    replace (∅ × m) with ∅.
    + now rewrite card_empty, mul_0_l.
    + apply Extensionality.
      split; intros H.
      * contradiction (Empty_set_classification z).
      * apply Product_classification in H as [a [b [H H0]]].
        contradiction (Empty_set_classification a).
  - rewrite <-S_is_succ.
    unfold succ.
    rewrite Product_union_distr_l, ? finite_union_cardinality, IHn, mul_distr_r,
    singleton_times_m_card, ? card_of_natural, singleton_card, mul_1_l;
      auto using naturals_are_finite, natural_products_are_finite,
      singletons_are_finite, singleton_times_natural_is_finite, disjoint_succ.
    now rewrite <-Product_intersection, disjoint_succ, Empty_product_left.
Qed.

Theorem subsets_of_finites_are_finite : ∀ E F, finite F → E ⊂ F → finite E.
Proof.
  intros E F H H0.
  destruct (classic (E = F)) as [| H1]; try congruence.
  destruct H as [n [f [H2 [H3 H4]]]].
  assert (E ⊊ F) as H5 by (split; auto).
  destruct (cardinality_of_subsets_of_n {y in n | ∃ x, x ∈ E ∧ f x = y} n)
    as [n' [H6 [g [H7 [H8 H9]]]]].
  { split.
    - intros x H6.
      apply Specify_classification in H6 as [H6 [z [H7 H8]]].
      rewrite <-H3, <-H8.
      apply function_maps_domain_to_range.
      subst; auto.
    - intros H6.
      destruct (proper_subset_inhab _ _ H5) as [x [H7 H8]].
      contradict H8.
      assert (f x ∈ range f) as H8.
      { apply function_maps_domain_to_range.
        congruence. }
      rewrite H3, <-H6 in H8.
      apply Specify_classification in H8 as [H8 [z [H9 H10]]].
      destruct H4 as [H4].
      rewrite Injective_classification in H4.
      apply H4 in H10; subst; auto. }
  exists n'.
  apply (cardinality_trans _ (domain g)).
  - destruct (function_construction E (domain g) (λ x, f x))
      as [f' [H10 [H11 H12]]].
    { intros a H.
      rewrite H7.
      apply Specify_classification.
      split.
      - rewrite <-H3.
        apply function_maps_domain_to_range.
        subst; auto.
      - now (exists a). }
    exists f'.
    destruct H4 as [H4 H13].
    repeat split; auto.
    + rewrite Injective_classification in *.
      intros x y H H14 H15.
      rewrite ? H12 in H15; try congruence.
      apply H4; subst; auto.
    + rewrite Surjective_classification in *.
      intros y H.
      rewrite H11, H7, <-H3, Specify_classification in H.
      destruct H as [H [x [H14 H15]]].
      exists x.
      split; try congruence.
      now rewrite H12.
  - now exists g.
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
    rewrite ? H9 in H12; try congruence.
    rewrite H7 in *.
    apply Product_classification in H10 as [a [b [H10 [H13 H14]]]].
    apply Product_classification in H11 as [c [d [H11 [H15 H16]]]].
    subst.
    rewrite ? proj1_eval, ? proj2_eval, Ordered_pair_iff in *; auto.
    split.
    + now apply H2.
    + now apply H5.
  - rewrite Surjective_classification in *.
    intros y H10.
    rewrite H8, Product_classification in H10.
    destruct H10 as [a [b [H10 [H11 H12]]]].
    subst.
    apply H3 in H10 as [x [H10 H12]].
    apply H6 in H11 as [y [H11 H13]].
    exists (x,y).
    split.
    + rewrite H7, Product_classification.
      now exists x, y.
    + rewrite H9.
      * rewrite proj1_eval, proj2_eval, Ordered_pair_iff; auto.
      * rewrite Product_classification.
        now exists x, y.
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
  intros A B C H.
  destruct (function_construction
              (A ^ (B ∪ C)) (A ^ B × A ^ C)
              (λ z, ({x in z | proj1 (B ∪ C) A x ∈ B},
                     {x in z | proj1 (B ∪ C) A x ∈ C})))
    as [f [H0 [H1 H2]]].
  { intros a H0.
    apply Specify_classification in H0 as [H0 [H1 H2]].
    apply Product_classification.
    exists {x in a | proj1 (B ∪ C) A x ∈ B}, {x in a | proj1 (B ∪ C) A x ∈ C}.
    repeat split; auto.
    - apply Specify_classification.
      repeat split.
      + rewrite Powerset_classification.
        intros x H3.
        apply Specify_classification in H3 as [H3 H4].
        apply H1, Product_classification in H3 as [b' [a' [H3 [H5 H6]]]].
        subst.
        rewrite proj1_eval in *; auto.
        apply Product_classification.
        now exists b', a'.
      + intros x H3.
        apply Specify_classification in H3 as [H3 H4].
        apply H1, Product_classification in H3 as [b' [a' [H3 [H5 H6]]]].
        subst.
        rewrite proj1_eval in *; auto.
        apply Product_classification.
        now exists b', a'.
      + intros x H3.
        destruct (H2 x) as [y [[H4 H5] H6]];
          try (apply Pairwise_union_classification; tauto).
        exists y.
        repeat split; auto.
        * apply Specify_classification.
          rewrite proj1_eval; auto.
          apply Pairwise_union_classification; tauto.
        * intros x' [H7 H8].
          apply H6.
          split; auto.
          now apply Specify_classification in H8 as [H8 H9].
    - apply Specify_classification.
      repeat split.
      + rewrite Powerset_classification.
        intros x H3.
        apply Specify_classification in H3 as [H3 H4].
        apply H1, Product_classification in H3 as [b' [a' [H3 [H5 H6]]]].
        subst.
        rewrite proj1_eval in *; auto.
        apply Product_classification.
        now exists b', a'.
      + intros x H3.
        apply Specify_classification in H3 as [H3 H4].
        apply H1, Product_classification in H3 as [b' [a' [H3 [H5 H6]]]].
        subst.
        rewrite proj1_eval in *; auto.
        apply Product_classification.
        now exists b', a'.
      + intros x H3.
        destruct (H2 x) as [y [[H4 H5] H6]];
          try (apply Pairwise_union_classification; tauto).
        exists y.
        repeat split; auto.
        * apply Specify_classification.
          rewrite proj1_eval; auto.
          apply Pairwise_union_classification; tauto.
        * intros x' [H7 H8].
          apply H6.
          split; auto.
          now apply Specify_classification in H8 as [H8 H9]. }
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
          rewrite Pairwise_union_classification; tauto. }
        apply Specify_classification in H11; tauto.
      * assert (z ∈ {x in v | proj1 (B ∪ C) A x ∈ C}) as H11.
        { rewrite <-H6.
          apply Specify_classification.
          subst.
          rewrite proj1_eval; auto.
          rewrite Pairwise_union_classification; tauto. }
        apply Specify_classification in H11; tauto.
    + pose proof H7 as H8.
      apply H4, Product_classification in H8 as [y [x [H8 [H9 H10]]]].
      apply Pairwise_union_classification in H8 as [H8 | H8].
      * assert (z ∈ {x in u | proj1 (B ∪ C) A x ∈ B}) as H11.
        { rewrite H5.
          apply Specify_classification.
          subst.
          rewrite proj1_eval; auto.
          rewrite Pairwise_union_classification; tauto. }
        apply Specify_classification in H11; tauto.
      * assert (z ∈ {x in u | proj1 (B ∪ C) A x ∈ C}) as H11.
        { rewrite H6.
          apply Specify_classification.
          subst.
          rewrite proj1_eval; auto.
          rewrite Pairwise_union_classification; tauto. }
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
      repeat split.
      - apply Powerset_classification.
        intros z H10.
        apply Pairwise_union_classification in H10 as [H10 | H10].
        + apply H6 in H10 as H11.
           apply Product_classification in H11 as [b [a [H11 [H12 H13]]]].
           apply Product_classification.
           exists b, a.
           repeat split; auto.
           apply Pairwise_union_classification; tauto.
        + apply H8 in H10 as H11.
           apply Product_classification in H11 as [b [a [H11 [H12 H13]]]].
           apply Product_classification.
           exists b, a.
           repeat split; auto.
           apply Pairwise_union_classification; tauto.
      - intros z H10.
        apply Pairwise_union_classification in H10 as [H10 | H10].
        + apply H6 in H10 as H11.
           apply Product_classification in H11 as [b [a [H11 [H12 H13]]]].
           apply Product_classification.
           exists b, a.
           repeat split; auto.
           apply Pairwise_union_classification; tauto.
        + apply H8 in H10 as H11.
           apply Product_classification in H11 as [b [a [H11 [H12 H13]]]].
           apply Product_classification.
           exists b, a.
           repeat split; auto.
           apply Pairwise_union_classification; tauto.
      - intros a H10.
        apply Pairwise_union_classification in H10 as [H10 | H10].
        + apply H7 in H10 as [z [[H10 H11] H12]].
          exists z.
          repeat split; auto.
          * apply Pairwise_union_classification; tauto.
          * intros x' [H13 H14].
            apply H12.
            apply Pairwise_union_classification in H14 as [H14 | H14];
              try tauto.
            contradiction (Empty_set_classification a).
            rewrite <-H.
            apply Pairwise_intersection_classification.
            apply H6, Product_classification in H11 as [c [d [H11 [H15 H16]]]].
            apply H8, Product_classification in H14 as [e [g [H14 [H17 H18]]]].
            apply Ordered_pair_iff in H16 as [H16 H19].
            apply Ordered_pair_iff in H18 as [H18 H20].
            subst; split; auto.
        + apply H9 in H10 as [z [[H10 H11] H12]].
          exists z.
          repeat split; auto.
          * apply Pairwise_union_classification; tauto.
          * intros x' [H13 H14].
            apply H12.
            apply Pairwise_union_classification in H14 as [H14 | H14];
              try tauto.
            contradiction (Empty_set_classification a).
            rewrite <-H.
            apply Pairwise_intersection_classification.
            apply H8, Product_classification in H11 as [c [d [H11 [H15 H16]]]].
            apply H6, Product_classification in H14 as [e [g [H14 [H17 H18]]]].
            apply Ordered_pair_iff in H16 as [H16 H19].
            apply Ordered_pair_iff in H18 as [H18 H20].
            subst; split; auto. }
    repeat split; try congruence.
    rewrite H2; subst; auto.
    replace {x in u ∪ v | proj1 (B ∪ C) A x ∈ B} with u.
    2: { apply Extensionality.
         split; intros H5.
         - apply Specify_classification.
           split.
           + apply Pairwise_union_classification; tauto.
           + apply H6 in H5.
             apply Product_classification in H5 as [a [b [H5 [H11 H12]]]].
             subst.
             rewrite proj1_eval; auto.
             apply Pairwise_union_classification; tauto.
         - apply Specify_classification in H5 as [H5 H11].
           apply Pairwise_union_classification in H5 as [H5 | H5]; auto.
           contradiction (Empty_set_classification (proj1 (B ∪ C) A z)).
           rewrite <-H.
           apply Pairwise_intersection_classification.
           split; auto.
           apply H8, Product_classification in H5 as [a [b [H5 [H12 H13]]]].
           subst.
           rewrite proj1_eval in *; auto;
             apply Pairwise_union_classification; tauto. }
    replace {x in u ∪ v | proj1 (B ∪ C) A x ∈ C} with v; auto.
    apply Extensionality.
    split; intros H5.
    + apply Specify_classification.
      split; try (apply Pairwise_union_classification; tauto).
      apply H8 in H5.
      apply Product_classification in H5 as [a [b [H5 [H11 H12]]]].
      subst.
      rewrite proj1_eval; auto.
      apply Pairwise_union_classification; tauto.
    + apply Specify_classification in H5 as [H5 H11].
      apply Pairwise_union_classification in H5 as [H5 | H5]; auto.
      contradiction (Empty_set_classification (proj1 (B ∪ C) A z)).
      rewrite <-H.
      apply Pairwise_intersection_classification.
      split; auto.
      apply H6, Product_classification in H5 as [a [b [H5 [H12 H13]]]].
      subst.
      rewrite proj1_eval in *; auto;
        apply Pairwise_union_classification; tauto.
Qed.

Theorem power_1_r : ∀ m n, m^{n,n} ~ m.
Proof.
  intros m n.
  symmetry.
  destruct (function_construction m (m^{n,n}) (λ x, {(n,x),(n,x)}))
    as [f [H [H0 H1]]].
  { intros a H.
    apply Specify_classification.
    repeat split.
    - apply Powerset_classification.
      intros x H0.
      apply Singleton_classification in H0.
      subst.
      apply Product_classification.
      exists n, a.
      repeat split; auto.
      now apply Singleton_classification.
    - intros x H0.
      apply Singleton_classification in H0.
      subst.
      apply Product_classification.
      exists n, a.
      repeat split; auto.
      now apply Singleton_classification.
    - intros a' H0.
      apply Singleton_classification in H0.
      subst.
      exists a.
      repeat split; auto.
      + now apply Singleton_classification.
      + intros x' [H0 H1].
        now apply Singleton_classification, Ordered_pair_iff in H1 as [H1 H2]. }
  exists f.
  repeat split; auto.
  - rewrite Injective_classification.
    intros x y H2 H3 H4.
    rewrite ? H1 in H4; try congruence.
    assert ((n,x) ∈ {(n,y),(n,y)}) as H5.
    { rewrite <-H4.
      now apply Singleton_classification. }
    now apply Singleton_classification, Ordered_pair_iff in H5 as [H5 H6].
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
    subst.
    apply Singleton_classification in H9.
    subst.
    rewrite (H7 d); intuition.
    now apply Singleton_classification.
Qed.

Theorem natural_powers_are_finite : ∀ m n : N, finite (m^n).
Proof.
  intros m n.
  induction n as [| n [x H]] using Induction.
  - rewrite power_0_r.
    replace (succ ∅) with (1 : set) by auto.
    apply naturals_are_finite.
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
      + assert (d ∈ range g) as H11.
        { rewrite <-H7.
          now apply function_maps_domain_to_range. }          
        assert (f y ∈ range f) as H12.
        { now apply function_maps_domain_to_range. }
        apply Specify_classification.
        repeat split.
        * apply Product_classification.
          exists d, (f y).
          repeat split; auto.
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
      apply H1 in H21; apply H5 in H20; auto.
      now subst.
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
      apply H1 in H21; apply H5 in H20; auto.
      now subst.
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
        apply Specify_classification in H4.
        tauto.
      * intros z H4.
        apply Specify_classification in H4.
        tauto.
      * intros a H4.
        destruct (H3 (g a)) as [x [[H10 H11] H12]];
          try now apply function_maps_domain_to_range.
        apply H2 in H10 as [z [H10 H13]].
        exists z.
        repeat split; auto.
        -- rewrite Specify_classification, Product_classification.
           split.
           ++ now exists a, z.
           ++ rewrite proj1_eval, proj2_eval, H13; auto.
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
           repeat split.
           ++ apply Specify_classification.
              split.
              ** apply Product_classification.
                 now exists c, d.
              ** rewrite ? proj1_eval, ? proj2_eval; auto.
           ++ rewrite ? proj1_eval, ? proj2_eval; auto;
                now apply function_maps_domain_to_range.
           ++ rewrite ? proj1_eval, ? proj2_eval; auto;
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
           ++ apply Specify_classification.
              rewrite Product_classification, proj1_eval, proj2_eval; auto.
              repeat split; auto.
              now exists a, x.
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

Lemma finite_subsets_bijective :
  ∀ E F, finite E → finite F → E ⊂ F → E ~ F → E = F.
Proof.
  intros E F H H0 H1 H2.
  apply Subset_equality_iff.
  split; auto.
  apply equinumerous_cardinality in H2.
  rewrite Union_subset in H1.
  rewrite <-H1, disjoint_union_complement, finite_union_cardinality in H2;
    eauto using disjoint_intersection_complement,
    subsets_of_finites_are_finite, complement_subset.
  rewrite <-(add_0_r (# E)) in H2 at 1.
  apply naturals.cancellation_add, eq_sym in H2.
  assert (# (F \ E) ~ 0%N) as H3 by now rewrite H2.
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
    - now rewrite <-H2.
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
      unfold functionify in H1.
      destruct constructive_indefinite_description.
      destruct a as [H2 [H3 H4]].
      rewrite functionify_domain in H, H0.
      set (ξ := exist _ _ H : elts (2^X)).
      set (γ := exist _ _ H0 : elts (2^X)).
      replace x with (elt_to_set _ ξ) in * by auto.
      replace y with (elt_to_set _ γ) in * by auto.
      rewrite ? H4 in H1.
      unfold ξ, γ in H1.
      unfold powerset_bijection_helper in *.
      repeat destruct Specify_classification.
      destruct a, a0.
      simpl in H1 |-*.
      clear H4.
      set (f := (mkFunc _ _ _ i2)).
      set (g := (mkFunc _ _ _ i4)).
      assert (x = graph f) by auto.
      assert (y = graph g) by auto.
      rewrite H4, H5.
      f_equal.
      apply func_ext; auto.
      intros z H6; simpl in H6.
      replace ({| domain := X; range := succ (succ ∅);
                  graph := x; func_hyp := i2 |}) with f in H1 by auto.
      replace ({| domain := X; range := succ (succ ∅);
                  graph := y; func_hyp := i4 |}) with g in H1 by auto.
      assert (f z ∈ range f) by now apply function_maps_domain_to_range.
      assert (g z ∈ range g) by now apply function_maps_domain_to_range.
      simpl in H7, H8.
      unfold succ in H7, H8, H1.
      apply Pairwise_union_classification in H7.
      apply Pairwise_union_classification in H8.
      rewrite Union_comm, Union_empty, Singleton_classification in H7, H8.
      rewrite Union_comm, Union_empty in H1.
      destruct H7, H8; rewrite ? Singleton_classification in *; try congruence.
      + assert (z ∈ {x in X | g x = {∅,∅}}) as H9
            by now apply Specify_classification.
        rewrite <-H1 in H9.
        apply Specify_classification in H9 as [H9 H10].
        rewrite H7 in H10.
        contradiction (Empty_set_classification ∅).
        rewrite H10 at 2.
        now rewrite Singleton_classification.
      + assert (z ∈ {x in X | f x = {∅,∅}}) as H9
            by now apply Specify_classification.
        rewrite H1 in H9.
        apply Specify_classification in H9 as [H9 H10].
        rewrite H8 in H10.
        contradiction (Empty_set_classification ∅).
        rewrite H10 at 2.
        now rewrite Singleton_classification.
    - rewrite Surjective_classification.
      assert (1 ∈ 2) as Z.
      { apply Pairwise_union_classification.
        right.
        now apply Singleton_classification. }
      assert (0 ∈ 2) as Z0.
      { apply Pairwise_union_classification.
        left.
        apply Pairwise_union_classification.
        right.
        now apply Singleton_classification. }
      intros y H.
      rewrite functionify_range, functionify_domain in *.
      exists {z in X × 2 | proj2 X 2 z = 1 ↔ proj1 X 2 z ∈ y}.
      assert ({z in X × 2 | proj2 X 2 z = 1 ↔ proj1 X 2 z ∈ y} ∈ 2 ^ X) as Z1.
      { apply Specify_classification.
        split.
        - apply Powerset_classification.
          intros z H0.
          apply Specify_classification in H0.
          tauto.
        - split.
          { intros z H0.
            apply Specify_classification in H0.
            tauto. }
          intros z H0.
          exists (if (excluded_middle_informative (z ∈ y)) then 1 else 0).
          destruct excluded_middle_informative; split.
          + split; auto.
            apply Specify_classification.
            split.
            * apply Product_classification.
              now exists z, 1.
            * rewrite proj1_eval, proj2_eval; tauto.
          + intros x' [H1 H2].
            apply Specify_classification in H2 as [H2 H3].
            rewrite proj1_eval, proj2_eval in H3; intuition.
          + split; auto.
            apply Specify_classification.
            split.
            * apply Product_classification.
              now exists z, 0.
            * rewrite proj1_eval, proj2_eval; auto.
              split; intros H1; try tauto.
              symmetry in H1.
              apply set_proj_injective in H1.
              contradict H1.
              rewrite succ_0.
              now (exists 0).
          + intros x' [H1 H2].
            apply Specify_classification in H2 as [H2 H3].
            rewrite proj1_eval, proj2_eval in H3; intuition.
            apply Pairwise_union_classification in H1 as [H1 | H1].
            * unfold succ in H1.
              now rewrite Union_comm, Union_empty,
              Singleton_classification in H1.
            * rewrite Singleton_classification in H1.
              now apply H4 in H1. }
      split; auto.
      unfold functionify.
      destruct constructive_indefinite_description.
      destruct a as [H0 [H1 H2]].
      set (ζ := exist _ _ Z1 : elts (2^X)).
      replace {z in X × 2 | proj2 X 2 z = 1 ↔ proj1 X 2 z ∈ y}
        with (elt_to_set _ ζ) by auto.
      rewrite H2.
      unfold ζ, powerset_bijection_helper.
      destruct Specify_classification, a.
      simpl.
      clear a i.
      apply Extensionality.
      set (f := mkFunc _ _ _ i1).
      split; intros H3.
      + apply Specify_classification in H3 as [H3 H4].
        assert (f z = 1) as H5 by auto.
        apply function_maps_domain_to_graph in H5; simpl in H5 |-*; auto.
        apply Specify_classification in H5 as [H5 H6].
        rewrite proj1_eval, proj2_eval in H6; auto.
        tauto.
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
        * rewrite proj1_eval, proj2_eval; auto.
          tauto.
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
