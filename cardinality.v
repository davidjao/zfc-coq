Require Export naturals Setoid.
Set Warnings "-notation-overridden".

Open Scope set_scope.

Definition equinumerous A B := ∃ f, domain f = A ∧ range f = B ∧ bijective f.

Infix "~" := equinumerous (at level 70) : set_scope.

Theorem cardinality_refl : ∀ A, A ~ A.
Proof.
  move=> A.
  exists (@functionify A A id).
  rewrite /bijective Injective_classification Surjective_classification
          functionify_domain functionify_range; (repeat split; auto) =>
  [x y H H0 | y H]; [ | exists y ];
    rewrite (reify H) ? (reify H0) ? functionify_action //.
Qed.

Theorem cardinality_sym : ∀ A B, A ~ B → B ~ A.
Proof.
  move=> A B [f [H [H0 H1]]].
  exists (inverse f).
  rewrite inverse_domain ? inverse_range; auto using inverse_bijective.
Qed.

Theorem cardinality_trans : ∀ A B C, A ~ B → B ~ C → A ~ C.
Proof.
  move=> A B C [f [<- [<- [? ?]]]]
           [g [/[dup] ? /Composition_classification [? [? ?]] [<- [*]]]].
  exists (g ∘ f).
  repeat split; eauto using composition_injective, composition_surjective.
Qed.

Theorem cardinality_is_equivalence :
  ∀ X, is_equivalence (P X) {z in P X × P X |
                              proj1 (P X) (P X) z ~ proj2 (P X) (P X) z}.
Proof.
  (repeat split) =>
  [? ? | ? ? ? ? /Specify_classification [H1] |
   ? ? ? ? ? ? /Specify_classification [?] /[swap] /Specify_classification [?]];
    rewrite Specify_classification ? Product_classification ? proj1_eval
            ? proj2_eval;
    intuition eauto using cardinality_refl, cardinality_sym, cardinality_trans.
Qed.

Add Parametric Relation : set equinumerous
      reflexivity proved by (cardinality_refl)
      symmetry proved by (cardinality_sym)
      transitivity proved by (cardinality_trans) as set_equivalence.

Theorem cardinality_eq : ∀ A B, A = B → A ~ B.
Proof.
  now move=> A B ->.
Qed.

Theorem injective_into_image : ∀ f, injective f → domain f ~ image f.
Proof.
  move=> f /Injective_classification H.
  exists (restriction_Y (Set_is_subset (image f))).
  rewrite restriction_Y_domain restriction_Y_range /bijective
          Injective_classification Surjective_classification
          restriction_Y_domain restriction_Y_range ? restriction_Y_action.
  (repeat split; auto) =>
  [x y /[dup] H0 /H /[swap] /[dup] H1 /[swap] /[apply] |
   y /Specify_classification [H0 [x [H1 H2]]]]; [ | exists x ];
    rewrite ? restriction_Y_action //.
Qed.

Theorem injection_restriction :
  ∀ f S, injective f → S ⊂ domain f → S ~ push_forward f S.
Proof.
  move=> f S /Injective_classification H H0.
  have: image (restriction f S) ⊂ push_forward f S =>
  [y /Specify_classification /and_comm [[x]] | H1].
  { rewrite restriction_domain restriction_range => /[dup] [[?]].
    rewrite -restriction_action // => [? [? ?] ?].
    apply Specify_classification, conj; eauto. }
  exists (restriction_Y H1).
  rewrite restriction_Y_domain restriction_Y_range restriction_domain
          /bijective Injective_classification Surjective_classification.
  (repeat split; auto; first by apply /Intersection_subset) => [x y | y].
  - rewrite restriction_Y_domain restriction_domain =>
    /[dup] H2 /[dup] /Intersection_right H3 /[swap]
     /[dup] H4 /[dup] /Intersection_right H5.
    rewrite ? restriction_Y_action ? restriction_domain
            -? restriction_action; auto.
  - rewrite restriction_Y_range restriction_Y_domain restriction_domain
            Specify_classification => [[H2 [x [H3 H4]]]].
    exists x.
    rewrite restriction_Y_action ? restriction_domain -? restriction_action //.
Qed.

Theorem cardinality_of_subsets_of_n :
  ∀ m (n : N), m ⊊ n → ∃ n', n' < n ∧ m ~ n'.
Proof.
  move => /[swap].
  elim/Induction =>
  [m /proper_subset_inhab [z [/Empty_set_classification H H0]]
  | n IH m /[dup] [[H H0]] /proper_subset_inhab [z [H1 H2]]] //.
  elim (classic (n ∈ m)).
  - elim (function_construction m n (λ x, If x = n then z else x)) =>
    [f [H3 [H4 H5]] | a].
    + have: injective f.
      { apply /Injective_classification => x y H6 H7.
        rewrite ? H5; repeat case excluded_middle_informative; congruence. }
      elim (classic (image f = range f)) => [ | H6].
      * exists n.
        rewrite -H3 -H4 -H6.
        auto using succ_lt, injective_into_image.
      * elim (IH (image f)) =>
        [n' [H7 H8] | ]; rewrite -? H3 -? H4; repeat split;
          eauto 6 using lt_trans, succ_lt, injective_into_image,
          cardinality_trans, image_subset_range.
    + case excluded_middle_informative => [-> | ].
      * move: H1 H2 => /in_S_succ /Pairwise_union_classification =>
        [[H1 | /Singleton_classification ->]] //.
      * move: H =>
        /[swap] H3 /[apply] /in_S_succ /Pairwise_union_classification
         [ | /Singleton_classification] //.
  - elim (classic (m = n)) =>
    [-> | H3 H4]; eauto using lt_trans, succ_lt, cardinality_refl.
    suff: m ⊊ n => [/IH [n' [H5 H6]] | ]; eauto using lt_trans, succ_lt.
    split; auto =>
    x /[dup] /[swap] /H /in_S_succ /Pairwise_union_classification
      [ | /Singleton_classification ->] //.
Qed.

Lemma equivalence_minus_element_singular : ∀ A x y,
    x ∈ A → y ∈ A → A \ {x,x} ~ A \ {y,y}.
Proof.
  move=> A x y H H0.
  case (classic (x = y)) => [-> | H1]; auto using cardinality_refl.
  elim (function_construction (A \ {x,x}) (A \ {y,y})
                              (λ z, If z = y then x else z))
  => [f' [H2 [H3 H4]] | a0 /Complement_classification H2].
  - exists f'.
    rewrite /bijective Injective_classification Surjective_classification H2 H3.
    (repeat split; auto) =>
    [x0 y0 /Complement_classification [H5 /Singleton_classification H6]
        /Complement_classification [H7 /Singleton_classification H8] |
     y0 /Complement_classification [H5 /Singleton_classification H6]].
    + rewrite ? H4 ? Complement_classification ? Singleton_classification //.
      case (classic (x = x0)), (classic (x = y0));
        repeat case excluded_middle_informative; congruence.
    + case (classic (x = y0)) =>
      [<- | ]; [ exists y | exists y0 ];
        rewrite H4 Complement_classification Singleton_classification;
        repeat split; try case excluded_middle_informative; intuition.
  - rewrite Complement_classification Singleton_classification.
    case excluded_middle_informative => *; intuition.
Qed.

Theorem equivalence_minus_element : ∀ A B x y,
    A ~ B → x ∈ A → y ∈ B → A \ {x,x} ~ B \ {y,y}.
Proof.
  move=> A B x y [f [<- [<- [/Injective_classification ?
                              /Surjective_classification H]]]] ? ?.
  enough ((domain f) \ {x,x} ~ (range f) \ {f x, f x});
    eauto using cardinality_trans, equivalence_minus_element_singular,
    function_maps_domain_to_range.
  elim (function_construction ((domain f) \ {x,x})
                              ((range f) \ {f x, f x}) (λ x, f x)) =>
  [f' [H0 [H1 H2]] | a /Complement_classification
                       [H5 /Singleton_classification H6]].
  - exists f'.
    rewrite /bijective Injective_classification Surjective_classification H0 H1.
    (repeat split; auto) =>
    [x0 y0 /[dup] ? /Complement_classification [? /Singleton_classification ?]
        /[dup] ? /Complement_classification [? /Singleton_classification ?] |
     y0 /[dup] ? /Complement_classification
        [/[dup] ? /H ? /Singleton_classification H8]]; try rewrite ? H2; auto.
    elim (H y0) => [x0 [? ?] | ] //.
    exists x0.
    rewrite H2 Complement_classification Singleton_classification;
      repeat split; auto; move: H8 => /[swap] <- /neq_sym //.
  - rewrite Complement_classification Singleton_classification;
      auto using function_maps_domain_to_range.
Qed.

Lemma two_sided_inverse_bijective : ∀ A B,
  (∃ (f : elts A → elts B) (g : elts B → elts A),
      ((∀ a : elts A, g (f a) = a) ∧ (∀ b : elts B, f (g b) = b))) → A ~ B.
Proof.
  move=> A B [f [g [H H0]]].
  exists (functionify f).
  rewrite /bijective Injective_classification Surjective_classification
          functionify_range functionify_domain.
  (repeat split; auto) => [x y H1 H2 | y H1].
  - rewrite (reify H1) (reify H2) ? functionify_action
    => /set_proj_injective H3.
    f_equal.
    rewrite <-H, <-H3, H => //.
  - exists (g (mkSet H1)).
    rewrite functionify_action H0.
    auto using elts_in_set.
Qed.

Theorem two_sided_inverse_bijective_set:
  ∀ A B, (∃ f g, (∀ a, a ∈ A → (f a ∈ B ∧ g (f a) = a)) ∧
                 (∀ b, b ∈ B → (g b ∈ A ∧ f (g b) = b))) → A ~ B.
Proof.
  move=> A B [f [g [/[dup] H /[swap] /[dup] H0]]].
  elim (function_construction A B f) => [f' [<- [<- H1 H2 H3]] | a /H [H1]] //.
  exists f'.
  rewrite /bijective Injective_classification Surjective_classification.
  (repeat split; auto) =>
  [x y /[dup] H4 /H3 [H5 H6] /[dup] H7 /H3 [H8 H9] | y /[dup] H4 /H2 [H5 H6]];
    [ | exists (g y) ]; rewrite ? H1 // -{2} H6 -{2} H9 => -> //.
Qed.

Theorem proper_subsets_of_natural_numbers : ∀ m (n : N), m ⊊ n → ¬ n ~ m.
Proof.
  move /[swap].
  elim/Induction => [m /proper_subset_inhab [z [/Empty_set_classification]] |
                     n IH m /[dup] H [H0 H1] [f [H2 [H3 /[dup] ? [? ?]]]]] //.
  have H4: S n \ {n,n} = n.
  { rewrite -S_is_succ /succ complement_disjoint_union ? disjoint_succ //. }
  elim (classic (n ∈ m)) => [? | ?].
  - (apply /(IH (m \ {n,n})); repeat split) =>
    [x /Complement_classification
       [/H0 /in_S_succ /Pairwise_union_classification [H5 | H5] ?] | H5 | ] //.
    + contradict H1.
      apply Subset_equality_iff, conj; auto =>
      x /in_S_succ /Pairwise_union_classification
        [ | /Singleton_classification ->] //.
      rewrite -H5 => /complement_subset //.
    + rewrite -{1}H4.
      apply equivalence_minus_element; rewrite /equinumerous; eauto.
  - apply /(IH (m \ {f n, f n})).
    + (apply /(subsetneq_subset_trans _ m); repeat split) =>
      [x /Complement_classification [H5 ?] | H5 |
       x /[dup] /H0 /in_S_succ /Pairwise_union_classification
         [H5 | /Singleton_classification -> ] ] //.
      move: (function_maps_domain_to_range f n) (in_succ n).
      rewrite H2 in_S_succ H3 -H5 => /[apply].
      rewrite Complement_classification Singleton_classification => [[?]] //.
    + rewrite -{1}H4.
      apply /equivalence_minus_element; try apply /in_S_succ /in_succ.
      * rewrite /equinumerous; eauto.
      * move: (function_maps_domain_to_range f n) (in_succ n).
        rewrite H2 in_S_succ H3 => /[apply] //.
Qed.

Theorem equiv_proper_subset_ω : ∃ S, S ⊊ ω ∧ S ~ ω.
Proof.
  exists (ω \ {0,0}).
  (repeat split) =>
  [x /Complement_classification [?] | | ]
    //; first by move: (elts_in_set 0) =>
  /[swap] {2}<- /Complement_classification [_] /Singleton_classification //.
  symmetry.
  set (f := functionify (λ x, x + 1)).
  elim (function_construction ω (ω \ {0,0}) (λ x, f x)) =>
  [f' [H [H0 H1]] | a H].
  - exists f'.
    (repeat split; auto;
      rewrite ? Injective_classification ? Surjective_classification) =>
    [x y H2 H3 | y H2].
    + move: H H2 H3 -> => H2 H3.
      (rewrite ? H1 ? (reify H2) ? (reify H3)
               ? functionify_action -? (add_comm 1); auto) =>
      /set_proj_injective /cancellation_add -> //.
    + move: H0 H2 -> =>
      /Complement_classification [H0] /Singleton_classification H2.
      exists (mkSet H0 - 1).
      (have: (mkSet H0) ≠ 0 by (contradict H2; now inversion H2)) =>
      /succ_0 => [[m /[dup] H3]].
      rewrite H H1 /f ? functionify_action 1? add_comm ? sub_abab H3;
        repeat split; eauto using elts_in_set, one_le_succ.
      rewrite -H3 //.
  - rewrite /f (reify H) functionify_action Complement_classification
            Singleton_classification add_1_r.
    split; eauto using elts_in_set => /set_proj_injective /(@eq_sym N) /PA4 //.
Qed.

Definition finite S := ∃ n : N, S ~ n.

Definition infinite S := ¬ finite S.

Theorem naturals_are_finite : ∀ n : N, finite n.
Proof.
  rewrite /finite.
  eauto using cardinality_refl.
Qed.

Theorem infinite_ω : infinite ω.
Proof.
  move: equiv_proper_subset_ω =>
  [S [/[dup] /[dup] H [H0 H1] /proper_subset_inhab [z [H2 H3]] H4]]
    [n /[dup] H5 [f [H6 [H7 [/Injective_classification H8
                              /Surjective_classification H9]]]]].
  (contradiction
    (proper_subsets_of_natural_numbers {x in n | ∃ s, s ∈ S ∧ x = f s} n);
    repeat split) => [x /Specify_classification [H10] | H10 | ] //.
  - absurd (f z ∈ n).
    + rewrite -H10 Specify_classification => [[H11 [s [H12 /H8]]]] H13.
      move: H6 H13 H2 (H12) (H12) -> =>
      /[apply] /[swap] /H0 /[swap] /[apply] <- //.
    + move: H6 H7 H2 (function_maps_domain_to_range f z) -> =>
      -> /[swap] /[apply] //.
  - rewrite -{1}H5 -{1}H4.
    elim (function_construction
            S {x in n | ∃ s : set, s ∈ S ∧ x = f s} (λ x, f x))
    => [f' [H10 [H11 H12]] | a /[dup] H10].
    + exists f'.
      rewrite /bijective Injective_classification Surjective_classification.
      (repeat split; auto) => [x y | y].
      * move: H10 (H12) -> => /[swap] H13 /[dup] -> // /[swap] H14 -> // /H8.
        move: H6 H13 H14 -> => /H0 /[swap] /H0; tauto.
      * rewrite H11 => /Specify_classification => [[H13 [s] /[dup] [[H14]] _]].
        rewrite -H10 => [[H15 ->]]; eauto.
    + move: H6 H7 (function_maps_domain_to_range f a) -> =>
      -> /[swap] /H0 /[swap] /[apply] H11.
      apply /Specify_classification /conj; eauto.
Qed.

Theorem natural_cardinality_uniqueness : ∀ m n : N, m ~ n → m = n.
Proof.
  move=> m n.
  wlog: m n / n < m =>
  [x H | /lt_is_subsetneq /proper_subsets_of_natural_numbers] //.
  elim (lt_trichotomy m n) => [ | []]; auto using eq_sym, cardinality_sym.
Qed.

Theorem finite_cardinality_uniqueness : ∀ S, finite S → exists ! n : N, S ~ n.
Proof.
  move=> S [n H].
  exists n.
  split; eauto using natural_cardinality_uniqueness,
         cardinality_trans, cardinality_sym.
Qed.

Definition finite_cardinality : set → N.
Proof.
  move=> S.
  elim (excluded_middle_informative (finite S)) =>
  [/finite_cardinality_uniqueness
    /constructive_definite_description [n H] | H].
  - exact n.
  - exact 0.
Defined.

Notation " # E " := (finite_cardinality E) (at level 45) : set_scope.

Theorem card_equiv : ∀ x, finite x → x ~ # x.
Proof.
  rewrite /finite_cardinality => x H.
  (case excluded_middle_informative => /=; try tauto) => H0.
  elim constructive_definite_description => //.
Qed.

Theorem card_equiv_l : ∀ S, finite S → # S ~ S.
Proof.
  move=> S /card_equiv /cardinality_sym //.
Qed.

Add Morphism finite with signature equinumerous ==> iff as finiteness_equiv.
Proof.
  split => [[n]|[n]]; exists n; eauto using cardinality_sym, cardinality_trans.
Qed.

Theorem card_of_natural : ∀ n : N, # n = n.
Proof.
  eauto using eq_sym, natural_cardinality_uniqueness, card_equiv,
  naturals_are_finite.
Qed.

Add Morphism finite_cardinality with signature
    equinumerous ==> eq as finite_cardinality_equiv.
Proof.
  rewrite /finite_cardinality => x y H.
  (repeat case excluded_middle_informative => /=; auto) =>
  [* | ? /[dup] | ? /[dup]]; try rewrite {1}H //.
  repeat elim constructive_definite_description.
  eauto using natural_cardinality_uniqueness, cardinality_trans,
  cardinality_sym.
Qed.

Theorem equivalence_to_card : ∀ S (n : N), S ~ n → # S = n.
Proof.
  move=> S n ->.
  auto using card_of_natural.
Qed.

Theorem equivalence_to_bijection : ∀ S (n : N),
    finite S → # S = n → ∃ f, domain f = S ∧ range f = n ∧ bijective f.
Proof.
  move=> S n /card_equiv /[swap] -> [f H].
  eauto.
Qed.

Lemma subset_equinumerosity :
  ∀ A B C D, A ~ B → B ⊂ C → C ~ D → ∃ E, E ⊂ D ∧ A ~ E.
Proof.
  move=> A B C D [f [<- [<- [/Injective_classification H
                              /Surjective_classification H0]]]]
           /[swap] [[g [<- [<- [/Injective_classification H1
                                 /Surjective_classification H2]]]]] H3.
  exists ({d in range g | ∃ a, a ∈ domain f ∧ g (f a) = d}).
  split => [d /Specify_classification [H4] | ] //.
  elim (function_construction
          (domain f) {d in range g |
                       ∃ a : set, a ∈ domain f ∧ g (f a) = d} (λ x, g (f x)))
  => [h [H4 [H5 H6]] | a H4].
  - exists h.
    rewrite /bijective Injective_classification Surjective_classification.
    (repeat split; auto) => [x y | y].
    + move: H4 H6 -> => /[swap] H6 /[swap] H7 /[dup] -> // -> // /H1 /H H8.
      apply /H8; eauto using function_maps_domain_to_range.
    + rewrite H5 Specify_classification H4 => [[H7 [a [H8 <-]]]].
      eauto.
  - apply Specify_classification, conj;
      eauto using function_maps_domain_to_range.
Qed.

Theorem card_empty : # ∅ = 0.
Proof.
  rewrite -(card_of_natural 0) //.
Qed.

Theorem empty_card : ∀ S, S ~ 0 → S = ∅.
Proof.
  move=> S /cardinality_sym [f] [H [<- [H0 /Surjective_classification]]].
  move: H -> => H.
  (apply Subset_equality_iff, conj; auto using Empty_set_is_subset) =>
  x /H [y [/Empty_set_classification]] //.
Qed.

Lemma finite_subsets_precursor :
  ∀ E F, finite F → E ⊂ F → ∃ n : N, E ~ n ∧ n ≤ # F.
Proof.
  move=>
  E F /[dup]
    [[n /[dup] /equivalence_to_card /[swap]
        [[f [<- [H /[dup] H0 [/Injective_classification H1
                               /Surjective_classification H2]]]]] H3 H4 H5]].
  elim (classic (E = (domain f))) =>
  [-> | H6]; eauto using cardinality_sym, card_equiv, le_refl.
  (elim (proper_subset_inhab E (domain f)); try split; eauto) => [z [H7 H8]].
  elim (cardinality_of_subsets_of_n
          {y in # (domain f) | ∃ x, x ∈ E ∧ f x = y} (# domain f)) =>
  [n' [H9 [g [H10 [H11 H12]]]] | ].
  - exists n'.
    split; last by eapply lt_le_trans; eauto using le_refl.
    apply /(cardinality_trans _ (domain g)); try now (exists g).
    move: (H5) (H10).
    elim (function_construction E (domain g) (λ x, f x)) =>
    [f' [<- [H13 H14 H15]] | y].
    + exists f'.
      rewrite /bijective Injective_classification Surjective_classification.
      (repeat split; auto) =>
      [x y H17 H18 | y]; try rewrite ? H14 // => /H1 ?; auto.
      move: H13 H16 H14 -> =>
      -> /[swap] /Specify_classification [?] [?] [?] /[swap] <-; eauto.
    + move: H10 H3 H -> => -> <- H.
      apply Specify_classification, conj; eauto.
      apply /function_maps_domain_to_range; auto.
  - split => [y /Specify_classification [H9 [x [H10]]] | H9] //.
    contradict H8.
    move: (H7) H H3 H9 =>
    /function_maps_domain_to_range /[swap] ->
    /[swap] <- /[swap] <-
    /Specify_classification [H] [x] /and_comm [/H1] /[swap] ? <-; auto.
Qed.

Theorem subsets_of_finites_are_finite : ∀ E F, finite F → E ⊂ F → finite E.
Proof.
  move=> E F H /finite_subsets_precursor [| n [H0 H1]] //.
  apply /ex_intro /H0.
Qed.

Theorem finite_subsets : ∀ E F, finite F → E ⊂ F → # E ≤ # F.
Proof.
  move=> E F /[swap] /finite_subsets_precursor /[apply]
           [[n [/equivalence_to_card <-]]] //.
Qed.

Theorem naturals_sum_diff : ∀ n m, (m + n) \ m ~ n.
Proof.
  elim/Induction =>
  [m | n /[swap] m /(_ m) [f [H [H0 [/Injective_classification H1
                                      /Surjective_classification H2]]]]];
    rewrite ? add_0_r ? add_succ_r -? S_is_succ;
    first by apply cardinality_eq, Complement_subset, Set_is_subset.
  have H3: ∀ z, z ∈ succ (m + n) \ m → z ≠ m + n → z ∈ domain f => [z | ].
  { rewrite H ? Complement_classification =>
    [[/Pairwise_union_classification
       [H3 | /Singleton_classification] H4] H5] //. }
  elim (function_construction
          (succ (m + n) \ m) (succ n) (λ x, If x = m + n then n else f x))
  => [f' [H4 [H5 H6]] | a H4].
  - exists f'.
    move: (H4) (H3) <- => H7.
    rewrite /bijective Injective_classification Surjective_classification H5.
    (repeat split; auto) => [x y H8 H9 | y /Pairwise_union_classification
                                           [ | /Singleton_classification ->]].
    + rewrite ? H6; try congruence.
      repeat case excluded_middle_informative; try congruence; auto
      => H10 H11 H12; contradiction (no_quines n);
           [ rewrite {1}H12 -H0 | rewrite -{1}H12 -H0 ];
           auto using function_maps_domain_to_range.
    + rewrite -H0 => /H2 [x].
      rewrite H H4 =>
      [[/Complement_classification [/[dup] H8 /subset_succ H9] H10 H11]].
      exists x.
      rewrite ? H6 ? Complement_classification //.
      repeat split => //.
      case excluded_middle_informative => //.
      move: H8 => /[swap] -> /no_quines //.
    + exists (m+n).
      have H8: m+n ∈ domain f'.
      { rewrite H4 Complement_classification.
        split.
        - apply /Pairwise_union_classification /or_intror.
          rewrite Singleton_classification //.
        - elim (classic (n = 0)) =>
          [-> | ]; rewrite ? add_0_r -? lt_is_in -? le_not_gt 1 ? add_comm;
            auto using le_refl, le_add_l. }
      rewrite H6 -? H4; (repeat split) => //.
      case excluded_middle_informative => //.
  - case excluded_middle_informative; auto using in_succ => H5.
    rewrite -H0.
    apply /subset_succ /function_maps_domain_to_range /H3 => //.
Qed.

Theorem finite_union_equinumerosity : ∀ E F,
    finite E → finite F → E ∩ F = ∅ → (E ∪ F) ~ # E + # F.
Proof.
  move=> E F [n /[dup] /equivalence_to_card -> /cardinality_sym]
           /[swap] [[m /[dup] /equivalence_to_card -> /cardinality_sym]].
  move: (naturals_sum_diff m n)
  => /[dup] H1 [h [H11 [H12 [/Injective_classification
                              H13 /Surjective_classification H14]]]]
      /[dup] H0 [g [H7 [H8 [/Injective_classification
                             H9 /Surjective_classification H10]]]]
      /[dup] H [f [H3 [H4 [/Injective_classification H5
                            /Surjective_classification H6]]]] H2.
  elim (function_construction
          (n + m) (E ∪ F) (λ x, If x ∈ n then f x else g (h x))) =>
  [f' [/[dup] H15 <- [H16 H17]] | a].
  - symmetry.
    exists f'.
    rewrite /bijective Injective_classification Surjective_classification.
    (repeat split; auto) => [x y H18 H19 | y].
    + rewrite ? H17 //.
      wlog: x y H17 H18 H19 / x ∈ n ∧ y ∉ n => [x0 | ].
      * (repeat case excluded_middle_informative)
        => *; [ apply H5 | apply x0 | apply eq_sym, x0 | ];
             repeat case excluded_middle_informative; intuition try congruence.
        apply H13; try rewrite H11 Complement_classification -H15 //.
        apply H9; auto; rewrite H7 -H12 ; apply function_maps_domain_to_range;
          rewrite H11 Complement_classification -H15 //.
      * (repeat case excluded_middle_informative; try tauto) => H20 H21 _ H22.
        contradiction (Empty_set_classification (f x)).
        rewrite -H2 -H4 -H8 Pairwise_intersection_classification.
        move: H3 H21 <- => /function_maps_domain_to_range.
        (have: y ∈ domain h by rewrite H11 -H15 Complement_classification //)
        => /function_maps_domain_to_range.
        move: H12 H7 H22 -> => <- {3}-> /function_maps_domain_to_range //.
    + rewrite H16 -H4 -H8 Pairwise_union_classification =>
      [[/H6 [x] /and_comm [<-] /[dup] /[dup] | /H10 [z [H18 H19]]]].
      * have: n ⊂ n + m by apply le_is_subset, le_add.
        move: H3 H15 H17 => {1 2}-> => -> H17 /[apply].
        repeat esplit; eauto.
        rewrite H17 //.
        case excluded_middle_informative => //.
      * move: H7 H12 H18 H11 H15 H17 -> => <- /H14 /[swap] -> /[swap] -> =>
        [[x [/[dup] H20 /Complement_classification [H21 H22] H23]] H17].
        repeat esplit; eauto.
        rewrite H17 //.
        case excluded_middle_informative; intuition congruence.
  - case excluded_middle_informative =>
    H15 H16; apply /Pairwise_union_classification.
    + move: H3 H15 H4 <- => /function_maps_domain_to_range /[swap] ->; auto.
    + (have: a ∈ domain h by rewrite H11 Complement_classification) =>
      /function_maps_domain_to_range.
      move: H12 H7 H8 -> =>
      <- /[swap] /function_maps_domain_to_range /[swap] ->; auto.
Qed.

Theorem finite_union_cardinality : ∀ E F,
    finite E → finite F → E ∩ F = ∅ → # (E ∪ F) = # E + # F.
Proof.
  eauto using equivalence_to_card, finite_union_equinumerosity.
Qed.

Theorem finite_disjoint_unions_are_finite : ∀ E F,
    finite E → finite F → E ∩ F = ∅ → finite (E ∪ F).
Proof.
  move=> E F H H0 H1.
  apply /ex_intro /finite_union_equinumerosity => //.
Qed.

Theorem singleton_card_1 : ∀ x, {x,x} ~ 1.
Proof.
  move=> x.
  elim (function_construction {x,x} 1 (λ x, 0)) =>
  [f [H [H0 H1]] | a H]; last by apply /in_succ.
  (eapply ex_intro, conj, conj, conj; eauto;
   rewrite ? Injective_classification ? Surjective_classification) => [a b | y].
  - move: H -> => /Singleton_classification -> /Singleton_classification -> //.
  - rewrite H H0 /one -in_S_succ => /Pairwise_union_classification =>
    [[/Empty_set_classification | /Singleton_classification ->]] //.
    (have: x ∈ {x,x} by apply /Singleton_classification); eauto.
Qed.

Theorem singletons_are_finite : ∀ x, finite {x,x}.
Proof.
  move=> x.
  apply /ex_intro /singleton_card_1.
Qed.

Lemma singleton_times_natural_equiv_natural : ∀ n m : N, ({n,n} × m ~ m).
Proof.
  move=> n m.
  symmetry.
  elim (function_construction m ({n,n} × m) (λ x, (n,x))) =>
  [f [H [H0 H1]] | a H].
  2: { apply /Product_classification.
       repeat esplit; rewrite ? Singleton_classification //. }
  exists f.
  rewrite /bijective ? Injective_classification ? Surjective_classification.
  (repeat split; auto) => [x y | y].
  - move: H (H1) -> =>
    /[swap] ? /[dup] -> // /[swap] ? -> // /Ordered_pair_iff [?] //.
  - move: H H0 -> =>
    -> /Product_classification
        [a [b [/Singleton_classification -> [/[dup] H /H1 H0 ->]]]]; eauto.
Qed.

Lemma singleton_times_natural_is_finite : ∀ n m : N, finite ({n,n} × m).
Proof.
  move=> n m.
  apply /ex_intro /singleton_times_natural_equiv_natural.
Qed.

Lemma singleton_times_m_card : ∀ n m : N, # ({n,n} × m) = m.
Proof.
  move=> n m.
  auto using equivalence_to_card, singleton_times_natural_equiv_natural.
Qed.

Theorem natural_products_are_finite : ∀ n m : N, finite (n × m).
Proof.
  elim/Induction => [m | n IH m].
  - exists 0.
    now rewrite Empty_product_left /=.
  - rewrite -S_is_succ /succ Product_union_distr_l.
    apply /finite_disjoint_unions_are_finite;
      auto using singleton_times_natural_is_finite.
    rewrite -Product_intersection disjoint_succ Empty_product_left //.
Qed.

Theorem finite_empty : ∀ S, finite S → # S = 0 → S = ∅.
Proof.
  move=> S /card_equiv /[swap] -> /empty_card H //.
Qed.

Theorem singleton_card : ∀ n, # {n,n} = 1.
Proof.
  move=> n.
  apply /equivalence_to_card /singleton_card_1.
Qed.

Theorem natural_prod_card : ∀ n m : N, # (n × m) = (# n) * (# m).
Proof.
  elim/Induction =>
  [m | n IH m];
    rewrite ? Empty_product_left ? card_empty ? card_of_natural ? mul_0_l //
    - S_is_succ /succ Product_union_distr_l ? finite_union_cardinality ? IH
                -? add_1_r ? mul_distr_r ? singleton_times_m_card
                ? card_of_natural ? mul_1_l -? Product_intersection
                ? disjoint_succ ? Empty_product_left;
  auto using naturals_are_finite, natural_products_are_finite,
  singletons_are_finite, singleton_times_natural_is_finite, disjoint_succ.
Qed.

Theorem Inclusion_Exclusion : ∀ E F,
    finite E → finite F → # (E ∪ F) + # (E ∩ F) = # E + # F.
Proof.
  move=> E F H H0.
  rewrite disjoint_union_complement finite_union_cardinality // -? add_assoc
  -1 ? finite_union_cardinality ? complement_union_intersection;
    eauto using disjoint_intersection_complement, subsets_of_finites_are_finite,
    complement_disjoint_intersection, complement_subset, Intersection_left.
Qed.

Theorem finite_unions_are_finite : ∀ E F, finite E → finite F → finite (E ∪ F).
Proof.
  move=> E F H H0.
  rewrite disjoint_union_complement.
  apply finite_disjoint_unions_are_finite;
    eauto using disjoint_intersection_complement, complement_subset,
    subsets_of_finites_are_finite.
Qed.

Theorem finite_union_card_bound : ∀ E F, # (E ∪ F) ≤ # E + # F.
Proof.
  move=> E F.
  case (classic (finite E)), (classic (finite F));
    try (by rewrite -Inclusion_Exclusion /le; eauto);
    rewrite {1}/finite_cardinality; case excluded_middle_informative
  => *; auto using zero_le; exfalso;
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
    rewrite -> proj1_eval, proj2_eval; auto.
    apply Product_classification.
    exists (f a), (g b).
    repeat split; auto; rewrite <-? H1, <-? H4;
      now apply function_maps_domain_to_range. }
  exists h.
  repeat split; auto.
  - rewrite -> Injective_classification in *.
    intros x y H10 H11 H12.
    rewrite -> ? H9, H7 in *; try congruence.
    apply Product_classification in H10 as [a [b [H10 [H13 H14]]]].
    apply Product_classification in H11 as [c [d [H11 [H15 H16]]]].
    subst.
    rewrite -> ? proj1_eval, ? proj2_eval, Ordered_pair_iff in *; intuition.
  - rewrite -> Surjective_classification in *.
    intros y H10.
    rewrite -> H8, Product_classification in H10.
    destruct H10 as [a [b [H10 [H11 H12]]]].
    subst.
    apply H3 in H10 as [x [H10 H12]].
    apply H6 in H11 as [y [H11 H13]].
    exists (x,y).
    split.
    + rewrite -> H7, Product_classification; eauto.
    + rewrite -> H9, proj1_eval, proj2_eval, Ordered_pair_iff; auto.
      apply Product_classification; eauto.
Qed.

Theorem finite_products_are_finite :
  ∀ E F, finite E → finite F → finite (E × F).
Proof.
  intros E F [n H] [m H0].
  rewrite -> H, H0.
  apply natural_products_are_finite.
Qed.

Theorem finite_products_card :
  ∀ E F, finite E → finite F → # (E × F) = (# E) * (# F).
Proof.
  intros E F [n H] [m H0].
  now rewrite -> H, H0, natural_prod_card.
Qed.

Theorem power_union_r : ∀ A B C, B ∩ C = ∅ → A ^ (B ∪ C) ~ A ^ B × A ^ C.
Proof.
  assert (∀ A B C z, z ∈ A ^ (B ∪ C) →
                     {x in z | proj1 (B ∪ C) A x ∈ B} ∈ A ^ B) as Z.
  { intros A B C z H.
    apply Specify_classification in H as [H [H0 H1]].
    apply Specify_classification.
    rewrite -> Powerset_classification.
    assert ({x in z | proj1 (B ∪ C) A x ∈ B} ⊂ B × A).
    { intros x H2.
      apply Specify_classification in H2 as [H2 H3].
      apply H0, Product_classification in H2 as [b [a [H2 [H4 H5]]]].
      subst.
      rewrite -> proj1_eval, Product_classification in *; eauto. }
    repeat split; auto.
    intros x H3.
    destruct (H1 x) as [y [[H4 H5] H6]];
      try (apply Pairwise_union_classification; tauto).
    exists y.
    repeat split; auto.
    + rewrite -> Specify_classification, proj1_eval; auto.
      apply Pairwise_union_classification; tauto.
    + intros x' [H7 H8].
      rewrite -> Specify_classification in H8.
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
    rewrite -> Union_comm in *; auto. }
  exists f.
  repeat split; auto.
  - rewrite -> Injective_classification.
    intros u v H3 H4 H5.
    rewrite -> ? H2 in H5; try congruence.
    apply Extensionality.
    rewrite -> H0 in *.
    apply Specify_classification in H3 as [H3 _].
    apply Specify_classification in H4 as [H4 _].
    rewrite -> Powerset_classification in *.
    apply Ordered_pair_iff in H5 as [H5 H6].
    move=> z; wlog: u v z H3 H4 H5 H6 / z ∈ u.
    { split; intros H7; [ apply (x u v z) | apply (x v u z) ]; auto. }
    split; intros H8; try tauto.
    apply H3, Product_classification in H8 as [y [x [H8 [H9 H10]]]].
    apply Pairwise_union_classification in H8 as H11.
    clear Z H H0 H1 H2 H3 H4.
    wlog: B C y H5 H6 H8 H10 H11 / y ∈ B.
    { destruct H11 as [H11 | H11]; [ | rewrite -> Union_comm in * ]; eauto. }
    intros H.
    assert (z ∈ {x in v | proj1 (B ∪ C) A x ∈ B}) as H0.
    { rewrite <-H5.
      apply Specify_classification.
      subst.
      rewrite -> proj1_eval; auto. }
    apply Specify_classification in H0; tauto.
  - rewrite -> Surjective_classification.
    intros y H3.
    rewrite -> H1, Product_classification in H3.
    destruct H3 as [u [v [H3 [H4 H5]]]].
    exists (u ∪ v).
    apply Specify_classification in H3 as [H3 [H6 H7]], H4 as [H4 [H8 H9]].
    assert (u ∪ v ∈ A ^ (B ∪ C)) as H10.
    { apply Specify_classification.
      rewrite -> Powerset_classification.
      assert (u ∪ v ⊂ (B ∪ C) × A) as H10.
      { intros z H10.
        apply Pairwise_union_classification in H10.
        clear H5 H f H0 H1 H2 Z y.
        wlog: A B C u v z H3 H4 H6 H7 H8 H9 H10 / z ∈ u.
        - intros x.
          destruct H10; eauto.
          rewrite -> Union_comm; eauto.
        - clear H10; intros H.
          apply H6 in H as H0.
          apply Product_classification in H0 as [b [a [H0 [H1 H2]]]].
          apply Product_classification.
          exists b, a.
          repeat split; auto.
          apply Pairwise_union_classification; auto. }
      repeat split; auto.
      intros a H11.
      apply Pairwise_union_classification in H11.
      clear Z f H0 H1 H2 y H5.
      wlog: A B C a u v H H3 H4 H6 H7 H8 H9 H10 H11 / a ∈ B.
      { destruct H11; [ | rewrite -> (Union_comm B C), (Union_comm u v),
                          Intersection_comm in * ]; eauto. }
      clear H11; intros H0.
      apply H7 in H0 as [z [[H0 H1] H2]].
      exists z.
      repeat split; auto.
      - apply Pairwise_union_classification; auto.
      - intros x' [H5 H11].
        apply H2.
        apply Pairwise_union_classification in H11 as [H11 | H11]; try tauto.
        contradiction (Empty_set_classification a).
        rewrite <-H.
        apply Pairwise_intersection_classification.
        apply H6, Product_classification in H1 as [c [d [H1 [H12 H13]]]].
        apply H8, Product_classification in H11 as [e [g [H11 [H14 H15]]]].
        rewrite -> Ordered_pair_iff in *.
        intuition; subst; auto. }
    repeat split; try congruence.
    rewrite -> H2; subst; auto.
    enough (∀ X Y W a b : set, Y ∩ W = ∅ → a ⊂ Y × X → b ⊂ W × X →
                               a = {x in a ∪ b | proj1 (Y ∪ W) X x ∈ Y}).
    { replace {x in u ∪ v | proj1 (B ∪ C) A x ∈ B} with u; auto.
      replace {x in u ∪ v | proj1 (B ∪ C) A x ∈ C} with v;
        rewrite -> (Union_comm B C), Union_comm, Intersection_comm in *; auto. }
    clear.
    intros X Y W a b H H0 H1.
    apply Extensionality.
    split; intros H2.
    + apply Specify_classification.
      split.
      * apply Pairwise_union_classification; auto.
      * apply H0, Product_classification in H2 as [x [y [H2 [H3 H4]]]].
        subst.
        rewrite -> proj1_eval; auto.
        apply Pairwise_union_classification; tauto.
    + apply Specify_classification in H2 as [H2 H3].
      apply Pairwise_union_classification in H2 as [H2 | H2]; auto.
      contradiction (Empty_set_classification (proj1 (Y ∪ W) X z)).
      rewrite <-H, Pairwise_intersection_classification.
      split; auto.
      apply H1, Product_classification in H2 as [x [y [H2 [H4 H5]]]].
      subst.
      rewrite -> proj1_eval in *; auto;
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
    rewrite -> Powerset_classification.
    assert ({(n,a),(n,a)} ⊂ {n,n} × m) as H0.
    { intros x H0.
      rewrite -> Singleton_classification, Product_classification in *.
      exists n, a.
      now rewrite -> Singleton_classification. }
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
  - rewrite -> Injective_classification.
    intros x y H2 H3 H4.
    rewrite -> ? H1 in H4; try congruence.
    assert ((n,x) ∈ {(n,y),(n,y)}) as H5.
    { rewrite <-H4.
      now apply Singleton_classification. }
    now apply Singleton_classification, Ordered_pair_iff in H5.
  - rewrite -> Surjective_classification.
    intros y H2.
    rewrite -> H0 in H2.
    apply Specify_classification in H2 as [H2 [H3 H4]].
    destruct (H4 n) as [a [[H5 H6] H7]]; try now apply Singleton_classification.
    exists a.
    split; try congruence.
    rewrite -> H1; auto.
    apply Extensionality.
    split; intros H8; try (apply Singleton_classification in H8; congruence).
    apply H3 in H8 as H9.
    apply Product_classification in H9 as [c [d [H9 [H10 H11]]]].
    rewrite -> Singleton_classification, (H7 d) in *; subst; intuition.
Qed.

Theorem natural_powers_are_finite : ∀ m n : N, finite (m^n).
Proof.
  intros m n.
  induction n as [| n [x H]] using Induction.
  - rewrite -> power_0_r, (reify PA1_ω).
    apply (naturals_are_finite 1).
  - rewrite <-S_is_succ.
    unfold succ.
    rewrite -> power_union_r, H, power_1_r;
      auto using disjoint_succ, finite_products_are_finite, naturals_are_finite.
Qed.

Theorem natural_powers_card : ∀ m n : N, # (m^n) = ((# m)^(# n))%N.
Proof.
  intros m n.
  induction n using Induction.
  - now rewrite -> ? card_of_natural, power_0_r, pow_0_r, <-(card_of_natural 1).
  - rewrite <-S_is_succ.
    unfold succ.
    now rewrite -> power_union_r, finite_union_cardinality, singleton_card,
    pow_add_r, pow_1_r, power_1_r, finite_products_card, IHn;
      auto using naturals_are_finite, disjoint_succ, singletons_are_finite,
      natural_powers_are_finite.
Qed.

Add Morphism power with signature
    equinumerous ==> equinumerous ==> equinumerous as power_equiv.
Proof.
  intros A C [f [H [H0 [H1 H2]]]] B D [g [H3 [H4 [H5 H6]]]].
  rewrite -> Injective_classification, Surjective_classification in *.
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
        rewrite -> H7 in H11.
        apply function_maps_domain_to_range in H4 as H12.
        apply Specify_classification.
        repeat split.
        * apply Product_classification; eauto.
        * exists (x', y).
          repeat split; auto; rewrite -> ? proj1_eval, ? proj2_eval; auto.
      + intros z [H11 H12].
        apply Specify_classification in H12 as [H12 [x [H13 [H14 H15]]]].
        apply H0 in H13 as H16.
        apply Product_classification in H16 as [a [b [H16 [H17 H18]]]].
        subst.
        rewrite -> ? proj1_eval, ? proj2_eval in *; auto;
          try now apply function_maps_domain_to_range.
        apply H5 in H14; auto.
        subst.
        rewrite -> (H9 b); auto. }
  exists h.
  repeat split; auto.
  - rewrite -> Injective_classification.
    intros x y H H0 H3.
    rewrite -> ? H9 in H3; try congruence.
    pose proof H as H4.
    pose proof H0 as H10.
    rewrite -> H7 in H4, H10.
    apply Specify_classification in H4 as [H4 [H11 H12]].
    apply Specify_classification in H10 as [H10 [H13 H14]].
    apply Extensionality.
    clear H2 H6 h H9 H7 H8 H H0.
    move=> z; wlog: x y z H3 H4 H10 H11 H12 H13 H14 / z ∈ x.
    + split; intros H; [ apply (x0 x y z) | apply (x0 y x z) ]; auto.
    + intros H15; split; intros H; try tauto.
      apply H11 in H15 as H16.
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
          rewrite -> ? proj1_eval, ? proj2_eval; auto;
            now apply function_maps_domain_to_range. }
      rewrite -> H3 in H18.
      apply Specify_classification in H18 as [H18 [z [H19 [H20 H21]]]].
      apply H13 in H19 as H22.
      apply Product_classification in H22 as [a' [b' [H22 [H23 H24]]]].
      subst.
      rewrite -> ? proj1_eval, ? proj2_eval in *; auto;
        try now apply function_maps_domain_to_range.
      apply H1 in H21; apply H5 in H20; subst; auto.
  - rewrite -> Surjective_classification.
    intros y H.
    rewrite -> H8 in H.
    apply Specify_classification in H as [H [H0 H3]].
    exists {z in domain g × domain f |
             (g (proj1 (domain g) (domain f) z),
              f (proj2 (domain g) (domain f) z)) ∈ y}.
    split.
    + rewrite -> H7.
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
        -- rewrite -> Specify_classification, Product_classification.
           split; eauto.
           rewrite -> proj1_eval, proj2_eval, H13; auto.
        -- intros x' [H14 H15].
           apply Specify_classification in H15 as [H15 H16].
           rewrite -> proj1_eval, proj2_eval in H16; auto.
           destruct (H3 (g a)) as [y' [[H18 H19] H20]];
             try now apply function_maps_domain_to_range.
           assert (y' = f x').
           { apply H20.
             split; auto; now apply function_maps_domain_to_range. }
           assert (y' = f z).
           { apply H20.
             split; auto; try now apply function_maps_domain_to_range.
             now rewrite -> H13. }
           apply H1; try congruence.
    + rewrite -> H9.
      * apply Extensionality.
        split; intros H10.
        -- apply Specify_classification in H10 as [H10 [x [H11 [H12 H13]]]].
           apply Specify_classification in H11 as [H11 H14].
           rewrite -> H12, H13 in H14.
           apply Product_classification in H10 as [a [b [H10 [H15 H16]]]].
           subst.
           rewrite -> proj1_eval, proj2_eval in *; auto.
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
             rewrite -> ? Specify_classification, ? Product_classification,
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
           ++ rewrite -> Specify_classification, Product_classification,
              proj1_eval, proj2_eval; repeat split; eauto.
           ++ intros x' [H13 H14].
              apply Specify_classification in H14 as [H14 H16].
              apply H1; auto.
              apply H12.
              split; rewrite -> ? proj1_eval, ? proj2_eval in *; auto.
              now apply function_maps_domain_to_range.
Qed.

Theorem finite_powers_are_finite : ∀ E F, finite E → finite F → finite (E^F).
Proof.
  intros E F [n H] [m H0].
  rewrite -> H, H0; auto using natural_powers_are_finite.
Qed.

Theorem finite_power_card : ∀ E F, finite E → finite F → #(E^F) = ((#E)^(#F))%N.
Proof.
  intros E F [n H] [m H0].
  now rewrite -> H, H0, natural_powers_card.
Qed.

Definition bijection_set A B :=
  { f in P (A × B) |
    ∃ f', domain f' = A ∧ range f' = B ∧ graph f' = f ∧ bijective f'}.

Definition size_of_bijections A B := # (bijection_set A B).

Theorem equinumerous_cardinality : ∀ A B, A ~ B → # A = # B.
Proof.
  intros A B H.
  now rewrite -> H.
Qed.

Theorem finite_cardinality_equinumerous :
  ∀ A B, finite A → finite B → # A = # B → A ~ B.
Proof.
  intros A B H H0 H1.
  now rewrite (card_equiv A H) (card_equiv B H0) H1.
Qed.

Definition inverse_function_out : set → set → set → set.
Proof.
  intros A B f.
  destruct (excluded_middle_informative (f ∈ bijection_set A B)).
  - apply Specify_classification in i as [H H0].
    destruct (constructive_indefinite_description H0) as [f' [H1 [H2 [H3 H4]]]].
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
      rewrite -> inverse_domain, inverse_range in H0; congruence.
    - exists (inverse g).
      rewrite -> inverse_domain, inverse_range; auto using inverse_bijective. }
  exists f.
  repeat split; auto.
  - rewrite -> Injective_classification.
    intros x y H2 H3 H4.
    rewrite -> H in *.
    rewrite -> ? H1 in H4; auto.
    unfold inverse_function_out in H4.
    repeat destruct excluded_middle_informative; try tauto.
    repeat destruct Specify_classification.
    destruct a, a0.
    repeat destruct constructive_indefinite_description.
    repeat destruct a1, a2.
    rewrite <-e5, <-e6, <-(function_inv_inv x0), <-(function_inv_inv x1); auto.
    do 2 f_equal.
    apply function_record_injective; auto.
    rewrite -> ? inverse_range; congruence.
  - rewrite -> Surjective_classification.
    intros y H2.
    rewrite -> H0 in H2.
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
          rewrite -> inverse_domain, inverse_range in *; congruence.
      - exists (inverse g).
        rewrite inverse_domain ? inverse_range; auto using inverse_bijective. }
    split; try now rewrite -> H.
    rewrite -> H1; auto.
    unfold inverse_function_out.
    destruct excluded_middle_informative; try tauto.
    destruct Specify_classification, a.
    destruct constructive_indefinite_description as [h].
    repeat destruct a0.
    rewrite <-H5.
    replace h with (inverse g).
    + rewrite -> function_inv_inv; auto.
    + apply function_record_injective; auto.
      rewrite -> inverse_range; congruence.
Qed.

Theorem size_of_bijections_sym :
  ∀ A B, size_of_bijections A B = size_of_bijections B A.
Proof.
  intros A B.
  eauto using equinumerous_cardinality, bijection_set_sym.
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
      destruct (constructive_indefinite_description H1)
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
    - eauto using Specify_classification.
    - destruct constructive_indefinite_description as [g].
      repeat destruct a.
      apply Specify_classification.
      destruct (Composition_classification g f) as [H3 [H4 _]]; try congruence.
      split.
      + apply Powerset_classification.
        intros z H5.
        apply graph_elements_are_pairs in H5.
        congruence.
      + exists (g ∘ f).
        destruct H, b.
        repeat split; eauto using composition_injective,
                      composition_surjective, eq_trans.
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
  - rewrite -> Injective_classification.
    intros x y H5 H6 H7.
    subst.
    rewrite -> ? H4 in H7; try congruence.
    rewrite -> H2 in H5, H6.
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
    rewrite -> Surjective_classification in H17.
    destruct (H17 z) as [w [H18 H19]]; try congruence.
    subst.
    rewrite <-H10, <-H13, H14; auto.
  - rewrite -> Surjective_classification.
    intros y H5.
    rewrite -> H3 in H5.
    assert (bijective (inverse f)) as H6 by now apply inverse_bijective.
    exists (inverse_function_shift C (inverse f) y).
    split.
    { rewrite -> H2, <-H0, <-inverse_domain; auto.
      apply inverse_function_shift_in_A_C; auto.
      rewrite -> inverse_range; auto; congruence. }
    rewrite -> H4;
      try (rewrite <-H0, <-inverse_domain; auto;
           apply inverse_function_shift_in_A_C; auto;
           rewrite -> inverse_range; auto; congruence).
    unfold inverse_function_shift at 1.
    repeat destruct excluded_middle_informative;
    try (contradict n; rewrite <-inverse_domain; auto;
         apply inverse_function_shift_in_A_C; auto;
         rewrite -> inverse_range; auto; congruence).
    destruct Specify_classification, a, constructive_indefinite_description.
    repeat destruct a0.
    unfold inverse_function_shift in e2.
    destruct excluded_middle_informative;
      try now rewrite -> inverse_range, H in n.
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
    { now rewrite -> H7, inverse_domain. }
    replace x with (x0 ∘ inverse f).
    + apply func_ext; try congruence.
      * now rewrite -> H13, e4, inverse_range.
      * intros x1 H16.
        rewrite -> H15, H9, ? left_inverse; auto; try congruence.
        rewrite -> inverse_domain; auto.
        apply function_maps_domain_to_range.
        congruence.
    + apply function_record_injective; try congruence.
Qed.

Lemma size_of_bijections_wf : ∀ A B C,
    A ~ B → size_of_bijections A C = size_of_bijections B C.
Proof.
  intros A B C H.
  eauto using equinumerous_cardinality, bijection_set_wf.
Qed.

Add Morphism bijection_set with signature
    equinumerous ==> equinumerous ==> equinumerous as bijection_set_equiv.
Proof.
  intros x y H x0 y0 H0.
  eapply bijection_set_wf in H, H0.
  rewrite -> (bijection_set_sym y), (bijection_set_sym x) in *.
  now rewrite -> H, H0.
Qed.

Add Morphism size_of_bijections with signature
    equinumerous ==> equinumerous ==> eq as size_of_bijections_equiv.
Proof.
  intros x y H x0 y0 H0.
  eapply size_of_bijections_wf in H, H0.
  rewrite -> (size_of_bijections_sym y), (size_of_bijections_sym x) in *.
  now rewrite -> H, H0.
Qed.

Lemma finite_subsets_bijective : ∀ E F, finite F → E ⊂ F → E ~ F → E = F.
Proof.
  intros E F H H0 H1.
  apply Subset_equality_iff, conj; auto.
  apply equinumerous_cardinality in H1.
  apply Union_subset in H0 as H2.
  rewrite <-H2, disjoint_union_complement, finite_union_cardinality in H1;
    eauto using disjoint_intersection_complement,
    subsets_of_finites_are_finite, complement_subset.
  rewrite <-(add_0_r (# E)) in H1 at 1.
  apply naturals.cancellation_add, eq_sym in H1.
  assert (# (F \ E) ~ 0%N) as H3 by now rewrite -> H1.
  rewrite <- card_equiv in H3;
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
  rewrite -> Surjective_classification.
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
    set (f := mkFunc H0).
    assert ({x in X | f x = 1} ∈ P X).
    { apply Powerset_classification.
      intros z H1.
      apply Specify_classification in H1.
      tauto. }
    exact (mkSet H1).
  Defined.

  Theorem powerset_powers : 2^X ~ P X.
  Proof.
    exists (functionify powerset_bijection_helper).
    rewrite -> functionify_domain, functionify_range.
    repeat split; auto.
    - apply Injective_classification.
      intros x y H H0 H1.
      rewrite -> @functionify_domain, (reify H), (reify H0),
      ? @functionify_action in *.
      unfold powerset_bijection_helper in *.
      repeat destruct Specify_classification.
      destruct a, a0.
      simpl in H1 |-*.
      set (f := (mkFunc i2)).
      set (g := (mkFunc i4)).
      assert (x = graph f) as H2 by auto.
      assert (y = graph g) as H3 by auto.
      rewrite -> H2, H3.
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
      rewrite -> Pairwise_union_classification, Union_comm, Union_empty,
      Singleton_classification in H5, H6.
      rewrite -> Union_comm, Union_empty, Singleton_classification in *.
      destruct H5, H6; try congruence.
      + assert (z ∈ {x in X | g x = {∅,∅}}) as H7
            by now apply Specify_classification.
        rewrite <-H1 in H7.
        apply Specify_classification in H7 as [H7 H8].
        congruence.
      + assert (z ∈ {x in X | f x = {∅,∅}}) as H7
            by now apply Specify_classification.
        rewrite -> H1 in H7.
        apply Specify_classification in H7 as [H7 H8].
        congruence.
    - rewrite -> Surjective_classification.
      assert (1 ∈ 2) as Z.
      { now apply Pairwise_union_classification, or_intror,
        Singleton_classification. }
      assert (0 ∈ 2) as Z0.
      { now apply Pairwise_union_classification, or_introl,
        Pairwise_union_classification, or_intror, Singleton_classification. }
      intros y H.
      rewrite -> @functionify_range, functionify_domain in *.
      exists {z in X × 2 | proj2 X 2 z = 1 ↔ proj1 X 2 z ∈ y}.
      assert ({z in X × 2 | proj2 X 2 z = 1 ↔ proj1 X 2 z ∈ y} ∈ 2 ^ X) as Z1.
      { apply Specify_classification.
        rewrite -> Powerset_classification.
        repeat split; intros z H0;
          try (apply Specify_classification in H0; tauto).
        exists (If z ∈ y then 1 else 0).
        destruct excluded_middle_informative; split.
        - rewrite -> Specify_classification, proj1_eval, proj2_eval,
          Product_classification; repeat split; eauto.
        - intros x' [H1 H2].
          apply Specify_classification in H2 as [H2 H3].
          rewrite -> proj1_eval, proj2_eval in H3; intuition.
        - rewrite -> Specify_classification, proj1_eval, proj2_eval,
          Product_classification; repeat split; eauto; intros H1; try tauto.
          now apply set_proj_injective, neq_succ in H1.
        - intros x' [H1 H2].
          apply Specify_classification in H2 as [H2 H3].
          rewrite -> proj1_eval, proj2_eval in H3; intuition.
          apply Pairwise_union_classification in H1 as [H1 | H1].
          * unfold succ in H1.
            now rewrite -> Union_comm, Union_empty,
            Singleton_classification in H1.
          * rewrite -> Singleton_classification in H1.
            now apply H4 in H1. }
      split; auto.
      rewrite -> (reify Z1), functionify_action.
      unfold powerset_bijection_helper.
      destruct Specify_classification, a.
      simpl.
      clear a i.
      apply Extensionality.
      set (f := mkFunc i1).
      split; intros H0.
      + apply Specify_classification in H0 as [H0 H1].
        assert (f z = 1) as H2 by auto.
        apply function_maps_domain_to_graph in H2; simpl in H2 |-*; auto.
        apply Specify_classification in H2 as [H2 H3].
        rewrite -> proj1_eval, proj2_eval in H3; tauto.
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
        * rewrite -> proj1_eval, proj2_eval; intuition.
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
    rewrite -> disjoint_union_complement, finite_union_cardinality,
    naturals.add_comm, sub_abba;
      eauto using subsets_of_finites_are_finite, complement_subset,
      disjoint_intersection_complement.
  - unfold finite_cardinality.
    destruct excluded_middle_informative at 2; try tauto.
    rewrite -> sub_0_l.
    destruct excluded_middle_informative; auto.
    contradict n.
    rewrite <-H1, disjoint_union_complement.
    now apply finite_unions_are_finite.
Qed.

Theorem pairing_card : ∀ x y, x ≠ y → {x,y} ~ 2.
Proof.
  intros x y H.
  apply Pairing_intersection_disjoint in H.
  now rewrite -> Pairing_union_singleton, finite_union_equinumerosity,
  ? singleton_card, add_1_r; eauto using singletons_are_finite.
Qed.
