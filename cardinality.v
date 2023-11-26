Require Export ssreflect ssrbool ssrfun naturals Setoid.
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
  move=>
  E n [f [<- [<- [/Injective_classification H /Surjective_classification H0]]]]
    F m [g [<- [<- [/Injective_classification H1
                     /Surjective_classification H2]]]].
  elim (function_construction
          (domain f × domain g) (range f × range g)
          (λ z, (f (proj1 (domain f) (domain g) z),
                 g (proj2 (domain f) (domain g) z)))) =>
  [h [H3 [H4 H5]] | z /Product_classification [a [b [H3 [H4 ->]]]]].
  - exists h.
    rewrite /bijective Injective_classification Surjective_classification.
    (repeat split; auto) => [x y /[dup] H6 /[swap] /[dup] H7 | z].
    + rewrite ? H5 -? H3 // ? H3 =>
      /[swap] /Product_classification [a [b [H8 [H9 ->]]]]
       /Product_classification [c [d [H10 [H11 ->]]]].
      rewrite ? pro1j_eval ? proj2_eval ? proj1_eval // =>
      /Ordered_pair_iff [/H] /[swap] /H1; intuition congruence.
    + rewrite H3 H4 => /Product_classification
                        [a [b [/H0 [x [H6 <-]] [/H2 [y [H7 <-]]] ->]]].
      exists (x,y).
      rewrite ? H5 ? Product_classification ? proj1_eval ? proj2_eval;
        repeat split; eauto.
  - rewrite proj1_eval ? proj2_eval ? Product_classification //.
    repeat esplit; eauto using function_maps_domain_to_range.
Qed.

Theorem finite_products_are_finite :
  ∀ E F, finite E → finite F → finite (E × F).
Proof.
  move=> E F [n ->] [m ->].
  auto using natural_products_are_finite.
Qed.

Theorem finite_products_card :
  ∀ E F, finite E → finite F → # (E × F) = (# E) * (# F).
Proof.
  move=> E F [n ->] [m ->].
  auto using natural_prod_card.
Qed.

Theorem power_union_r : ∀ A B C, B ∩ C = ∅ → A ^ (B ∪ C) ~ A ^ B × A ^ C.
Proof.
  have Z:
    ∀ A B C z, z ∈ A ^ (B ∪ C) → {x in z | proj1 (B ∪ C) A x ∈ B} ∈ A ^ B
  => [A B C z /Specify_classification [H [H0 H1]] | A B C H].
  { rewrite Specify_classification Powerset_classification.
    have: {x in z | proj1 (B ∪ C) A x ∈ B} ⊂ B × A =>
    [x /Specify_classification
       [/H0 /Product_classification [b [a [H2 [H3 ->]]]]] | ];
      first by rewrite proj1_eval ? Product_classification; eauto.
    (repeat split; auto) => a /[dup] H3 /Union_left =>
    /(_ C) /H1 [y [[H4 H5] H6]].
    exists y.
    repeat split => // =>
    [ | x' [H7]]; rewrite Specify_classification ? rewrite proj1_eval;
      try apply Union_left; intuition. }
  elim (function_construction
          (A ^ (B ∪ C)) (A ^ B × A ^ C)
          (λ z, ({x in z | proj1 (B ∪ C) A x ∈ B},
                 {x in z | proj1 (B ∪ C) A x ∈ C}))) =>
  [f [/[dup] H0 <- [H1 H2]] | z /[dup]].
  2: { rewrite {2 4}Union_comm => *.
       eapply Product_classification, ex_intro, ex_intro, conj, conj; eauto. }
  (do 2 esplit; repeat split; eauto;
   rewrite ? Injective_classification ? Surjective_classification) => [u v | y].
  - move: H0 => /[swap] /[dup] H3 /[swap] /[dup] {2}->
                /[swap] /Specify_classification [/Powerset_classification H4 _]
                 /[swap] /[dup] H5 /[swap] -> /Specify_classification
                                               [/Powerset_classification H6 _].
    rewrite ? H2 // => /Ordered_pair_iff [H7 H8].
    apply Extensionality.
    move=> z; wlog: u v z H3 H4 H5 H6 H7 H8 / z ∈ u.
    { split => *; [ apply (H0 u v z) | apply (H0 v u z) ]; auto. }
    (split; try tauto) =>
    /H4 /Product_classification
     [y [x [/Pairwise_union_classification H9 [H10 H11]]]] =>
    {Z H H1 H2 H3 H4 H5 H6}.
    wlog: B C y H7 H8 H9 H10 H11 / y ∈ B => [ | /[dup] H /(Union_left _ C) H1].
    { elim H9 => *; [ | rewrite Union_comm in H7 H8 ]; eauto. }
    have: z ∈ {x in v | proj1 (B ∪ C) A x ∈ B} =>
    [ | /Specify_classification]; last by tauto.
    move: H11 H0 H7 -> => H0 <-.
    apply Specify_classification.
    rewrite proj1_eval //.
  - move: H1 -> => /Product_classification
                    [u [v [/Specify_classification [H3 [H4 H5]]
                            [/Specify_classification [H6 [H7 H8]] H9]]]].
    exists (u ∪ v).
    have: u ∪ v ∈ A ^ (B ∪ C).
    { rewrite Specify_classification Powerset_classification.
      have: u ∪ v ⊂ (B ∪ C) × A => [z /Pairwise_union_classification H10 | ].
      { rewrite Product_union_distr_l Pairwise_union_classification.
        intuition eauto. }
      repeat split; auto => a /Pairwise_union_classification H10.
      clear Z f H0 H2 H3 H6 H9 H1.
      wlog: A B C a u v H H4 H5 H7 H8 H10 y / a ∈ B =>
      [ | {H10} /[dup] H10 /H5 [z [[H0 /[dup] /H4 /Product_in_left
                                       H1 /(Union_left _ v) H2] H3]]].
      { elim H10; [ | rewrite ? (Union_comm B C) ? (Union_comm u v)
                              1 ? Intersection_comm in H y |-* ]; eauto. }
      exists z.
      repeat split; auto =>
      x' [H6 /Pairwise_union_classification [H9 | /H7 /Product_in_left H9]];
        apply H3 => //.
      contradiction (Empty_set_classification a).
      rewrite -H Pairwise_intersection_classification //. }
    move: H0 => /[swap] /[dup] H0 /[swap] <- H1.
    split; auto.
    rewrite H2 //.
    suff H10: (∀ X Y W a b : set, Y ∩ W = ∅ → a ⊂ Y × X → b ⊂ W × X →
                                  a = {x in a ∪ b | proj1 (Y ∪ W) X x ∈ Y}).
    { suff <- : u = {x in u ∪ v | proj1 (B ∪ C) A x ∈ B}; auto.
      suff <- : v = {x in u ∪ v | proj1 (B ∪ C) A x ∈ C};
        rewrite (Union_comm B C) Union_comm
                Intersection_comm in H0 H |-*; auto. }
    clear => X Y W a b H H0 H1.
    apply Extensionality => z.
    split =>
    [/[dup] /H0 /Product_classification
      [x [y [/[dup] H2 /(Union_left _ W) H3 [H4 ->]]]] /(Union_left _ b) H5 |
     /Specify_classification
      [/Pairwise_union_classification
        [H2 | /H1 /Product_classification
               [x [y [/[dup] H2 /(Union_right Y) H3 [H4 ->]]]]] H5]]; auto.
    + rewrite Specify_classification proj1_eval //.
    + contradiction (Empty_set_classification (proj1 (Y ∪ W) X (x, y))).
      rewrite -H Pairwise_intersection_classification {2}proj1_eval //.
Qed.

Theorem power_1_r : ∀ m n, m^{n,n} ~ m.
Proof.
  move=> m n.
  symmetry.
  elim (function_construction m (m^{n,n}) (λ x, {(n,x),(n,x)}))
  => [f [H [H0 H1]] | a H].
  - exists f.
    rewrite /bijective Injective_classification Surjective_classification.
    (repeat split; auto) => [x y | y].
    + move: H H1 -> => /[swap] H2 /[swap] H3 /[dup] -> // -> //.
      move: (in_singleton (n,x)) =>
      /[swap] -> /Singleton_classification /Ordered_pair_iff [] //.
    + move: (H) H0 (in_singleton n) -> => -> =>
      /[swap] /Specify_classification [? [H2 /(_ n)]] /[apply] [[a [[? ?] H3]]].
      exists a.
      rewrite H1; repeat split; auto.
      apply Extensionality => z.
      split => [/Singleton_classification -> |
                /[dup] /H2 /Product_classification
                 [c [d [/Singleton_classification -> [? ->] ?]]]] //.
      apply Singleton_classification, Ordered_pair_iff,
      conj, eq_sym, H3, conj => //.
  - rewrite Specify_classification Powerset_classification.
    have H0: {(n,a),(n,a)} ⊂ {n,n} × m => [x | ].
    { rewrite Singleton_classification Product_classification.
      exists n, a.
      rewrite Singleton_classification //. }
    (repeat split; auto) => a' /Singleton_classification ->.
    exists a.
    ((repeat split; auto) => [ | x']);
    rewrite ? Singleton_classification // ? Ordered_pair_iff => [[]] _ [] //.
Qed.

Theorem natural_powers_are_finite : ∀ m n : N, finite (m^n).
Proof.
  move /[swap].
  elim/Induction
  => *; rewrite ? power_0_r -? S_is_succ /succ ? power_union_r ? power_1_r;
       auto using finite_products_are_finite, naturals_are_finite,
       disjoint_succ, (naturals_are_finite 1).
Qed.

Theorem natural_powers_card : ∀ m n : N, # (m^n) = ((# m)^(# n))%N.
Proof.
  move /[swap].
  elim/Induction => [m | n IH m].
  - rewrite ? card_of_natural power_0_r pow_0_r -(card_of_natural 1) //.
  - rewrite
    -S_is_succ /succ power_union_r ? disjoint_succ // finite_union_cardinality
               ? disjoint_succ // ? singleton_card ? pow_add_r ? pow_1_r
               ? power_1_r ? finite_products_card ? IH //;
               auto using naturals_are_finite, singletons_are_finite,
    natural_powers_are_finite.
Qed.

Add Morphism power with signature
    equinumerous ==> equinumerous ==> equinumerous as power_equiv.
Proof.
  move=> A C [f [<- [<- [/Injective_classification H
                          /Surjective_classification H0]]]] B D
           [g [<- [<- [/Injective_classification H1
                        /Surjective_classification H2]]]].
  elim (function_construction
          ((domain f)^(domain g)) ((range f)^(range g))
          (λ S, {z in (range g) × (range f) |
                  ∃ x, x ∈ S ∧ g (proj1 (domain g) (domain f) x) =
                               proj1 (range g) (range f) z ∧
                       f (proj2 (domain g) (domain f) x) =
                       proj2 (range g) (range f) z})) =>
  [h [H3 [H4 H5]] | φ /Specify_classification [H3 [H4 H5]]].
  - exists h.
    rewrite /bijective Injective_classification Surjective_classification.
    (repeat split; auto) => [x y H6 H7 | y].
    + move: H3 H6 H7 H5 (H5) -> =>
      /[dup] H3 /Specify_classification [_ [H6 H7]] /[dup] H8
       /Specify_classification [_ [H9 H10]] -> // -> // H11.
      apply Extensionality => z {A B C D H0 H2 h H3 H4 H8}.
      wlog: x y z H H1 H6 H7 H9 H10 H11 / z ∈ x.
      * split => *; [ apply (H0 x y z) | apply (H0 y x z) ]; auto.
      * split => [/[dup] /[swap] /H6 /Product_classification
                   [a [b [H2 [H3 ->]]] H4 {z H0}] | H2] //.
        have: (g a, f b) ∈ {z in range g × range f | ∃ x0 : set,
                              x0 ∈ x ∧ g (proj1 (domain g) (domain f) x0) =
                                       proj1 (range g) (range f) z
                              ∧ f (proj2 (domain g) (domain f) x0) =
                                proj2 (range g) (range f) z}.
        { apply Specify_classification, conj.
          - apply Product_classification.
            exists (g a), (f b).
            repeat split; auto; now apply function_maps_domain_to_range.
          - exists (a, b).
            rewrite ? proj1_eval ? proj2_eval;
              auto using function_maps_domain_to_range. }
        rewrite H11 Specify_classification =>
        [[H0 [z [/[dup] /H9 /Product_classification [a' [b' [? [? ->] ?]]]]]]].
        rewrite ? proj1_eval ? proj2_eval;
          auto using function_maps_domain_to_range =>
        [[]] /H1 /[swap] /H; intuition congruence.
    + move: (H3) (H4) -> => -> => /Specify_classification [_ [H6 H7]].
      exists {z in domain g × domain f |
               (g (proj1 (domain g) (domain f) z),
                f (proj2 (domain g) (domain f) z)) ∈ y}.
      have H8: {z in domain g × domain f |
                 (g (proj1 (domain g) (domain f) z),
                  f (proj2 (domain g) (domain f) z)) ∈ y} ∈ domain f ^ domain g.
      { (apply Specify_classification, conj, conj;
         rewrite ? Powerset_classification) =>
        [z /Specify_classification [] | z /Specify_classification [] |
         z /[dup] H8 /function_maps_domain_to_range /H7
           [x [[/H0 [w [] /[swap] <- H9] H11] H12]]] //.
        exists w.
        (repeat split; auto;
          first by rewrite Specify_classification Product_classification
                           proj1_eval ? proj2_eval; intuition eauto)
        => x' [H13 /Specify_classification [H14]].
        rewrite proj1_eval ? proj2_eval //.
        auto using function_maps_domain_to_range. }
      split; rewrite ? H5; auto.
      apply Extensionality => z.
      split => [/Specify_classification
                 [/Product_classification [a [b [H9 [H10 ->]]]]
                   [x [/Specify_classification [] H12 /[swap] [[-> ->]]]]]
               | /[dup] /H6 /Product_classification
                  [a [b [/H2 [c [H10 <-]] [/H0 [d [H12 <-]] ->] H14]]]];
                 first by rewrite proj1_eval ? proj2_eval //.
      apply Specify_classification, conj; auto.
      exists (c, d).
      repeat split;
        rewrite 1 ? Specify_classification ? Product_classification
                ? proj1_eval ? proj2_eval; repeat split;
          eauto using function_maps_domain_to_range.
  - (apply Specify_classification, conj, conj;
     rewrite ? Powerset_classification) =>
    [z /Specify_classification [] | z /Specify_classification [] |
     z /H2 [x [/[dup] H6 /H5 [y [[H7 H8] H9]] H10]]] //.
    exists (f y).
    (repeat split; auto using function_maps_domain_to_range) =>
    [ | x' [H11 /Specify_classification
                [H12 [y' [/[dup] /H4 /Product_classification
                           [a [b [H13 [H14 ->]]]] H15]]]]].
    + move: (H6) (H10) (H7) =>
      /function_maps_domain_to_range /[swap] ->
      /[swap] /function_maps_domain_to_range => H11 H12.
      rewrite Specify_classification Product_classification.
      repeat esplit; eauto; rewrite ? proj1_eval ? proj2_eval //.
    + rewrite ? proj1_eval ? proj2_eval -? H10 //;
              auto using function_maps_domain_to_range =>
      [[]] /(H1 _ _ H13 H6) H16 <-.
      apply /f_equal /H9.
      rewrite -H16 //.
Qed.

Theorem finite_powers_are_finite : ∀ E F, finite E → finite F → finite (E^F).
Proof.
  move=> E F /card_equiv -> /card_equiv ->.
  auto using natural_powers_are_finite.
Qed.

Theorem finite_power_card : ∀ E F, finite E → finite F → #(E^F) = ((#E)^(#F))%N.
Proof.
  move=> E F /card_equiv -> /card_equiv ->.
  auto using natural_powers_card.
Qed.

Definition bijection_set A B :=
  { f in P (A × B) |
    ∃ f', domain f' = A ∧ range f' = B ∧ graph f' = f ∧ bijective f'}.

Definition size_of_bijections A B := # (bijection_set A B).

Theorem equinumerous_cardinality : ∀ A B, A ~ B → # A = # B.
Proof.
  move=> A B -> //.
Qed.

Theorem finite_cardinality_equinumerous :
  ∀ A B, finite A → finite B → # A = # B → A ~ B.
Proof.
  now move=> A B /card_equiv {2}-> /card_equiv {2}-> ->.
Qed.

Definition inverse_function_out : set → set → set → set.
Proof.
  move=> A B f.
  elim (excluded_middle_informative (f ∈ bijection_set A B)) =>
  [/Specify_classification [H /constructive_indefinite_description
                              [f' [H0 [H1 [H2 H3]]]]] | ?].
  - exact (graph (inverse f')).
  - exact ∅.
Defined.

Theorem bijection_set_sym :
  ∀ A B, bijection_set A B ~ bijection_set B A.
Proof.
  move=> A B.
  elim (function_construction
          (bijection_set A B) (bijection_set B A)
          (λ x, inverse_function_out A B x)) => [f [H [H0 H1]] | a H].
  - exists f.
    rewrite /bijective Injective_classification Surjective_classification H H0.
    (repeat split; auto) => [x y H2 H3 | y].
    + rewrite ? H1 // /inverse_function_out /sumbool_rect /=.
      (repeat case excluded_middle_informative; try tauto) => i i0.
      repeat destruct iffLR as [_].
      (repeat elim constructive_indefinite_description) =>
      [x0 [H4 [H5 [H6 [H7 H8]]]]] x1 [H9 [H10 [H11 [H12 H13]]]].
      rewrite -H11 -H6 -{2}(function_inv_inv x0) //
      -{2}(function_inv_inv x1) // => /function_record_injective.
      rewrite ? inverse_range // H4 => -> //.
    + rewrite {1}/bijection_set Specify_classification =>
      [[H2 [g [/[dup] H3 <- [/[dup] H4 <- [H5 H6]]]]]].
      exists (graph (inverse g)).
      have: graph (inverse g) ∈ bijection_set (range g) (domain g).
      { rewrite /bijection_set Specify_classification Powerset_classification.
        split => [x /graph_elements_are_pairs | ]; [ | exists (inverse g) ];
                   rewrite inverse_domain ? inverse_range;
                   auto using inverse_bijective. }
      split; auto.
      rewrite H1 /inverse_function_out /sumbool_rect -H3 -H4; try congruence.
      (elim excluded_middle_informative; try tauto) => H8.
      destruct iffLR as [_].
      elim constructive_indefinite_description => z [H9 [H10 [H11 [H12 H13]]]].
      rewrite -H5 -(function_inv_inv g) //.
      apply f_equal, f_equal, function_record_injective;
        rewrite ? inverse_range //.
  - rewrite /inverse_function_out /sumbool_rect.
    (elim excluded_middle_informative => /=; try tauto) => {}H.
    destruct iffLR as [_].
    elim constructive_indefinite_description => [g [H0 [H1 [H2 H3]]]].
    apply Specify_classification, conj.
    + apply Powerset_classification => z /graph_elements_are_pairs.
      rewrite inverse_domain ? inverse_range; congruence.
    + exists (inverse g).
      rewrite inverse_domain ? inverse_range; auto using inverse_bijective.
Qed.

Theorem size_of_bijections_sym :
  ∀ A B, size_of_bijections A B = size_of_bijections B A.
Proof.
  eauto using equinumerous_cardinality, bijection_set_sym.
Qed.

Section inverse_function_sideload.

  Variable C : set.
  Variable f : function.
  Hypothesis H : bijective f.
  Variable x : set.

  Definition inverse_function_shift : set.
  Proof.
    elim (excluded_middle_informative (x ∈ bijection_set (range f) C)) =>
    [/Specify_classification [H0 /constructive_indefinite_description
                                 [g [H1 [H2 [H3 H4]]]]] | H0].
    - exact (graph (g ∘ f)).
    - exact ∅.
  Defined.

  Lemma inverse_function_shift_in_A_C :
    x ∈ bijection_set (range f) C →
    inverse_function_shift ∈ bijection_set (domain f) C.
  Proof.
    move: H.
    rewrite /inverse_function_shift /sumbool_rect => [[H0 H1] H2].
    (elim excluded_middle_informative; try tauto) => {}H2.
    destruct iffLR as [_].
    elim constructive_indefinite_description => [g [H3 [<- [H4 [H5 H6]]]]].
    rewrite Specify_classification Powerset_classification.
    elim (Composition_classification g f) => [<- [<- _] | ] //.
    split => [z /graph_elements_are_pairs | ] //.
    eapply ex_intro, conj, conj, conj, conj;
      eauto using composition_injective, composition_surjective.
  Qed.

End inverse_function_sideload.

Lemma bijection_set_wf : ∀ A B C,
    A ~ B → bijection_set A C ~ bijection_set B C.
Proof.
  move=> B A C /cardinality_sym [f [<- [<- /[dup] /[dup] H /inverse_bijective IH
                                            [/Injective_classification H0
                                              /Surjective_classification H1]]]].
  elim (function_construction
          (bijection_set (range f) C) (bijection_set (domain f) C)
          (λ x, inverse_function_shift C f x)) =>
  [h [H2 [H3 H4]] | ]; auto using inverse_function_shift_in_A_C.
  exists h.
  rewrite /bijective Injective_classification Surjective_classification ? H2.
  (repeat split; auto) => [x y H5 H6 | y /[dup] H5].
  - rewrite ? H4 // /inverse_function_shift /sumbool_rect.
    (repeat elim excluded_middle_informative; try tauto) => {}H6 {}H5.
    destruct iffLR as [_]; elim constructive_indefinite_description =>
    {e} x0 [H7 [H8 [H9 [/Injective_classification H10
                         /Surjective_classification H11]]]].
    destruct iffLR as [_]; elim constructive_indefinite_description =>
    {e} x1 [H12 [H13 [H14 [/Injective_classification H15
                            /Surjective_classification H16]]]].
    elim (Composition_classification x0 f) => [H17 [H18 H19] | ] //.
    elim (Composition_classification x1 f) =>
    [H20 [H21 H22] | ] // /function_record_injective.
    rewrite -H9 -H14 H18 H21 H8 H13 => /(_ (eq_refl C)) => H23.
    (apply f_equal, func_ext; try congruence) => z.
    rewrite H7 => /H1 [w [H24 <-]].
    rewrite -H19 // -H22 // H23 //.
  - rewrite H3 -inverse_range // =>
    /[dup] H6 /inverse_function_shift_in_A_C => /(_ IH).
    rewrite inverse_domain // => H7.
    exists (inverse_function_shift C (inverse f) y).
    split; auto.
    rewrite H4 // {1}/inverse_function_shift /sumbool_rect.
    (elim excluded_middle_informative; try tauto) => {}H7.
    destruct iffLR as [_]; elim constructive_indefinite_description
    => x [H8 [H9 [/[swap] [[H10 H11]]]]] {e}.
    rewrite /inverse_function_shift /sumbool_rect.
    (elim excluded_middle_informative; try tauto) => {}H7.
    destruct iffLR as [_]; elim constructive_indefinite_description
    => x0 [H12 [H13 [H14 [H15 H16]]]] {e}.
    elim (Composition_classification x0 (inverse f)) => [H17 [H18 H19] | ] //.
    elim (Composition_classification (x0 ∘ inverse f) f) =>
    [H20 [H21 H22] | ] //; last by rewrite -inverse_domain.
    elim (Composition_classification x f) => [H23 [H24 H25] | ] //
    /function_record_injective.
    rewrite H18 H9 H13 -H14 => /(_ (eq_refl C)) ->.
    apply /f_equal /func_ext =>
    //; rewrite ? H12 ? inverse_range -? H18 ? H20 // => x1 H26.
    rewrite H22 // H19 ? inverse_domain ? left_inverse //;
            auto using function_maps_domain_to_range.
    Qed.

Lemma size_of_bijections_wf : ∀ A B C,
    A ~ B → size_of_bijections A C = size_of_bijections B C.
Proof.
  eauto using equinumerous_cardinality, bijection_set_wf.
Qed.

Add Morphism bijection_set with signature
    equinumerous ==> equinumerous ==> equinumerous as bijection_set_equiv.
Proof.
  move=> x y /bijection_set_wf /[swap] x0 /(_ x0)
           /[swap] y0 -> /bijection_set_wf => /(_ y) H0.
  rewrite ? (bijection_set_sym y) //.
Qed.

Add Morphism size_of_bijections with signature
    equinumerous ==> equinumerous ==> eq as size_of_bijections_equiv.
Proof.
  move=> x y /[swap] x0 /size_of_bijections_wf =>
  /(_ x0) /[swap] y0 -> /size_of_bijections_wf => /(_ y) H0.
  rewrite ? (size_of_bijections_sym y) //.
Qed.

Lemma finite_subsets_bijective : ∀ E F, finite F → E ⊂ F → E ~ F → E = F.
Proof.
  move=> E F H /[dup] H0 /Union_subset {1}<- /equinumerous_cardinality.
  rewrite disjoint_union_complement finite_union_cardinality;
    eauto using disjoint_intersection_complement,
    subsets_of_finites_are_finite, complement_subset =>
  /(@eq_sym N) /cancellation_0 /finite_empty => H1.
  rewrite -Subset_equality_iff (Complement_subset F) H1;
    eauto using subsets_of_finites_are_finite, complement_subset.
Qed.

Lemma finite_set_injection_is_bijection :
  ∀ f, finite (domain f) → domain f ~ range f → injective f → bijective f.
Proof.
  move=> f H H0 /[dup] H1 /injective_into_image H2.
  move: (H0) (H0) (H) (H2) => {2}-> -> H3 /cardinality_sym H4.
  rewrite /bijective Surjective_classification.
  suff <- : image f = range f;
    auto using finite_subsets_bijective, image_subset_range.
  split => // z /Specify_classification [] //.
Qed.

Section Powerset_powers.

  Variable X : set.

  Definition powerset_bijection_helper : elts (2^X) → elts (P X).
  Proof.
    move=> [x /Specify_classification [H H0]].
    have H1: {x in X | (mkFunc H0) x = 1} ∈ P X.
    { apply Powerset_classification => z /Specify_classification [] //. }
    exact (mkSet H1).
  Defined.

  Theorem powerset_powers : 2^X ~ P X.
  Proof.
    exists (functionify powerset_bijection_helper).
    rewrite /bijective Injective_classification Surjective_classification
            @functionify_domain functionify_range.
    (repeat split; auto) => [x y H H0 | y /Powerset_classification H].
    - rewrite (reify H) (reify H0) ? @functionify_action
              /powerset_bijection_helper.
      (repeat destruct iffLR => /=) => H1.
      suff -> : (x = graph (mkFunc i0)); last by auto.
      suff -> : (y = graph (mkFunc i2)); last by auto.
      f_equal.
      apply func_ext; auto => z /= H2.
      have /= /Pairwise_union_classification: (mkFunc i0) z ∈ range (mkFunc i0);
        auto using function_maps_domain_to_range.
      have /= /Pairwise_union_classification: (mkFunc i2) z ∈ range (mkFunc i2);
        auto using function_maps_domain_to_range.
      (rewrite {3 10}/succ Union_comm Union_empty ? Singleton_classification) =>
      [[H3 | H3]] [H4 | H4]; try congruence.
      + have: z ∈ {x in X | (mkFunc i0) x = succ ∅} by
            apply Specify_classification, conj => //.
        rewrite H1 => /Specify_classification [] _ -> //.
      + have: z ∈ {x in X | (mkFunc i2) x = succ ∅} by
            apply Specify_classification, conj => //.
        rewrite -H1 => /Specify_classification [] _ -> //.
    - have H0: 1 ∈ 2 by apply /lt_is_in /succ_lt.
      have H1: 0 ∈ 2 by apply lt_is_in; eauto using lt_trans, succ_lt.
      exists {z in X × 2 | proj2 X 2 z = 1 ↔ proj1 X 2 z ∈ y}.
      have H2: {z in X × 2 | proj2 X 2 z = 1 ↔ proj1 X 2 z ∈ y} ∈ 2 ^ X.
      { rewrite Specify_classification Powerset_classification.
        (repeat split) => [z /Specify_classification [] |
                           z /Specify_classification [] | z] //.
        exists (If z ∈ y then 1 else 0).
        (elim excluded_middle_informative; repeat split => //) =>
        [ | x' [H3 /Specify_classification] | |
          x' [] /Pairwise_union_classification
             [/Pairwise_union_classification
               [/Empty_set_classification | /Singleton_classification] |
              /Singleton_classification ->] ]
          //; (rewrite Specify_classification proj1_eval // proj2_eval //
                       ? Product_classification; repeat split;
               try by intuition eauto) => /set_proj_injective /neq_succ //. }
      split; auto.
      rewrite (reify H2) functionify_action /powerset_bijection_helper.
      destruct iffLR as [_] => /=.
      apply Extensionality => z.
      split => [/Specify_classification /= [] H3
                 /function_maps_domain_to_graph /= /(_ H3) /(_ H0)
                 /Specify_classification | H3];
                 first by rewrite proj1_eval // proj2_eval //; tauto.
      apply Specify_classification, conj, function_maps_domain_to_graph,
      Specify_classification, conj; auto => /=.
      + eapply Product_classification, ex_intro, ex_intro, conj; eauto.
      + rewrite proj1_eval // ? proj2_eval; intuition.
  Qed.

End Powerset_powers.

Theorem powerset_finite : ∀ X, finite X → finite (P X).
Proof.
  move=> X.
  rewrite -powerset_powers.
  auto using finite_powers_are_finite, naturals_are_finite.
Qed.

Theorem powerset_card : ∀ X, finite X → # P X = (2^(# X))%N.
Proof.
  move=> X H.
  rewrite -powerset_powers ? finite_power_card ? card_of_natural;
    auto using naturals_are_finite.
Qed.

Theorem complement_card : ∀ E F, E ⊂ F → finite E → # (F \ E) = # F - # E.
Proof.
  move=> E F /[dup] H /Union_subset H0 H1.
  case (classic (finite F)) => [H2 | H2].
  - rewrite -{2}H0 disjoint_union_complement finite_union_cardinality
                1 ? naturals.add_comm ? sub_abba;
      eauto using subsets_of_finites_are_finite, complement_subset,
      disjoint_intersection_complement.
  - rewrite {1 2}/finite_cardinality /sumbool_rect.
    repeat elim excluded_middle_informative; try tauto; rewrite ? sub_0_l //
    => /[swap] /[dup] /finite_unions_are_finite /(_ H1).
    rewrite Union_comm -disjoint_union_complement H0 //.
Qed.

Theorem pairing_card : ∀ x y, x ≠ y → {x,y} ~ 2.
Proof.
  move=> x y /Pairing_intersection_disjoint H.
  now rewrite Pairing_union_singleton finite_union_equinumerosity
      ? singleton_card ? add_1_r; eauto using singletons_are_finite.
Qed.

Theorem injective_card :
  ∀ f, finite (range f) → injective f → # domain f ≤ # range f.
Proof.
  move=> ? ? /injective_into_image ->.
  auto using finite_subsets, image_subset_range.
Qed.
  
Theorem surjective_card :
  ∀ f, finite (domain f) → surjective f → # range f ≤ # domain f.
Proof.
  move=> f ? /right_inverse_iff_surjective [g [H [H0 H1]]].
  (have /injective_card: injective g; rewrite ? Injective_classification) =>
    [? ? ? ? /(f_equal f) | ]; rewrite ? H1 -? H ? H0; intuition.
Qed.
