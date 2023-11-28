Set Warnings "-ambiguous-paths".
Require Export ssreflect ssrbool ssrfun cardinality rationals.

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
    move=> z.
    case (excluded_middle_informative (z ~ x)) =>
    [/constructive_indefinite_description [g [H [H0 H1]]] | H].
    - exact g.
    - exact empty_function.
  Defined.

  Theorem oschf_domain : ∀ z, z ~ x → domain (oschf z) = z.
  Proof.
    rewrite /oschf => *.
    (case excluded_middle_informative; try tauto) => *.
    elim constructive_indefinite_description => ? [? [? ?]] //.
  Qed.

  Theorem oschf_range : ∀ z, z ~ x → range (oschf z) = x.
  Proof.
    rewrite /oschf => *.
    (case excluded_middle_informative; try tauto) => *.
    elim constructive_indefinite_description => ? [? [? ?]] //.
  Qed.

  Theorem oschf_bijective : ∀ z, z ~ x → bijective (oschf z).
  Proof.
    rewrite /oschf => *.
    (case excluded_middle_informative; try tauto) => *.
    elim constructive_indefinite_description => ? [? [? ?]] //.
  Qed.

  Theorem orbit_stabilizer_cardinality_helper : domain f ~ Y × x.
  Proof.
    elim (function_construction
            (domain f) (Y × x)
            (λ x, (f x, (oschf (inverse_image_of_element f (f x)) x))))
    => [g [H [H0 H1]] | a H].
    - exists g.
      rewrite /bijective Injective_classification Surjective_classification.
      (repeat split; auto) => [u v | y].
      + rewrite ? H => H2 H3.
        rewrite ? H1 /oschf // => /Ordered_pair_iff [/[dup] H4 ->].
        elim excluded_middle_informative =>
        [H5 | []]; last by auto using function_maps_domain_to_image.
        elim constructive_indefinite_description =>
        [h [H6 [H7 [/Injective_classification H8 H9]] /H8 ->]]
          //; rewrite H6 Inverse_image_classification //;
          auto using function_maps_domain_to_range.
      + rewrite H0 => /Product_classification [a [b [H2 [H3 ->]]]].
        move: (oschf_bijective (inverse_image_of_element f a) (Y_inv a H2))
        => [_ /Surjective_classification /(_ b)].
        (elim; rewrite ? oschf_range; auto) => [z].
        (rewrite oschf_domain; auto) =>
        [[]] /Specify_classification => [[H4 H5] H6].
        exists z.
        rewrite H1; intuition congruence.
    - rewrite /oschf.
      elim excluded_middle_informative =>
      [H1 | []]; auto using function_maps_domain_to_image.
      elim constructive_indefinite_description => [g [H2 [H3 H4]]].
      apply Product_classification.
      exists (f a), (g a).
      repeat split; auto using function_maps_domain_to_image.
      move: H2 H3 (function_maps_domain_to_range g a) -> => ->.
      rewrite /inverse_image_of_element Specify_classification; auto.
  Qed.

End orbit_stabilizer_cardinality_theorem.

Theorem orbit_stabilizer_cardinality : ∀ f x,
    (∀ y, y ∈ range f → inverse_image_of_element f y ~ x) →
    domain f ~ range f × x.
Proof.
  move=> f x H.
  auto using orbit_stabilizer_cardinality_helper, image_subset_range.
Qed.

Theorem orbit_stabilizer_cardinality_image : ∀ f x,
    (∀ y, y ∈ image f → inverse_image_of_element f y ~ x) →
    domain f ~ image f × x.
Proof.
  move=> f x H.
  auto using orbit_stabilizer_cardinality_helper, Set_is_subset.
Qed.

Section permutation_succ_helper_functions.

  Variable n : N.
  Variable y : elts (S n).

  Section functionify_construction.

    Variable A B : set.
    Definition functionify : elts (bijection_set A B) → function.
    Proof.
      move=> [f /Specify_classification
                [F /constructive_indefinite_description [f' F0]]].
      exact f'.
    Defined.

    Theorem functionify_domain : ∀ f, domain (functionify f) = A.
    Proof.
      rewrite /functionify => [[f F]].
      destruct iffLR.
      elim constructive_indefinite_description => ? [] //.
    Qed.

    Theorem functionify_range : ∀ f, range (functionify f) = B.
    Proof.
      rewrite /functionify => [[f F]].
      destruct iffLR.
      elim constructive_indefinite_description => ? [] ? [] //.
    Qed.

    Theorem functionify_graph : ∀ f, graph (functionify f) = f.
    Proof.
      rewrite /functionify => [[f F]].
      destruct iffLR.
      elim constructive_indefinite_description => ? [] ? [] _ [] -> //.
    Qed.

    Theorem functionify_bijective : ∀ f, bijective (functionify f).
    Proof.
      rewrite /functionify => [[f F]].
      destruct iffLR.
      elim constructive_indefinite_description => ? [] ? [] ? [] //.
    Qed.

  End functionify_construction.

  Definition permutation_succ_helper : set → set.
  Proof.
    move=> x.
    case (excluded_middle_informative (x ∈ (bijection_set (S n) (S n)))) =>
    [/Specify_classification [H /constructive_indefinite_description
                                [f [H0 [H1 [H2 H3]]]]] | H].
    - exact (f n).
    - exact ∅.
  Defined.

  Lemma permutation_succ_proj_construction : ∀ a,
      a ∈ bijection_set (S n) (S n) → permutation_succ_helper a ∈ S n.
  Proof.
    rewrite /permutation_succ_helper => a H.
    (case excluded_middle_informative; try tauto) => H0.
    destruct iffLR.
    elim constructive_indefinite_description => [x [H1 [H2 [H3 H4]]]].
    move: H2 H1 (function_maps_domain_to_range x n) -> => -> /(_ (in_S n)) //.
  Qed.

  Definition permutation_succ_proj : function.
  Proof.
    elim (constructive_indefinite_description
            (function_construction
               (bijection_set (S n) (S n)) (S n)
               permutation_succ_helper permutation_succ_proj_construction))
    => [f H].
    exact f.
  Defined.

  Theorem psp_domain : domain permutation_succ_proj = bijection_set (S n) (S n).
  Proof.
    rewrite /permutation_succ_proj /sig_rect.
    elim constructive_indefinite_description => ? [] //.
  Qed.

  Theorem psp_range : range permutation_succ_proj = S n.
  Proof.
    rewrite /permutation_succ_proj /sig_rect.
    elim constructive_indefinite_description => ? [] ? [] //.
  Qed.

  Definition n_in_Sn : elts (S n).
  Proof.
    move: (in_S n) => /mkSet //.
  Defined.

  Theorem psp_action :
    ∀ x :  elts (bijection_set (S n) (S n)),
      permutation_succ_proj x = ((functionify (S n) (S n) x) n).
  Proof.
    rewrite /permutation_succ_proj /sig_rect /permutation_succ_helper
            /functionify => x.
    elim constructive_indefinite_description =>
    [f [H [H0 ->]]]; try case excluded_middle_informative =>
    [H1 | []]; auto using elts_in_set.
    destruct iffLR, x, iffLR.
    elim constructive_indefinite_description => [f' [H2 [H3 [/= H4 H5]]]].
    elim constructive_indefinite_description => [f'' [H7 [H8 [H9 H10]]]].
    f_equal.
    apply function_record_injective; congruence.
  Qed.

  Definition inverse_image_incl :
    elts (inverse_image_of_element permutation_succ_proj y) →
    elts (bijection_set (S n) (S n)).
  Proof.
    rewrite /inverse_image_of_element => [[f /Specify_classification]].
    rewrite psp_domain => [[F F0]].
    exact (mkSet F).
  Defined.

  Lemma inverse_image_incl_value :
    ∀ f, (inverse_image_incl f : set) = (f : set).
  Proof.
    rewrite /inverse_image_incl /inverse_image_of_element
            /eq_rect_r /eq_rect => f.
    destruct f, eq_sym, iffLR => //.
  Qed.

  Lemma inverse_image_classification :
    ∀ f : elts (inverse_image_of_element permutation_succ_proj y),
      ((functionify (S n) (S n) (inverse_image_incl f)) n) = y.
  Proof.
    rewrite /functionify /inverse_image_incl /inverse_image_of_element
            /eq_rect_r /eq_rect =>
    [[f /[dup] /Specify_classification [H H0] F]].
    destruct eq_sym, iffLR, iffLR.
    elim constructive_indefinite_description => [g [H1 [H2 [H3 H4]]]].
    move: (reify H) psp_action H0 H3 -> => -> <- H0.
    f_equal.
    apply function_record_injective;
      rewrite ? functionify_range ? functionify_graph //.
  Qed.

  Theorem permutation_succ_left_helper_lemma :
    ∀ f (x : elts n), ((functionify (S n) (S n) (inverse_image_incl f))
                         x ∈ S n \ {y, y}).
  Proof.
    move=> f x.
    apply Complement_classification, conj.
    - rewrite -{3}(functionify_range (S n) (S n) (inverse_image_incl f)).
      apply function_maps_domain_to_range.
      rewrite functionify_domain.
      apply subset_S, elts_in_set.
    - move: (functionify_bijective _ _ (inverse_image_incl f)) =>
      [/Injective_classification H H0].
      rewrite Singleton_classification -(inverse_image_classification f) => /H.
      move: (no_quines n) => /[swap] {1}<-; auto using elts_in_set;
                               rewrite functionify_domain.
      + apply subset_S, elts_in_set.
      + auto using in_S.
  Qed.

  Definition permutation_succ_left_helper :
    elts (inverse_image_of_element permutation_succ_proj y) →
    elts n → elts (S n \ {y, y}).
  Proof.
    move=> f x.
    exact (mkSet (permutation_succ_left_helper_lemma f x)).
  Defined.

  Theorem pslh_action : ∀ f (x : elts n),
      (functionify _ _ (inverse_image_incl f)) x =
      (permutation_succ_left_helper f x).
  Proof.
    rewrite /permutation_succ_left_helper => f x //.
  Qed.

  Theorem psl_bijective :
    ∀ f, bijective (sets.functionify (permutation_succ_left_helper f)).
  Proof.
    move=> f.
    rewrite /bijective Injective_classification Surjective_classification
            /sets.functionify.
    (split; elim constructive_indefinite_description) =>
    [f' [H [H0 H1]] x1 x2 | f' [H [H0 H1]] z].
    - rewrite H => H2 H3.
      rewrite (reify H2) (reify H3) ? H1 -? pslh_action.
      move: (functionify_bijective _ _ (inverse_image_incl f)) =>
      [] /[swap] _ /Injective_classification /[apply] ->
      //; rewrite functionify_domain; apply subset_S, elts_in_set.
    - rewrite H0 => /Complement_classification [/[swap] H2].
      move: (functionify_bijective _ _ (inverse_image_incl f)) =>
      [_] /Surjective_classification.
      rewrite functionify_range functionify_domain H -{2}S_is_succ =>
      /[apply] [[x [/Pairwise_union_classification H3 H4]]].
      exists x.
      suff: x ∈ n => [H5 | ].
      + split; auto.
        rewrite (reify H5) H1 -pslh_action //.
      + move: H3 H4 H2 => [ | /Singleton_classification] // -> <-.
        rewrite inverse_image_classification Singleton_classification //.
  Qed.

  Theorem permutation_succ_left_construction : ∀ f,
      graph (sets.functionify (permutation_succ_left_helper f))
            ∈ bijection_set n (S n \ {y, y}).
  Proof.
    rewrite /bijection_set /sets.functionify => f.
    rewrite Specify_classification Powerset_classification.
    split => [z /Graph_classification | ].
    - elim constructive_indefinite_description => [f' [H [H0 H1]]] [x [H2 ->]].
      apply Product_classification.
      exists x, (f' x).
      move: H H0 <- => <-.
      auto using function_maps_domain_to_range.
    - exists (sets.functionify (permutation_succ_left_helper f)).
      move: (psl_bijective f).
      rewrite /sets.functionify.
      elim constructive_indefinite_description.
      tauto.
  Qed.

  Definition permutation_succ_left :
    elts (inverse_image_of_element permutation_succ_proj y) →
    elts (bijection_set n (S n \ {y, y})).
  Proof.
    move=> f.
    exact (mkSet (permutation_succ_left_construction f)).
  Defined.

  Lemma permutation_succ_right_helper_lemma :
    ∀ (f : elts (bijection_set n (S n \ {y, y}))) (x : elts (S n)),
      (x : set) ≠ n → ((functionify _ _ f) x ∈ S n \ {y, y}).
  Proof.
    move=> f x H.
    rewrite -{2}(functionify_range _ _ f).
    apply function_maps_domain_to_range.
    move: (elts_in_set x).
    rewrite functionify_domain -{2}S_is_succ =>
    /Pairwise_union_classification [ | ] // /Singleton_classification //.
  Qed.

  Definition permutation_succ_right_helper :
    elts (bijection_set n (S n \ {y, y})) → elts (S n) → elts (S n).
  Proof.
    move=> f x.
    case (excluded_middle_informative ((x : set) = n)) =>
    [H | /(permutation_succ_right_helper_lemma f)
          /Complement_classification [H H0]].
    - exact y.
    - exact (mkSet H).
  Defined.

  Theorem psrh_n : ∀ f, permutation_succ_right_helper f n_in_Sn = y.
  Proof.
    rewrite /permutation_succ_right_helper => f.
    case excluded_middle_informative; auto => [[]] //.
  Qed.

  Theorem psrh_bijective :
    ∀ f, bijective (sets.functionify (permutation_succ_right_helper f)).
  Proof.
    rewrite /sets.functionify => f.
    elim constructive_indefinite_description => [f' [H [H0 H1]]].
    rewrite /bijective Injective_classification Surjective_classification.
    (split; rewrite ? H ? H0) => [x1 x2 H2 H3 | z H2].
    - rewrite (reify H2) (reify H3) ? H1 /permutation_succ_right_helper.
      (repeat elim excluded_middle_informative; try congruence) =>
      /= H4 H5 H6; repeat destruct iffLR;
        try by contradict n0; rewrite Singleton_classification //.
      inversion H6 as [H7].
      move: (functionify_bijective _ _ f) H7 =>
      [/[swap] _ /Injective_classification] /[apply] ->
      //; [move: H2 | move: H3]; rewrite functionify_domain -S_is_succ =>
      /Pairwise_union_classification; rewrite ? Singleton_classification; tauto.
    - rewrite (reify H2).
      destruct (classic ((mkSet H2) = y)).
      + exists n.
        split; auto using in_S.
        rewrite (reify (in_S n)) H1 psrh_n H3 //.
      + move: (functionify_bijective _ _ f) => [_ /Surjective_classification].
        rewrite functionify_range functionify_domain => /(_ z).
        elim => [x [H4 H5] | ].
        * exists x.
          split; first by apply subset_S.
          rewrite (reify (subset_S _ _ H4)) H1 /permutation_succ_right_helper.
          elim excluded_middle_informative => [ | H6]; last by destruct iffLR.
          move: (no_quines n) => /[swap] {1}<- //.
        * rewrite Complement_classification Singleton_classification.
          split; auto.
          contradict H3.
            by apply set_proj_injective.
  Qed.

  Lemma permutation_succ_right_construction : ∀ f,
      graph (sets.functionify (permutation_succ_right_helper f)) ∈
            (inverse_image_of_element permutation_succ_proj y).
  Proof.
    rewrite /inverse_image_of_element => f.
    apply Specify_classification.
    have H: graph (sets.functionify (permutation_succ_right_helper f))
                  ∈ bijection_set (S n) (S n).
    { rewrite Specify_classification Powerset_classification /sets.functionify.
      split => [z /Graph_classification [z' [/[swap] ->]] | ].
      - elim constructive_indefinite_description => [f' [H0 [H1 H2]] H3].
        rewrite Product_classification -{1}H0 -H1.
        exists z', (f' z').
        auto using function_maps_domain_to_range.
      - exists (sets.functionify (permutation_succ_right_helper f)).
        move: (psrh_bijective f).
        rewrite /sets.functionify.
        elim constructive_indefinite_description.
        tauto. }
    split.
    - rewrite /permutation_succ_proj /sig_rect.
      elim constructive_indefinite_description => [f' [-> [H1 H2]]] //.
    - rewrite (reify H) psp_action /functionify.
      destruct iffLR.
      elim constructive_indefinite_description =>
      [f' [H0 [H1 [/function_record_injective]]]] {i e}.
      rewrite sets.functionify_range -(psrh_n f) -(functionify_action) => <- //.
  Qed.

  Definition permutation_succ_right :
    elts (bijection_set n (S n \ {y, y})) →
    elts (inverse_image_of_element permutation_succ_proj y).
  Proof.
    move=> f.
    exact (mkSet (permutation_succ_right_construction f)).
  Defined.

End permutation_succ_helper_functions.

Theorem permutation_succ :
  ∀ n : N, bijection_set (S n) (S n) ~ (S n) × (bijection_set n n).
Proof.
  move=> n.
  rewrite -psp_domain -psp_range.
  apply orbit_stabilizer_cardinality => y.
  rewrite psp_range => H.
  (have: (n : set) = S n \ {n,n} by
      rewrite -S_is_succ /succ complement_disjoint_union;
   auto using disjoint_succ) => /[dup] Sn {2}->.
  have -> : S n \ {n,n} ~ S n \ {y,y} by
      apply equivalence_minus_element; auto using in_S, cardinality_refl.
  apply two_sided_inverse_bijective.
  rewrite (reify H).
  exists (permutation_succ_left _ (mkSet H)),
  (permutation_succ_right _ (mkSet H)).
  split => [a | b].
  - move: (elts_in_set a) => /= /[dup] H0 /[dup] /Inverse_image_classification
                                /[swap] /Inverse_image_subset.
    rewrite psp_domain psp_range =>
    /(_ H) /[dup] H1 /[swap] /(_ H1 H) H2 /Specify_classification
     [H3 [f [H4 [H5 [H6 H7]]]]].
    apply set_proj_injective, (function_graph_equality (S n) (S n)) =>
    /= [ | | z /Graph_classification [z' [/[swap] ->]]].
    { move: (func_hyp (sets.functionify
                         (permutation_succ_right_helper
                            _ _ (permutation_succ_left _ _ a)))).
      rewrite @sets.functionify_domain @sets.functionify_range //. }
    { rewrite -{1}H4 -H5 -H6.
      apply func_hyp. }
    rewrite @sets.functionify_domain => H8.
    rewrite (reify H8) functionify_action /permutation_succ_right_helper.
    elim excluded_middle_informative => /= [-> | H9].
    * rewrite -H6.
      apply Graph_classification.
      exists n.
      rewrite H4 Ordered_pair_iff /= -H2 (reify H1) psp_action.
      repeat split; auto using in_S.
      f_equal.
      apply function_record_injective;
        rewrite ? functionify_range ? functionify_graph //.
    * (repeat destruct iffLR => /=) => {i n0 i0}.
      elim constructive_indefinite_description => {e} f' [H10 [H11 [H12 H13]]].
      have: (z', f' z') ∈ graph f'.
      { apply Graph_classification.
        exists z'.
        rewrite H10 Sn Complement_classification Singleton_classification //. }
      rewrite H12 => /Graph_classification =>
      [[z'' [/[swap] /Ordered_pair_iff [<-]]]].
      rewrite sets.functionify_domain => /[swap] H14.
      rewrite (reify H14) functionify_action => -> /=.
      move: H2.
      rewrite -(inverse_image_incl_value n (mkSet H) a) psp_action /functionify.
      elim inverse_image_incl => [w W].
      destruct iffLR.
      elim constructive_indefinite_description => [f'' [H15 [H16 [H17 H18]]]].
      rewrite /= -H17 => H19.
      apply function_maps_domain_to_graph =>
      //; try apply function_maps_domain_to_range; rewrite H15 //.
  - move: (elts_in_set b) =>
    /= /Specify_classification [H0 [g [H1 [H2 [H3 H4]]]]].
    (apply set_proj_injective, (function_graph_equality n (S n \ {y,y})); auto)
    => /= [ | | z].
    { move: (func_hyp (sets.functionify
                         (permutation_succ_left_helper
                            _ _ (permutation_succ_right n (mkSet H) b)))).
      rewrite @sets.functionify_domain @sets.functionify_range //. }
    { rewrite -{2}H1 -{2}H2 -H3.
      apply func_hyp. }
    rewrite /sets.functionify.
    elim constructive_indefinite_description =>
    [f [H5 [H6 H7]]] /Graph_classification [z' [/[swap] ->]].
    rewrite H5 => H8.
    rewrite (reify H8) H7 -H3.
    apply Graph_classification.
    exists (mkSet H8).
    split => [/= | ]; try congruence.
    rewrite <-(pslh_action n (mkSet H)).
    apply Ordered_pair_iff.
    split; auto => {f H5 H6 H7}.
    rewrite /functionify /inverse_image_incl /permutation_succ_right
            /eq_rect_r /eq_rect.
    destruct iffLR, eq_sym, iffLR.
    elim constructive_indefinite_description =>
    x [H5 [H6 [/[swap] H7]]] /function_record_injective.
    rewrite ? sets.functionify_range /sets.functionify => /(_ H6) ->.
    elim constructive_indefinite_description => [f [H9 [H10 H11]]] /=.
    rewrite (reify (subset_S n _ H8)) H11 /permutation_succ_right_helper.
    case excluded_middle_informative =>
    /= [H12 | H12]; first by move: H12 no_quines H8 -> => /[apply] //.
    destruct iffLR => /=.
    f_equal.
    apply function_record_injective;
      rewrite ? functionify_domain ? functionify_range ? functionify_graph //.
Qed.

Theorem bijection_empty_is_singleton : bijection_set 0%N 0%N = {∅, ∅}.
Proof.
  apply Extensionality => z.
  rewrite Singleton_classification.
  split => [/Specify_classification [/Powerset_classification] | ->].
  - rewrite Empty_product_left =>
    /Subset_equality /(_ (Empty_set_is_subset z)) //.
  - rewrite Specify_classification Powerset_classification Empty_product_left.
    split; auto using Set_is_subset.
    exists empty_function.
    rewrite /empty_function ? /ssr_have /naturals.zero /=.
    elim constructive_indefinite_description => f [H [H0 H1]].
    rewrite function_empty_domain /bijective Injective_classification
            Surjective_classification H H0.
    (repeat split; auto) =>
    [x y /Empty_set_classification | x /Empty_set_classification] //.
Qed.

Theorem bijections_of_empty_set : bijection_set 0%N 0%N ~ 1%N.
Proof.
  rewrite bijection_empty_is_singleton.
  apply singleton_card_1.
Qed.

Theorem bijections_of_one : bijection_set 1%N 1%N ~ 1%N.
Proof.
  now rewrite /naturals.one permutation_succ bijections_of_empty_set
  -S_is_succ /succ Union_comm Union_empty singleton_products ? singleton_card_1.
Qed.

Theorem permutations_are_finite : ∀ n : N, finite (bijection_set n n).
Proof.
  induction n as [| n [m H]] using Induction.
  - exists 1%N.
    apply bijections_of_empty_set.
  - exists ((S n) * m)%N.
    now rewrite permutation_succ H (card_equiv (S n × m))
        ? natural_prod_card ? card_of_natural;
      auto using finite_products_are_finite, naturals_are_finite.
Qed.

Theorem size_of_bijections_of_empty_set : size_of_bijections 0%N 0%N = 1%N.
Proof.
  apply natural_cardinality_uniqueness.
  rewrite -bijections_of_empty_set.
  eauto using cardinality_sym, card_equiv, permutations_are_finite.
Qed.

Theorem size_of_bijections_of_one : size_of_bijections 1%N 1%N = 1%N.
Proof.
  rewrite /size_of_bijections bijections_of_one card_of_natural //.
Qed.

Theorem number_of_permutations_n : ∀ n, n! = permutations n.
Proof.
  elim/Induction => [ | n].
  - rewrite /factorial /permutations prod_N_neg
            ? size_of_bijections_of_empty_set //; apply naturals.lt_succ.
  - (rewrite /factorial /permutations ? prod_N_succ ? IHn /size_of_bijections
             ? permutation_succ ? product_card ? card_of_natural 1
             ? mul_comm; auto using one_le_succ, permutations_are_finite,
                         naturals_are_finite) => <- //.
Qed.

Theorem number_of_permutations :
  ∀ S (n : N), S ~ n → n! = size_of_bijections S S.
Proof.
  move: number_of_permutations_n => /[swap] S /[swap] n -> -> //.
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
  move=> n k H.
  symmetry.
  elim (function_construction
          (set_of_combinations (n+1) k)
          (set_of_combinations n k ∪ set_of_combinations n (k-1))
          (λ x, If n ∈ x then x \ {n,n} else x)) =>
  [f [H0 [H1 H2]] | a /Specify_classification [/Powerset_classification H0 H1]].
  - exists f.
    rewrite /bijective Injective_classification Surjective_classification.
    (repeat split; auto) => [x y H3 H4 | y].
    + rewrite ? H2 -? H0 //.
      (repeat elim excluded_middle_informative => //) => H5 H6 H7.
      * apply Extensionality => z.
        destruct (classic (z = n)) as [-> | H8]; split =>
        H9 //; eapply complement_subset; [rewrite <-H7 | rewrite -> H7];
          rewrite Complement_classification Singleton_classification //.
      * move: H7 H3 H4 <-.
        (rewrite H0 /set_of_combinations ? Specify_classification
                 complement_card ? singleton_card ? sub_1_r;
         auto using singletons_are_finite) =>
        [z /Singleton_classification -> |
         [/Powerset_classification /subsets_of_finites_are_finite H7 <-]
           [_ /pred_fixpoint /finite_empty H8]] //.
        (move: H8 H6 ->; auto using naturals_are_finite) =>
        /Empty_set_classification //.
      * move: H7 H3 H4 ->.
        (rewrite H0 /set_of_combinations ? Specify_classification
                 complement_card ? singleton_card ? sub_1_r;
          auto using singletons_are_finite) =>
        [z /Singleton_classification -> |
         [] _ <- [/Powerset_classification /subsets_of_finites_are_finite H7]
                   /(@eq_sym N) /pred_fixpoint /finite_empty H8] //.
        (move: H8 H5 ->; auto using naturals_are_finite) =>
        /Empty_set_classification //.
    + rewrite H1 => /Pairwise_union_classification
                     [/Specify_classification [/Powerset_classification H3 H4] |
                      /Specify_classification [/Powerset_classification H3 H4]].
      * exists y.
        have: y ∈ domain f.
        { rewrite H0 /set_of_combinations Specify_classification
                  Powerset_classification add_1_r.
          split; auto => z /H3 /subset_S H5 //. }
        split; auto.
        rewrite H2 -? H0 //.
        (case excluded_middle_informative; auto) => /H3 /no_quines //.
      * exists (y ∪ {n,n}).
        have H5: y ∩ {n,n} = ∅.
        { (apply Subset_equality_iff, conj; auto using Empty_set_is_subset)
          => z /Pairwise_intersection_classification [] /H3 /[swap]
               /Singleton_classification -> /no_quines //. }
        have H6: (y ∪ {n,n} ∈ domain f).
        { rewrite H0 /set_of_combinations Specify_classification
                  Powerset_classification add_1_r.
          split => [z /Pairwise_union_classification
                      [/H3 /subset_S | /Singleton_classification ->] | ];
                     auto using in_S.
          rewrite finite_union_cardinality ? singleton_card ? H4 1 ? add_comm
                  ? sub_abab;
            eauto using one_le_succ, singletons_are_finite,
            subsets_of_finites_are_finite, naturals_are_finite. }
        split; auto.
        rewrite H2 -? H0 //.
        case excluded_middle_informative;
          rewrite ? complement_disjoint_union ? Pairwise_union_classification
                  ? Singleton_classification; tauto.
  - case excluded_middle_informative; move: H0;
      rewrite add_1_r -S_is_succ Pairwise_union_classification
                                 /set_of_combinations ? Specify_classification
                                 ? Powerset_classification => H0 H2.
    + apply or_intror, conj =>
      [x /Complement_classification [/H0 /Pairwise_union_classification [? | ?]
                                      /Singleton_classification ?] | ] //.
      (rewrite complement_card ? singleton_card ? H1
               //; auto using singletons_are_finite) =>
      z /Singleton_classification -> //.
    + apply or_introl, conj =>
      [z /[dup] /H0 /Pairwise_union_classification
         [H3 | /Singleton_classification ->] H4 | ] //.
Qed.

Theorem Pascal's_identity :
  ∀ n k, (1 ≤ k → binomial n k + binomial n (k-1) = binomial (n+1) k)%N.
Proof.
  rewrite /binomial => n k H.
  rewrite -Pascal's_identity_bijection ? finite_union_cardinality;
    auto using binomials_are_finite.
  apply Extensionality => z.
  split => [/Pairwise_intersection_classification
             [/Specify_classification [H0 H1] /Specify_classification [H2 H3]]
           | /Empty_set_classification] //.
  move: H H1 H3 => /naturals.lt_0_le_1 /nonzero_lt /succ_0 [m ->] ->.
  rewrite sub_succ sub_0_r => /(@eq_sym N) /neq_succ //.
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
  move=> n k H.
  apply Extensionality => z.
  split => [/Specify_classification [/Powerset_classification /finite_subsets]
           | /Empty_set_classification H0] // =>
  /(_ (naturals_are_finite n)) /[swap] -> /naturals.le_not_gt.
  rewrite card_of_natural //.
Qed.

Theorem binomial_overflow : ∀ n k, (n < k)%N → binomial n k = 0%N.
Proof.
  rewrite /binomial => n k H.
  rewrite combinations_overflow ? card_empty //.
Qed.

Theorem binomial_empty_set : ∀ k, k ≠ 0%N → binomial 0 k = 0%N.
Proof.
  move=> k /succ_0 [m ->].
  apply binomial_overflow, naturals.lt_succ.
Qed.

Theorem zero_factorial : 0! = 1%N.
Proof.
  rewrite /factorial prod_N_neg; auto; apply naturals.succ_lt.
Qed.

Lemma factorial_ne_0 : ∀ k, k! ≠ 0%N.
Proof.
  induction k using Induction.
  - rewrite zero_factorial.
    eauto using neq_sym, PA4.
  - (rewrite /factorial prod_N_succ; auto using one_le_succ) =>
    /naturals.cancellation_0_mul => [[ | /(@eq_sym N) /PA4]] //.
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
  rewrite inv_div //= -M2 ? IZQ_mul ? INZ_mul inv_l
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
  induction n using Induction => X f H H0 H1.
  - rewrite sum_0.
    repeat f_equal.
    apply Extensionality => z.
    rewrite H1.
    split => [H2 | [y [[[/naturals.le_antisymm /[apply] ->]]]]] //.
    exists 0%N.
    (repeat split; eauto using naturals.le_refl) =>
    x' [[/naturals.le_antisymm /[apply]]] //.
  - (rewrite sum_succ ? (IHn (X \ (f (S n))) f) /=;
             eauto using zero_le, subsets_of_finites_are_finite,
     complement_subset, subsets_of_finites_are_finite) =>
    [k [H2 H3] x /[dup] H4 /H0 H5 | | ].
    + (have: x ∈ X by eauto using naturals.le_trans, naturals.le_succ) =>
      /[dup] H6 /H1 [y [[[H7 H8] H9] H10]].
      apply Complement_classification, conj => [ | H11] //.
      have: y = S n by eauto using zero_le, naturals.le_refl.
      have -> : y = k by eauto using naturals.le_trans, naturals.le_succ.
      move: H3 => /[swap] -> /not_succ_le //.
    + split => [/Complement_classification
                 [/H1 [y [[[H2 /squeeze_upper H3] H4] H5]] H6]
               | [y [[[H2 H3] /[dup] H4 /H0 H5] H6]]].
      * exists y.
        (repeat split; auto) =>
        [| ? [[]]]; eauto using naturals.le_trans, naturals.le_succ.
        apply NNPP => /naturals.lt_not_ge /H3.
        move: H4 => /[swap] -> //.
      * apply Complement_classification.
        (have: x ∈ X by eauto using naturals.le_trans, naturals.le_succ) =>
        /[dup] H7 /H1 [z [[[H8 H9] H10] H11]].
        split; auto => H12.
        have: z = S n by auto using zero_le, naturals.le_refl.
        have -> : z = y by eauto using naturals.le_trans, naturals.le_succ.
        move: H3 => /[swap] -> /not_succ_le //.
    + rewrite INZ_add -finite_union_cardinality;
        eauto using subsets_of_finites_are_finite, complement_subset,
        subsets_of_finites_are_finite, zero_le, naturals.le_refl.
      * apply NNPP =>
        /Nonempty_classification [x /Pairwise_intersection_classification
                                    [/Complement_classification []]] //.
      * rewrite Union_comm -disjoint_union_complement.
        apply f_equal, f_equal, Union_subset, H0.
        eauto using zero_le, naturals.le_refl.
Qed.

Theorem sum_card : ∀ a b X f,
    finite X → (∀ k, a ≤ k ≤ b → f k ⊂ X)%N →
    (∀ x, x ∈ X ↔ exists ! k : N, a ≤ k ≤ b ∧ x ∈ f k)%N →
    sum ℤ (λ k, # (f k) : Z) a b = (# X : Z).
Proof.
  move=> a b X f H.
  case (classic (a ≤ b)%N) => [[c <-] H0 H1 |
                               /[dup] H0 /naturals.lt_not_ge H1 H2 H3].
  - rewrite /sum iterate_shift.
    (apply sum_card_0; auto) =>
    [k [H2 H3] | x]; first by apply H0, conj;
      rewrite ? (add_comm a); auto using le_add_l, O1_le.
    split => [/H1 [y [[[H2 H3] H4] H5]] | [y [[[H2 H3] H4] H5]]].
    + exists (y-a)%N.
      (repeat split; try apply zero_le) => [ | | x' [[H6 H7] H8]].
      * apply (O1_le_iff a).
        rewrite (add_comm c) (add_comm (y-a)) sub_abab //.
      * rewrite add_comm sub_abab; auto using naturals.le_refl.
      * move: (H5 (x'+a))%N ->; rewrite ? sub_abba ? (add_comm a c) //.
        eauto using le_add_l, O1_le.
    + apply (H0 (y+a)%N); auto.
      rewrite (add_comm a c).
      eauto using le_add_l, O1_le.
  - rewrite sum_neg //.
    apply INZ_eq, eq_sym.
    suff -> : X = ∅; auto using card_empty.
    (apply Subset_equality_iff, conj; auto using Empty_set_is_subset) =>
    z /H3 [y [[[H4 H5] H6] H7]].
    contradict H2.
    eauto using naturals.le_trans.
Qed.
