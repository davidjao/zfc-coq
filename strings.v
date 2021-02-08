Require Export polynomials.

Theorem STR_construction :
  ∃ S : set, ∀ f, f ∈ S ↔ ∃ n : N, is_function f n {0,1}%N.
Proof.
  destruct (Replacement ω (λ n X, X = {0%N,1%N}^n)) as [S].
  - intros x H.
    exists ({0%N,1%N}^x).
    split; auto.
  - exists (⋃ S).
    split; intros H0.
    + apply Union_classification in H0 as [x [H0 H1]].
      apply H in H0 as [n [H0 H2]].
      subst.
      apply Specify_classification in H1 as [H1 H2].
      now (exists (exist _ _ H0 : N)).
    + destruct H0 as [n H0].
      apply Union_classification.
      exists ({0%N,1%N}^n).
      split.
      * apply H.
        exists n.
        split; auto.
        apply (proj2_sig n).
      * apply Specify_classification.
        split; auto.
        destruct H0 as [H0 H1].
        now apply Powerset_classification.
Qed.

Definition STR : set.
Proof.
  destruct (constructive_indefinite_description _ STR_construction) as [STR].
  exact STR.
Defined.

Theorem STR_classification : ∀ f, f ∈ STR ↔ ∃ n : N, is_function f n {0%N,1%N}.
Proof.
  intros f.
  unfold STR.
  now destruct constructive_indefinite_description.
Qed.

Theorem zero_string_construction : is_function {(0,0),(0,0)}%N 1%N {0%N,1%N}.
Proof.
  split.
  - intros z H.
    apply Singleton_classification in H.
    subst.
    apply Product_classification.
    exists 0%N, 0%N.
    rewrite <-lt_is_in.
    repeat split; auto using zero_le, (PA4 0).
    apply Pairing_classification; intuition.
  - intros a H.
    exists 0%N.
    unfold naturals.one in H.
    rewrite <-S_is_succ in H.
    apply Pairwise_union_classification in H as [H | H];
      try now contradiction (Empty_set_classification a).
    apply Singleton_classification in H.
    subst.
    repeat split.
    + apply Pairing_classification; intuition.
    + now apply Singleton_classification.
    + intros x' [H H0].
      apply Singleton_classification, Ordered_pair_iff in H0 as [H0 H1].
      now subst.
Qed.

Theorem one_string_construction : is_function {(0,1),(0,1)}%N 1%N {0%N,1%N}.
Proof.
  split.
  - intros z H.
    apply Singleton_classification in H.
    subst.
    apply Product_classification.
    exists 0%N, 1%N.
    rewrite <-lt_is_in.
    repeat split; auto using zero_le, (PA4 0).
    apply Pairing_classification; intuition.
  - intros a H.
    exists 1%N.
    unfold naturals.one in H.
    rewrite <-S_is_succ in H.
    apply Pairwise_union_classification in H as [H | H];
      try now contradiction (Empty_set_classification a).
    apply Singleton_classification in H.
    subst.
    repeat split.
    + apply Pairing_classification; intuition.
    + now apply Singleton_classification.
    + intros x' [H H0].
      apply Singleton_classification, Ordered_pair_iff in H0 as [H0 H1].
      now subst.
Qed.

Delimit Scope String_scope with str.
Open Scope String_scope.

Definition σ := elts STR.
Definition setify : σ → set := λ a, proj1_sig a.
Coercion setify : σ >-> set.
Definition Σ := elts (P STR).
Definition subsetify : Σ → set := λ a, proj1_sig a.
Coercion subsetify : Σ >-> set.

Bind Scope String_scope with STR.
Bind Scope String_scope with σ.

Definition functionify : σ → function.
Proof.
  intros z.
  pose proof (proj2_sig z) as H; simpl in H.
  rewrite STR_classification in H.
  destruct (constructive_indefinite_description _ H) as [n H0].
  exact (mkFunc _ _ _ H0).
Defined.

Coercion functionify : σ >-> function.

Theorem string_range : ∀ x : σ, range x = {0%N,1%N}.
Proof.
  intros x.
  unfold functionify.
  now destruct constructive_indefinite_description.
Qed.

Definition zero_string : σ.
Proof.
  assert ({(0,0),(0,0)}%N ∈ STR) as H.
  { apply STR_classification.
    exists 1%N.
    apply zero_string_construction. }
  exact (exist _ _ H).
Defined.

Notation "0" := zero_string : String_scope.
Definition one_string : σ.
Proof.
  assert ({(0,1),(0,1)}%N ∈ STR) as H.
  { apply STR_classification.
    exists 1%N.
    apply one_string_construction. }
  exact (exist _ _ H).
Defined.
Notation "1" := one_string : String_scope.

Definition length : σ → N.
Proof.
  intros z.
  pose proof (proj2_sig z) as H; simpl in H.
  apply STR_classification in H.
  destruct (constructive_indefinite_description _ H) as [n H0].
  exact n.
Defined.

Theorem length_is_domain : ∀ x : σ, domain x = length x.
Proof.
  intros x.
  unfold length, functionify.
  repeat destruct constructive_indefinite_description.
  simpl.
  eauto using domain_uniqueness.
Qed.

Theorem string_domain : ∀ (x : σ) z, z ∈ domain x → z ∈ ω.
Proof.
  intros x z H.
  eapply elements_of_naturals_are_naturals; eauto.
  rewrite length_is_domain.
  apply (proj2_sig (length x)).
Qed.

Theorem length_zero : length 0 = 1%N.
Proof.
  unfold length, zero_string.
  repeat destruct constructive_indefinite_description.
  simpl in *.
  eauto using set_proj_injective, domain_uniqueness, zero_string_construction.
Qed.

Theorem length_one : length 1 = 1%N.
Proof.
  unfold length, zero_string.
  repeat destruct constructive_indefinite_description.
  simpl in *.
  eauto using set_proj_injective, domain_uniqueness, one_string_construction.
Qed.

Definition cc_singleton : σ → Σ.
Proof.
  intros [x H].
  assert ({x,x} ∈ P STR).
  { apply Powerset_classification.
    intros z H0.
    apply Singleton_classification in H0.
    congruence. }
  exact (exist _ _ H0).
Defined.

Section concat_elements_construction.

  Variable n m : N.
  Variable f g : set.
  Hypothesis F : is_function f n {0%N,1%N}.
  Hypothesis G : is_function g m {0%N,1%N}.

  Definition concat_elements : elts (n+m)%N → elts {0%N,1%N}.
  Proof.
    intros x.
    set (f' := mkFunc _ _ _ F).
    set (g' := mkFunc _ _ _ G).
    assert (proj1_sig x ∈ ω).
    { pose proof (proj2_sig x) as H.
      apply elements_of_naturals_are_naturals in H; auto.
      apply (proj2_sig (n+m)%N). }
    set (ξ := (exist _ _ H : N)).
    destruct (excluded_middle_informative (ξ < n)%N).
    - apply lt_is_in in l.
      assert (f' ξ ∈ {0%N,1%N}).
      { replace {0%N,1%N} with (range f'); try now simpl.
        now apply function_maps_domain_to_range. }
      exact (exist _ _ H0).
    - assert ((ξ - n)%N ∈ m).
      { apply naturals.le_not_gt, sub_abab in n0.
        pose proof (proj2_sig x) as H0; simpl in H0.
        assert (ξ ∈ n+m)%N as H1 by auto.
        rewrite <-lt_is_in, naturals.lt_not_ge in *.
        contradict H1.
        destruct (constructive_indefinite_description _ H1) as [c H2].
        exists c.
        rewrite <-n0, <-H2.
        ring. }
      assert (g' (ξ - n)%N ∈ {0%N,1%N}).
      { replace {0%N,1%N} with (range g'); try now simpl.
        now apply function_maps_domain_to_range. }
      exact (exist _ _ H1).
  Defined.

End concat_elements_construction.

Definition concat : σ → σ → σ.
Proof.
  intros [a A] [b B].
  rewrite STR_classification in *.
  destruct (constructive_indefinite_description _ A) as [n H].
  destruct (constructive_indefinite_description _ B) as [m H0].
  set (f := sets.functionify _ _ (concat_elements n m a b H H0)).
  assert (graph f ∈ STR).
  { apply STR_classification.
    exists (n+m)%N.
    pose proof (func_hyp f) as H1.
    unfold f in H1 at 2 3.
    now rewrite sets.functionify_domain, sets.functionify_range in H1. }
  exact (exist _ _ H1).
Defined.

Infix "++" := concat : String_scope.

Theorem concat_length : ∀ a b, length (a ++ b) = (length a + length b)%N.
Proof.
  intros [a A] [b B].
  unfold concat, length.
  repeat destruct constructive_indefinite_description.
  simpl in *.
  replace x2 with x0 by eauto using set_proj_injective, domain_uniqueness.
  replace x3 with x1 by eauto using set_proj_injective, domain_uniqueness.
  eapply set_proj_injective, domain_uniqueness; eauto.
  pose proof (func_hyp (sets.functionify
                          _ _ (concat_elements x0 x1 a b i0 i1))) as H.
  now rewrite sets.functionify_domain, sets.functionify_range in H.
Qed.

Definition empty_string : σ.
Proof.
  assert (∅ ∈ STR).
  { apply STR_classification.
    exists 0%N.
    split; auto using Empty_set_is_subset.
    intros a H.
    contradiction (Empty_set_classification a). }
  exact (exist _ _ H).
Defined.

Notation "'ε'" := empty_string (at level 0) : String_scope.

Reserved Notation "s =~ re" (at level 80).

Theorem length_empty : length ε = 0%N.
Proof.
  unfold empty_string, length.
  destruct constructive_indefinite_description.
  simpl in *.
  eapply set_proj_injective, domain_uniqueness; eauto.
  split; auto using Empty_set_is_subset.
  intros a H.
  contradiction (Empty_set_classification a).
Qed.

Inductive reg_exp : Type :=
| EmptySet
| Char (t : σ)
| Concat (r1 r2 : reg_exp)
| Or (r1 r2 : reg_exp)
| Star (r : reg_exp).

Notation "[ x ]" := (Char x) : String_scope.
Infix "⌣" := Or (at level 60) : String_scope.
Infix "||" := Concat : String_scope.
Notation "A '⃰' " := (Star A) (at level 30, format "A '⃰'") : String_scope.

Inductive exp_match : σ → reg_exp → Prop :=
| MChar x : x =~ [x]
| MUnionL a A B (H1 : a =~ A) : a =~ A ⌣ B
| MUnionR b A B (H2 : b =~ B) : b =~ A ⌣ B
| MApp a b A B (H1 : a =~ A) (H2 : b =~ B) : a ++ b =~ A || B
| MStar0 A : ε =~ A ⃰
| MStarApp u v A (H1 : u =~ A) (H2 : v =~ A ⃰) : u ++ v =~ A ⃰
                                where "s =~ re" := (exp_match s re).

Definition realization A := {x in STR | ∃ y : σ, x = y ∧ exp_match y A}.
Coercion realization : reg_exp >-> set.

Theorem realization_in_powerset : ∀ A, realization A ∈ P STR.
Proof.
  intros A.
  rewrite Powerset_classification.
  intros z H.
  now apply Specify_classification in H as [H H0].
Qed.

Theorem realization_is_subset : ∀ A, realization A ⊂ STR.
Proof.
  intros A.
  apply Powerset_classification, realization_in_powerset.
Qed.

Definition subset_of (A : reg_exp) := exist _ _ (realization_in_powerset A) : Σ.

Coercion subset_of : reg_exp >-> Σ.

Definition concat_set (A : Σ) (B : Σ) : Σ.
Proof.
  set (X := {z in STR | ∃ a b : σ, a ∈ A ∧ b ∈ B ∧ z = a ++ b}).
  assert (X ∈ P STR).
  { apply Powerset_classification.
    intros x H.
    now apply Specify_classification in H as [H H0]. }
  exact (exist _ _ H).
Defined.

Theorem concat_reg_exp : ∀ A B : reg_exp, concat_set A B = A || B.
Proof.
  intros A B.
  apply set_proj_injective.
  simpl.
  apply Extensionality.
  split; intros H.
  - apply Specify_classification in H as [H [a [b [H0 [H1 H2]]]]].
    subst.
    apply Specify_classification.
    split; auto.
    exists (a ++ b).
    split; auto.
    apply MApp.
    + apply Specify_classification in H0 as [H0 [y [H2 H3]]].
      apply set_proj_injective in H2.
      congruence.
    + apply Specify_classification in H1 as [H1 [y [H2 H3]]].
      apply set_proj_injective in H2.
      congruence.
  - apply Specify_classification in H as [H [y [H0 H1]]].
    apply Specify_classification.
    split; auto.
    inversion H1.
    exists a, b.
    repeat split; try congruence.
    + apply Specify_classification.
      split; try apply (proj2_sig a).
      exists a.
      split; auto.
    + apply Specify_classification.
      split; try apply (proj2_sig b).
      exists b.
      split; auto.
Qed.

Theorem empty_set_realization : realization EmptySet = ∅.
Proof.
  apply Extensionality.
  split; intros H.
  - apply Specify_classification in H as [H [y [H0 H1]]].
    inversion H1.
  - contradiction (Empty_set_classification z).
Qed.

Theorem singleton_realization : ∀ a, realization [a] = {a,a}.
Proof.
  intros a.
  apply Extensionality.
  split; intros H.
  - apply Specify_classification in H as [H [y [H0 H1]]].
    inversion H1.
    subst.
    now apply Singleton_classification.
  - apply Singleton_classification in H.
    subst.
    apply Specify_classification.
    split.
    + apply (proj2_sig a).
    + exists a.
      split; auto.
      apply MChar.
Qed.

Theorem reg_exps_are_strings : ∀ A : reg_exp, A ⊂ STR.
Proof.
  intros A z H.
  now apply Specify_classification in H as [H H0].
Qed.

Theorem empty_subset_construction : [ε] ∈ P STR.
Proof.
  rewrite Powerset_classification.
  intros z H.
  rewrite singleton_realization, Singleton_classification in H.
  subst.
  apply (proj2_sig ε).
Qed.

Definition empty_subset := [ε] : Σ.

Definition pow (A : Σ) (n : N) :=
  iterate_with_bounds (P STR) concat_set (λ x, A) empty_subset 1 n : Σ.
Infix "^" := pow : String_scope.

Theorem pow_0_r : ∀ A, A^0 = [ε].
Proof.
  intros A.
  unfold pow, iterate_with_bounds.
  destruct excluded_middle_informative; auto.
  - exfalso.
    apply naturals.le_not_gt in l.
    eauto using naturals.succ_lt.
Qed.

Theorem pow_1_r : ∀ A, A^1 = A.
Proof.
  intros A.
  unfold pow.
  now rewrite iterate_0.
Qed.

Theorem append_ε_l : ∀ b, ε ++ b = b.
Proof.
  intros [b B].
  unfold concat, empty_string.
  apply set_proj_injective.
  simpl.
  repeat destruct constructive_indefinite_description.
  simpl.
  set (f := mkFunc _ _ _ i0).
  replace b with (graph f) by now simpl.
  f_equal.
  assert (x = 0%N).
  { apply set_proj_injective.
    eapply domain_uniqueness; eauto.
    split; auto using Empty_set_is_subset.
    intros a H.
    contradiction (Empty_set_classification a). }
  subst; rename x0 into x.
  apply func_ext; rewrite ? sets.functionify_domain, ? sets.functionify_range;
    simpl; rewrite ? add_0_l in *; auto.
  intros y H.
  replace y with (proj1_sig (exist _ _ H : (elts (0+x)%N))) by auto.
  unfold sets.functionify, concat_elements.
  destruct constructive_indefinite_description.
  destruct a as [H0 [H1 H2]].
  rewrite H2; clear H2.
  simpl.
  destruct excluded_middle_informative; simpl.
  - apply naturals.lt_not_ge in l.
    contradict l.
    auto using zero_le.
  - unfold f.
    f_equal.
    now rewrite sub_0_r.
Qed.

Theorem concat_ε_l : ∀ A, concat_set [ε] A = A.
Proof.
  intros [A HA].
  apply set_proj_injective, Extensionality.
  simpl; split; intros H; apply Powerset_classification in HA.
  - apply Specify_classification in H as [H [a [b [H0 [H1 H2]]]]].
    rewrite singleton_realization, Singleton_classification in H0.
    apply set_proj_injective in H0.
    subst.
    now rewrite append_ε_l.
  - apply Specify_classification.
    split; auto.
    assert (z ∈ STR) as H0 by auto.
    set (ζ := exist _ _ H0 : σ).
    replace z with (proj1_sig ζ) by auto.
    exists ε, ζ.
    rewrite append_ε_l.
    repeat split; auto.
    now rewrite singleton_realization, Singleton_classification.
Qed.

Theorem pow_succ_r : ∀ n A, A^(S n) = concat_set (A^n) A.
Proof.
  induction n using Induction; intros A.
  - now rewrite pow_0_r, pow_1_r, concat_ε_l.
  - unfold pow.
    rewrite iterate_succ; auto.
    exists n.
    rewrite <-add_1_r.
    ring.
Qed.

Theorem subsetifying_subset : ∀ A, subsetify (subset_of A) = A.
Proof.
  now intros a.
Qed.

Section concat_function_construction.

  Variable A B : reg_exp.

  Definition concat_function : elts (A × B) → elts (A || B).
  Proof.
    intros [z H].
    apply Product_classification in H.
    destruct (constructive_indefinite_description _ H) as [a H0].
    clear H.
    destruct (constructive_indefinite_description _ H0) as [b [H1 [H2 H3]]].
    clear H0.
    subst.
    assert (a ∈ STR) as H3 by now apply (reg_exps_are_strings A).
    assert (b ∈ STR) as H4 by now apply (reg_exps_are_strings B).
    set (α := exist _ _ H3 : σ).
    set (β := exist _ _ H4 : σ).
    assert (α ++ β ∈ A || B) as H5.
    { rewrite <-subsetifying_subset, <-concat_reg_exp.
      apply Specify_classification.
      split; try now apply (proj2_sig (α ++ β)).
      now exists α, β. }
    exact (exist _ _ H5).
  Defined.

End concat_function_construction.

Definition concat_product A B := sets.functionify _ _ (concat_function A B).

Theorem concat_product_action :
  ∀ (A B : reg_exp) (x : elts (A × B)) (a b : σ),
    a ∈ A → b ∈ B → proj1_sig x = (a,b) →
    concat_product A B (proj1_sig x) = a ++ b.
Proof.
  intros A B [x X] a b H H0 H1.
  unfold concat_product, sets.functionify.
  destruct constructive_indefinite_description.
  destruct a0 as [H2 [H3 H4]].
  rewrite H4.
  unfold concat_function, sets.functionify.
  destruct constructive_indefinite_description as [a'].
  destruct constructive_indefinite_description as [b'].
  repeat destruct a0.
  simpl.
  destruct constructive_indefinite_description as [n].
  destruct constructive_indefinite_description as [m].
  subst.
  simpl in *.
  destruct a, b.
  apply Ordered_pair_iff in H1 as [H1 H5].
  subst.
  unfold concat.
  repeat destruct constructive_indefinite_description.
  simpl.
  unfold setify in i1, i2.
  simpl in i1, i2.
  assert (x2 = n) as H1 by eauto using set_proj_injective, domain_uniqueness.
  assert (x3 = m) as H5 by eauto using set_proj_injective, domain_uniqueness.
  subst.
  replace i1 with i5 by now apply proof_irrelevance.
  now replace i2 with i6 by now apply proof_irrelevance.
Qed.

Inductive unambiguous : reg_exp → Prop :=
| unambiguous_empty : unambiguous EmptySet
| unambiguous_char x : unambiguous (Char x)
| unambiguous_union A B :
    unambiguous A → unambiguous B → A ∩ B = ∅ → unambiguous (A ⌣ B)
| unambiguous_prod A B :
    unambiguous A → unambiguous B → injective (concat_product A B) →
    unambiguous (A || B)
| unambiguous_star A :
    unambiguous A →
    (∀ n m : N, n ≠ m → (pow A n) ∩ (pow A m) = ∅)%str →
    injective (concat_product A (A ⃰)) →
    unambiguous (A ⃰).

Theorem singleton_unambiguous : ∀ x, unambiguous [x].
Proof.
  apply unambiguous_char.
Qed.

Theorem length_of_n_string :
  ∀ (n : N) (x : σ), x ∈ (([0] ⌣ [1])^n)%str → length x = n.
Proof.
  induction n using Induction.
  - rewrite pow_0_r.
    intros x H.
    rewrite subsetifying_subset, singleton_realization,
    Singleton_classification in H.
    apply set_proj_injective in H.
    subst.
    apply length_empty.
  - intros x H.
    rewrite pow_succ_r in H.
    apply Specify_classification in H as [H [a [b [H0 [H1 H2]]]]].
    apply set_proj_injective in H2.
    subst.
    rewrite concat_length, IHn; auto.
    rewrite <-add_1_r.
    f_equal.
    apply Specify_classification in H1 as [H1 [y [H2 H3]]].
    apply set_proj_injective in H2.
    inversion H3.
    + inversion H6.
      subst.
      apply length_zero.
    + inversion H6.
      subst.
      apply length_one.
Qed.

Theorem ambiguous_singletons : ∀ x, ¬ unambiguous ([x] ⌣ [x]).
Proof.
  intros x H.
  inversion H.
  contradiction (Empty_set_classification x).
  rewrite <-H4.
  apply Pairwise_intersection_classification.
  assert (x ∈ [x]); auto.
  apply Specify_classification.
  split.
  - apply (proj2_sig x).
  - exists x.
    split; auto using MChar.
Qed.

Theorem ambiguous_empty_star : ¬ unambiguous ([ε]⃰).
Proof.
  intros H.
  inversion H.
  rewrite Injective_classification in H3.
  assert (0%N ≠ 1%N) as H4 by apply PA4.
  pose proof (H2 _ _ H4) as H5.
  contradict H5.
  apply Nonempty_classification.
  exists ε.
  apply Pairwise_intersection_classification.
  split.
  - now rewrite pow_0_r, subsetifying_subset,
    singleton_realization, Singleton_classification.
  - now rewrite pow_1_r, subsetifying_subset,
    singleton_realization, Singleton_classification.
Qed.

Theorem zero_ne_1 : 0 ≠ 1.
Proof.
  intros H.
  assert (proj1_sig 0 = proj1_sig 1) as H0 by congruence.
  simpl in H0.
  apply Subset_equality_iff in H0 as [H0 H1].
  assert ((∅, ∅) = (∅, succ ∅)) as H2.
  { rewrite <-Singleton_classification.
    apply H0.
    now rewrite Singleton_classification. }
  apply Ordered_pair_iff in H2 as [H2 H3].
  contradiction (Empty_set_classification ∅).
  rewrite H3 at 2.
  apply Pairwise_union_classification.
  right.
  now apply Singleton_classification.
Qed.

Theorem functionify_injective :
  ∀ s t : σ, (s : function) = (t : function) → s = t.
Proof.
  intros s t H.
  unfold functionify in H.
  repeat destruct constructive_indefinite_description.
  apply set_proj_injective.
  now inversion H.
Qed.

Theorem functionify_concat_l : ∀ a b x, (x < length a)%N → (a ++ b) x = a x.
Proof.
  intros a b x H.
  pose proof length_is_domain a as A0.
  destruct a as [a A], b as [b B].
  unfold functionify, concat in A0 |-*.
  destruct constructive_indefinite_description as [m].
  destruct constructive_indefinite_description as [a'].
  destruct constructive_indefinite_description as [n].
  simpl in *.
  assert (a' = m+n)%N.
  { eapply set_proj_injective, domain_uniqueness; eauto.
    split; intros z H0.
    - apply graph_elements_are_pairs in H0.
      now rewrite sets.functionify_domain, sets.functionify_range in H0.
    - pose proof func_hyp (sets.functionify (m + n)%N {∅, succ ∅}
                                            (concat_elements m n a b i i1))
        as [H1 H2].
      rewrite sets.functionify_domain, sets.functionify_range in H2.
      now apply H2 in H0. }
  subst.
  set (f := mkFunc _ _ _ i0).
  assert (f = (sets.functionify
                 (m + n)%N {∅, succ ∅} (concat_elements m n a b i i1))) as H0.
  { apply function_record_injective; auto.
    now rewrite sets.functionify_range. }
  rewrite H0.
  unfold sets.functionify.
  destruct constructive_indefinite_description as [f'], a0 as [H1 [H2 H3]].
  apply set_proj_injective in A0.
  rewrite <-A0 in H.
  assert (proj1_sig x ∈ m+n)%N as H4.
  { assert (m ≤ m+n)%N as H4 by now (exists n).
    rewrite le_is_subset in H4.
    now apply H4, lt_is_in. }
  set (ξ := exist _ _ H4 : elts (m+n)%N).
  unfold INS.
  replace (proj1_sig x) with (proj1_sig ξ) by auto.
  rewrite H3.
  unfold concat_elements.
  destruct excluded_middle_informative; auto.
  contradict n0.
  unfold ξ.
  simpl.
  destruct x.
  simpl.
  replace (elements_of_naturals_are_naturals (m + n) x (proj2_sig (m + n)) H4)%N
    with i2; auto using proof_irrelevance.
Qed.

Theorem functionify_concat_r : ∀ a b x,
    (length a ≤ x < length a + length b)%N → (a ++ b) x = b (x - length a)%N.
Proof.
  intros a b x [H H0].
  pose proof length_is_domain a as A0.
  pose proof length_is_domain b as B0.
  destruct a as [a A], b as [b B].
  unfold functionify, concat in A0, B0 |-*.
  destruct constructive_indefinite_description as [m].
  destruct constructive_indefinite_description as [n].
  destruct constructive_indefinite_description as [a'].
  simpl in *.
  apply set_proj_injective in A0.
  apply set_proj_injective in B0.
  rewrite <-? A0 in H0, H.
  rewrite <-B0 in H0.
  assert (a' = m+n)%N.
  { eapply set_proj_injective, domain_uniqueness; eauto.
    split; intros z H1.
    - apply graph_elements_are_pairs in H1.
      now rewrite sets.functionify_domain, sets.functionify_range in H1.
    - pose proof func_hyp (sets.functionify (m + n)%N {∅, succ ∅}
                                            (concat_elements m n a b i i0))
           as [H2 H3].
      rewrite sets.functionify_domain, sets.functionify_range in H3.
      now apply H3 in H1. }
  subst a'.
  set (f := mkFunc _ _ _ i1).
  assert (f = (sets.functionify
                 (m + n)%N {∅, succ ∅} (concat_elements m n a b i i0))) as H1.
  { apply function_record_injective; auto.
    now rewrite sets.functionify_range. }
  rewrite H1.
  unfold sets.functionify.
  destruct constructive_indefinite_description as [f'], a0 as [H2 [H3 H4]].
  assert (proj1_sig x ∈ m+n)%N as H5 by now apply lt_is_in.
  set (ξ := exist _ _ H5 : elts (m+n)%N).
  unfold INS.
  replace (proj1_sig x) with (proj1_sig ξ) by auto.
  rewrite H4.
  unfold concat_elements.
  destruct excluded_middle_informative; simpl.
  - apply naturals.le_not_gt in H.
    contradict H.
    destruct x.
    simpl in l.
    replace i2 with
        (elements_of_naturals_are_naturals (m + n) x (proj2_sig (m + n)) H5)%N;
      auto using proof_irrelevance.
  - f_equal.
    rewrite <-A0.
    unfold INS.
    do 2 f_equal.
    destruct x.
    simpl.
    f_equal.
    apply proof_irrelevance.
Qed.

Theorem unambiguous_all_strings : unambiguous (([0] ⌣ [1])⃰).
Proof.
  apply unambiguous_star.
  - apply unambiguous_union; auto using singleton_unambiguous.
    apply Extensionality.
    split; intros H.
    + apply Pairwise_intersection_classification in H as [H H0].
      rewrite singleton_realization, Singleton_classification in *.
      contradiction zero_ne_1.
      apply set_proj_injective.
      unfold setify in *.
      congruence.
    + contradiction (Empty_set_classification z).
  - intros n m H.
    apply NNPP.
    contradict H.
    apply Nonempty_classification in H as [x H].
    apply Pairwise_intersection_classification in H as [H H0].
    assert (x ∈ STR).
    { pose proof (proj2_sig (([0] ⌣ [1]) ^ n)%str) as H1; simpl in H1.
      apply Powerset_classification in H1; auto. }
    set (ξ := (exist _ _ H1 : σ)).
    replace x with (proj1_sig ξ) in * by auto.
    rewrite <-(length_of_n_string n ξ), <-(length_of_n_string m ξ); auto.
  - apply Injective_classification.
    intros x y H H0 H1.
    unfold concat_product in H, H0.
    rewrite sets.functionify_domain in *.
    set (ξ := (exist _ _ H : elts (([0] ⌣ [1]) × Star ([0] ⌣ [1])))).
    set (γ := (exist _ _ H0 : elts (([0] ⌣ [1]) × Star ([0] ⌣ [1])))).
    pose proof H as H2.
    pose proof H0 as H3.
    replace x with (proj1_sig ξ) in * by auto.
    replace y with (proj1_sig γ) in * by auto.
    apply Product_classification in H2 as [x1 [x2 [H4 [H5 H6]]]].
    apply Product_classification in H3 as [y1 [y2 [H7 [H8 H9]]]].
    assert (x1 ∈ STR) as H10 by now apply realization_is_subset in H4.
    assert (x2 ∈ STR) as H11 by now apply realization_is_subset in H5.
    assert (y1 ∈ STR) as H12 by now apply realization_is_subset in H7.
    assert (y2 ∈ STR) as H13 by now apply realization_is_subset in H8.
    set (ζ1 := (exist _ _ H10 : σ)).
    set (ζ2 := (exist _ _ H11 : σ)).
    set (γ1 := (exist _ _ H12 : σ)).
    set (γ2 := (exist _ _ H13 : σ)).
    replace x1 with (proj1_sig ζ1) in * by auto.
    replace x2 with (proj1_sig ζ2) in * by auto.
    replace y1 with (proj1_sig γ1) in * by auto.
    replace y2 with (proj1_sig γ2) in * by auto.
    fold (setify ζ1) (setify ζ2) (setify γ1) (setify γ2) in *.
    erewrite (concat_product_action _ _ ξ ζ1 ζ2),
    (concat_product_action _ _ γ γ1 γ2) in H1; eauto.
    apply set_proj_injective in H1.
    rewrite H6, H9.
    assert (length ζ1 = length γ1) as H2.
    { rewrite ? length_is_domain, ? (length_of_n_string 1); auto;
        now rewrite pow_1_r. }
    do 2 f_equal.
    + apply functionify_injective, func_ext.
      * rewrite ? length_is_domain; congruence.
      * now rewrite ? string_range.
      * intros z H3.
        assert (z ∈ ω) as H14 by eauto using string_domain.
        set (ζ := exist _ _ H14 : N).
        replace z with (proj1_sig ζ) by auto.
        rewrite <-(functionify_concat_l ζ1 ζ2), <-(functionify_concat_l γ1 γ2);
          try congruence.
        -- rewrite length_is_domain, H2 in H3.
           now apply lt_is_in.
        -- rewrite length_is_domain in H3.
           now apply lt_is_in.
    + assert (length ζ2 = length γ2) as H3.
      { eapply naturals.cancellation_add.
        now rewrite <-concat_length, H1, concat_length, H2. }
      apply functionify_injective, func_ext; auto.
      * rewrite ? length_is_domain; congruence.
      * now rewrite ? string_range.
      * intros z H14.
        assert (z ∈ ω) as H15 by eauto using string_domain.
        set (ζ := exist _ _ H15 : N).
        replace z with (INS ζ) by auto.
        rewrite <-(sub_abba ζ (length ζ1)) at 1.
        rewrite <-(sub_abba ζ (length γ1)) at 2.
        assert (length γ1 ≤ ζ + length γ1 < length γ1 + length γ2)%N.
        { split.
          - exists ζ.
            ring.
          - rewrite (naturals.add_comm _ (length γ2)).
            apply naturals.O1, lt_is_in.
            rewrite length_is_domain, H3 in H14.
            apply H14. }
        rewrite <-? functionify_concat_r; congruence.
Qed.
