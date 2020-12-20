Require Export set_theory.

Definition ω : set.
Proof.
  destruct (constructive_indefinite_description _ Infinity) as [X].
  exact (⋂ {x in P X | ∅ ∈ x ∧ Inductive x}).
Defined.

Theorem PA1_ω : ∅ ∈ ω.
Proof.
  unfold empty_set, ω, intersection, union, specify.
  repeat destruct constructive_indefinite_description.
  destruct a as [H H0].
  replace x0 with ∅.
  - apply i0.
    split.
    + apply i3.
      split; [ eapply i1; split; try exact H | exists x1; intuition ];
        apply i2; eauto using Set_in_powerset.
    + intros z H1.
      now apply i2 in H1.
  - apply Extensionality; split; intros H1.
    + now apply Empty_set_classification in H1.
    + now apply i in H1.
Qed.

Theorem PA2_ω : Inductive ω.
Proof.
  unfold ω, intersection, union, specify.
  repeat destruct constructive_indefinite_description.
  intros y H.
  apply i in H as [H H0].
  apply i.
  split.
  - apply i2 in H as [H1 [z [H2 H3]]].
    pose proof H3 as H4.
    apply i1 in H4 as [H4 [H5 H6]].
    apply i2.
    split; eauto.
  - intros z H1.
    pose proof H1 as H2.
    apply H0 in H1.
    apply i1 in H2 as [H2 [H3 H4]].
    eauto.
Qed.

Theorem ω_is_minimal : ∀ s, s ⊂ ω → ∅ ∈ s → Inductive s → ω ⊂ s.
Proof.
  intros s H H0 H1.
  unfold ω, specify in *.
  repeat destruct constructive_indefinite_description.
  assert (s ∈ x0) as H2.
  { apply i.
    split; auto.
    apply Powerset_classification.
    intros z H2.
    assert (x ∈ x0) as H3.
    { apply i.
      split; auto; apply Powerset_classification, Set_is_subset. }
    eapply Intersection_classification;
      try rewrite Nonempty_classification; eauto. }
  intros z H4.
  eapply Intersection_classification; eauto;
    try rewrite Nonempty_classification; eauto.
Qed.

Theorem PA3_ω : ∀ s, s ⊂ ω → ∅ ∈ s → Inductive s → s = ω.
Proof.
  auto using Subset_equality, ω_is_minimal.
Qed.

Theorem PA4_ω : ∀ n, n ∈ ω → succ n ≠ ∅.
Proof.
  intros n H.
  apply Nonempty_classification.
  exists n.
  apply Pairwise_union_classification.
  right.
  apply Pairing_classification; auto.
Qed.

Theorem Induction_ω : ∀ P : set → Prop,
    (∀ n, n ∉ ω → P n) → P ∅ → (∀ m, m ∈ ω → P m → P (succ m)) → ∀ n, P n.
Proof.
  intros P H H0 H1 n.
  destruct (classic (n ∈ ω)); auto.
  replace ω with {x in ω | P x} in H2;
    try (now rewrite Specify_classification in H2); clear n H H2.
  apply PA3_ω; try intros y H; try rewrite Specify_classification in *;
    intuition; auto using PA1_ω, PA2_ω.
Qed.

Theorem elements_of_naturals_are_naturals : ∀ n m, n ∈ ω → m ∈ n → m ∈ ω.
Proof.
  induction n using Induction_ω; intuition.
  - exfalso; eapply Empty_set_classification; eauto.
  - apply Pairwise_union_classification in H1 as [H1 | H1]; auto.
    apply Singleton_classification in H1; congruence.
Qed.

Lemma pigeonhole_precursor : ∀ n m, n ∈ ω → m ∈ n → ¬ n ⊂ m.
Proof.
  induction n using Induction_ω; intuition.
  - eapply Empty_set_classification; eauto.
  - apply Pairwise_union_classification in H1 as [H1 | H1].
    + eapply IHn; eauto.
      intros z H4.
      now apply H2, Pairwise_union_classification, or_introl.
    + apply Singleton_classification in H1.
      subst.
      eapply IHn, Set_is_subset; eauto.
      now apply H2, Pairwise_union_classification,
      or_intror, Singleton_classification.
Qed.

Lemma elements_of_naturals_are_subsets : ∀ n m, n ∈ ω → m ∈ n → m ⊂ n.
Proof.
  induction n using Induction_ω; intuition.
  - exfalso; eapply Empty_set_classification; eauto.
  - apply Pairwise_union_classification in H1 as [H1 | H1]; intros z H3;
      eapply Pairwise_union_classification, or_introl.
    + eapply IHn; eauto.
    + apply Singleton_classification in H1.
      congruence.
Qed.

Theorem PA5_ω : ∀ n m, n ∈ ω → m ∈ ω → succ n = succ m → n = m.
Proof.
  intros n m H H0 H1.
  assert (n ∈ succ m) as H2; assert (m ∈ succ n) as H3; unfold succ in *;
    [ rewrite H1 | rewrite <-H1 | rewrite H1 | ];
    try now apply Pairwise_union_classification, or_intror,
    Singleton_classification.
  rewrite Pairwise_union_classification, Singleton_classification in *.
  destruct H2, H3; auto.
  exfalso; eapply pigeonhole_precursor;
    eauto using elements_of_naturals_are_subsets.
Qed.

Theorem recursion : ∀ f X a,
    a ∈ X → domain f = X → range f = X →
    ∃ u, domain u = ω ∧ range u = X ∧ u ∅ = a ∧
         ∀ n, n ∈ ω → u (succ n) = f (u n).
Proof.
  intros f X a H H0 H1.
  set (C := {A in P (ω × X) |
             (∅,a) ∈ A ∧
             ∀ x n, x ∈ X → n ∈ ω → (n,x) ∈ A → (succ n, f x) ∈ A}).
  set (u := ⋂ C).
  assert (ω × X ∈ C) as H2.
  { apply Specify_classification.
    repeat split.
    - apply Powerset_classification, Set_is_subset.
    - apply Product_classification.
      eauto using PA1_ω.
    - intros x n H2 H3 H4.
      subst.
      apply Product_classification.
      exists (succ n), (f x).
      repeat split; eauto using PA2_ω.
      rewrite <-H1.
      now apply function_maps_domain_to_range. }
  assert (C ≠ ∅) as H3 by (rewrite Nonempty_classification; now exists (ω × X)).
  assert (u ∈ C) as H4.
  { apply Specify_classification.
    repeat split; unfold u in *.
    - apply Powerset_classification.
      intros z H4.
      rewrite Intersection_classification in H4; auto.
    - rewrite Intersection_classification; auto.
      intros z H4.
      now apply Specify_classification in H4.
    - intros x n H4 H5 H6.
      rewrite Intersection_classification in *; auto.
      intros y H7.
      pose proof H6 _ H7 as H8.
      apply Specify_classification in H7 as [H7 [H9 H10]].
      auto. }
  apply Specify_classification in H4 as [H4 [H5 H6]].
  assert (is_function u ω X) as H7.
  { split; unfold u in *.
    - intros z H7.
      rewrite Intersection_classification in H7; auto.
    - intros n H7.
      induction n using Induction_ω; intuition.
      + exists a.
        repeat split; auto.
        intros b [H8 H9].
        apply NNPP.
        intros H10.
        assert (u \ {(∅, b), (∅, b)} ∈ C) as H11.
        { apply Specify_classification.
          repeat split; unfold u in *; intros;
            try rewrite Complement_classification, Singleton_classification,
            Ordered_pair_iff in *; intuition.
          - rewrite Powerset_classification in *.
            intros z H11.
            rewrite Complement_classification, Intersection_classification in *;
              intuition.
          - contradiction (PA4_ω n). }
        rewrite Intersection_classification in *; auto.
        apply H9, Complement_classification in H11 as [H11 H12].
        now rewrite Singleton_classification in *.
      + destruct H9 as [y [[H9 H10] H11]].
        exists (f y).
        repeat split; auto.
        * rewrite <-H1.
          apply function_maps_domain_to_range.
          congruence.
        * intros x' [H12 H13].
          apply NNPP.
          intros H14.
          assert (u \ {(succ n, x'), (succ n, x')} ∈ C) as H15.
          { apply Specify_classification.
            repeat split; unfold u in *; intros;
            try rewrite Complement_classification, Singleton_classification,
            Ordered_pair_iff in *; intuition.
            - apply Powerset_classification.
              intros z H15.
              rewrite Complement_classification, Powerset_classification in *.
              intuition.
            - now apply (PA4_ω n), eq_sym.
            - apply PA5_ω in H20; subst; eauto using f_equal. }
          rewrite Intersection_classification in *; auto.
          apply H13, Specify_classification in H15 as [H15 H16].
          contradict H16.
          now apply Singleton_classification. }
  set (g := (mkFunc ω X u H7)).
  exists g.
  repeat split.
  - apply function_maps_domain_to_graph; auto using PA1_ω.
  - intros n H8.
    apply function_maps_domain_to_graph; simpl; auto using PA2_ω.
    + rewrite <-H1.
      apply function_maps_domain_to_range.
      rewrite H0.
      now apply function_maps_domain_to_range.
    + apply H6; auto; try now apply function_maps_domain_to_range.
      replace u with (graph g); auto.
      apply function_maps_domain_to_graph; auto.
      now apply function_maps_domain_to_range.
Qed.

Definition N := elts ω.

Definition S : N → N.
Proof.
  intros [n H].
  exact (mkSet ω (succ n) (PA2_ω n H)).
Defined.

Theorem S_is_succ : ∀ n : N, (value ω (S n)) = succ (value ω n).
Proof.
  now intros [n H].
Qed.

Notation "0" := (mkSet ω ∅ PA1_ω).
Notation "1" := (S 0).
Notation "2" := (S 1).

Theorem set_proj_injective : ∀ X n m, (value X n) = (value X m) → n = m.
Proof.
  intros S n m H.
  destruct n, m; simpl in *.
  subst.
  assert (in_set = in_set0) by apply proof_irrelevance.
  now subst.
Qed.

Definition add : N → N → N.
Proof.
  intros a b.
  pose proof in_set ω a as A.
  pose proof in_set ω b as B.
  pose proof PA2_ω.
  destruct (constructive_indefinite_description
              _ (function_construction ω ω succ PA2_ω)) as [S [H0 [H1 H2]]].
  destruct (constructive_indefinite_description
              _ (recursion S ω (value ω a) A H0 H1)) as [u_a [H3 [H4 [H5 H6]]]].
  assert (u_a (value ω b) ∈ ω) as H7.
  { rewrite <-H4.
    apply function_maps_domain_to_range.
    now rewrite H3. }
  exact (mkSet ω (u_a (value ω b)) H7).
Defined.

Definition add_right : N → set → set.
Proof.
  intros a x.
  destruct (excluded_middle_informative (x ∈ ω)).
  - exact (value ω (add (mkSet ω x i) a)).
  - exact ∅.
Defined.

Infix "+" := add.

Theorem add_right_lemma : ∀ a b, add_right a (value ω b) = (value ω (b + a)).
Proof.
  intros a b.
  unfold add_right.
  destruct excluded_middle_informative.
  - replace {| value := value ω b; in_set := i |} with b;
      auto using set_proj_injective.
  - contradiction (in_set ω b).
Qed.

Definition mult : N → N → N.
Proof.
  intros a b.
  pose proof in_set ω a as A.
  pose proof in_set ω b as B.
  assert (∀ x : set, x ∈ ω → add_right a x ∈ ω) as H.
  { intros x H.
    unfold add_right.
    destruct excluded_middle_informative; intuition.
    exact (in_set ω ({| value := x; in_set := i |} + a)). }
  destruct (constructive_indefinite_description
              _ (function_construction ω ω (add_right a) H))
    as [add_a [H0 [H1 H2]]].
  destruct (constructive_indefinite_description
              _ (recursion add_a ω ∅ PA1_ω H0 H1)) as [mul_b [H3 [H4 [H5 H6]]]].
  assert (mul_b (value ω b) ∈ ω) as H7.
  { rewrite <-H4.
    apply function_maps_domain_to_range.
    now rewrite H3. }
  exact (mkSet ω (mul_b (value ω b)) H7).
Defined.

Infix "*" := mult.

Theorem Induction : ∀ P : N → Prop,
    P 0 → (∀ n : N, P n → P (S n)) → ∀ n : N, P n.
Proof.
  intros P H H0 n.
  assert (∀ x y, x ∈ ω → value ω y = x → P y) as H1.
  { induction x using Induction_ω; intuition.
    - replace y with 0; auto using set_proj_injective.
    - set (m := mkSet ω x H1).
      replace y with (S m); try apply set_proj_injective; auto. }
  destruct n; eauto.
Qed.

Definition PA3 := Induction.

Theorem PA4 : ∀ n : N, 0 ≠ S n.
Proof.
  intros n H.
  assert (value ω (S n) = value ω 0) by congruence.
  destruct n; simpl in *.
  contradiction (PA4_ω value).
Qed.

Theorem PA5 : ∀ n m, S n = S m → n = m.
Proof.
  intros [n A] [m B] H.
  apply set_proj_injective; auto.
  simpl in *.
  apply PA5_ω; congruence.
Qed.

Theorem add_zero_r : ∀ x, x + 0 = x.
Proof.
  intros x.
  unfold add.
  repeat destruct constructive_indefinite_description.
  repeat destruct a.
  repeat destruct constructive_indefinite_description.
  repeat destruct a.
  now apply set_proj_injective.
Qed.

Theorem add_succ_r : ∀ x y, x + S y = S (x + y).
Proof.
  intros x y.
  unfold add.
  repeat destruct constructive_indefinite_description.
  repeat destruct a.
  repeat destruct constructive_indefinite_description.
  repeat destruct a.
  apply set_proj_injective.
  destruct y.
  simpl.
  rewrite e5, e1; auto.
  rewrite <-e3.
  apply function_maps_domain_to_range.
  now rewrite e2.
Qed.

Theorem mul_zero_r : ∀ x, x * 0 = 0.
Proof.
  intros x.
  unfold mult.
  repeat destruct constructive_indefinite_description.
  repeat destruct a.
  repeat destruct constructive_indefinite_description.
  repeat destruct a.
  now apply set_proj_injective.
Qed.

Theorem mul_succ_r : ∀ x y, x * (S y) = x * y + x.
Proof.
  intros x y.
  unfold mult.
  repeat destruct constructive_indefinite_description.
  repeat destruct a.
  repeat destruct constructive_indefinite_description.
  repeat destruct a.
  apply set_proj_injective.
  simpl.
  pose proof (in_set ω y) as H.
  rewrite S_is_succ, e5, e1, <-add_right_lemma; auto.
  rewrite <-e3.
  apply function_maps_domain_to_range.
  now rewrite e2.
Qed.

Theorem add_comm : ∀ a b, a + b = b + a.
Proof.
  induction a using Induction; induction b using Induction; auto.
  - now rewrite add_zero_r, add_succ_r, IHb in *.
  - now rewrite add_zero_r, add_succ_r, <-IHa, add_zero_r.
  - now rewrite ? add_succ_r, IHb, <-? IHa, ? add_succ_r, IHa.
Qed.

Theorem add_assoc : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  induction c using Induction.
  - now rewrite ? add_zero_r.
  - now rewrite ? add_succ_r, IHc.
Qed.

Theorem mul_1_r : ∀ a, a * 1 = a.
Proof.
  intros a.
  now rewrite mul_succ_r, mul_zero_r, add_comm, add_zero_r.
Qed.

Theorem mul_distr_r : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  induction c using Induction.
  - now rewrite ? mul_zero_r, add_zero_r.
  - now rewrite ? (mul_succ_r), IHc, ? add_assoc,
    <-(add_assoc (a*c)), (add_comm _ a), ? add_assoc.
Qed.

Theorem mul_comm : ∀ a b, a * b = b * a.
Proof.
  induction a using Induction; induction b using Induction; auto.
  - now rewrite mul_succ_r, IHb, ? mul_zero_r, add_zero_r.
  - now rewrite mul_succ_r, <-IHa, ? mul_zero_r, add_zero_r.
  - now rewrite ? mul_succ_r, ? IHb, <-? IHa, ? mul_succ_r,
    <-? add_assoc, ? add_succ_r, IHa, (add_comm a).
Qed.

Theorem mul_distr_l : ∀ a b c, a * (b + c) = a * b + a * c.
Proof.
  intros a b c.
  now rewrite mul_comm, mul_distr_r, ? (mul_comm a).
Qed.

Theorem mul_assoc : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  induction c using Induction.
  - now rewrite ? mul_zero_r.
  - now rewrite ? (mul_succ_r), mul_distr_l, IHc.
Qed.
