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

Lemma ω_is_transitive : ∀ x y z,
    x ∈ ω → y ∈ ω → z ∈ ω → x ∈ y → y ∈ z → x ∈ z.
Proof.
  intros x y z H H0 H1 H2 H3.
  apply elements_of_naturals_are_subsets in H3; auto.
Qed.

Lemma subsets_of_naturals_are_elements :
  ∀ n m, n ∈ ω → m ∈ ω → m ⊂ n → m ≠ n → m ∈ n.
Proof.
  induction n using Induction_ω; intuition.
  - apply Nonempty_classification in H2 as [x H2].
    apply H1 in H2.
    contradiction (Empty_set_classification x).
  - destruct (classic (m = n)) as [H4 | H4].
    + now apply Pairwise_union_classification,
      or_intror, Singleton_classification.
    + eapply elements_of_naturals_are_subsets; auto.
      * now apply Pairwise_union_classification, or_intror,
        Singleton_classification.
      * apply IHn; auto.
        intros x H5.
        pose proof H2 _ H5 as H6.
        apply Pairwise_union_classification in H6 as [H6 | H6]; auto.
        apply Singleton_classification in H6.
        subst.
        contradict H3.
        apply Subset_equality_iff.
        split; auto.
        intros x H6.
        apply Pairwise_union_classification in H6 as [H6 | H6].
        -- eapply elements_of_naturals_are_subsets; eauto.
        -- apply Singleton_classification in H6.
           congruence.
Qed.

Lemma ω_trichotomy : ∀ n m, n ∈ ω → m ∈ ω → m ⊂ n ∨ n ⊂ m.
Proof.
  intros n m H H0.
  induction n using Induction_ω; intuition.
  - apply or_intror, Empty_set_is_subset.
  - left.
    intros x H2.
    apply Pairwise_union_classification.
    left.
    now apply H3.
  - destruct (classic (n = m)); [ left | right ]; intros x H4.
    + apply Pairwise_union_classification, or_introl.
      congruence.
    + apply subsets_of_naturals_are_elements in H2; auto.
      apply Pairwise_union_classification in H4 as [H4 | H4]; auto.
      apply Singleton_classification in H4.
      congruence.
Qed.

Lemma ω_irreflexive : ∀ n m, n ∈ ω → m ∈ ω → ¬ (n ∈ m ∧ m ∈ n).
Proof.
  intros n m H H0 [H1 H2].
  apply elements_of_naturals_are_subsets in H1; auto.
  eapply pigeonhole_precursor; eauto using Set_is_subset.
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

Theorem ω_WOP : ∀ X, X ≠ ∅ → X ⊂ ω → ∃ x, x ∈ X ∧ ∀ y, y ∈ X → x ⊂ y.
Proof.
  intros X H H0.
  apply Nonempty_classification in H as [x H].
  assert (x ∈ ω) as H1 by now apply H0.
  revert x X H0 H1 H.
  induction x using Induction_ω; intuition.
  - exists ∅.
    split; auto using Empty_set_is_subset.
  - destruct (IHx (X ∪ {x,x})) as [y [H3 H4]]; auto;
      try now apply Pairwise_union_classification,
      or_intror, Singleton_classification.
    { intros y H3.
      apply Pairwise_union_classification in H3 as [H3 | H3]; eauto.
      apply Singleton_classification in H3.
      now subst. }
    destruct (classic (x ∈ X)) as [H5 | H5].
    + assert (X ∪ {x,x} = X).
      { apply Extensionality.
        split; intros H6.
        - apply Pairwise_union_classification in H6 as [H6 | H6]; auto.
          apply Singleton_classification in H6.
          congruence.
        - now apply Pairwise_union_classification, or_introl. }
      rewrite H6 in *.
      exists y.
      tauto.
    + apply Pairwise_union_classification in H3 as [H3 | H3].
      * exists y.
        split; auto.
        intros y0 H7.
        now apply H4, Pairwise_union_classification, or_introl.
      * rewrite Singleton_classification in H3.
        subst.
        exists (succ x).
        split; auto.
        intros y H3 z H6.
        apply Pairwise_union_classification in H6 as [H6 | H6].
        -- apply H4; auto.
           now apply Pairwise_union_classification, or_introl.
        -- apply Singleton_classification in H6.
           subst.
           apply subsets_of_naturals_are_elements; auto.
           ++ now apply H4, Pairwise_union_classification, or_introl.
           ++ intros H6.
              congruence.
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

Delimit Scope N_scope with N.
Open Scope N_scope.
Bind Scope N_scope with N.

Definition zero := (mkSet ω ∅ PA1_ω). (* PA1 : Zero is a natural. *)

Definition S : N → N. (* PA2 : The successor of a natural is a natural. *)
Proof.
  intros [_ n H].
  exact (mkSet ω (succ n) (PA2_ω n H)).
Defined.

Notation "0" := zero : N_scope.
Notation "1" := (S 0) : N_scope.
Notation "2" := (S 1) : N_scope.

Theorem S_is_succ : ∀ n : N, (value ω (S n)) = succ (value ω n).
Proof.
  now intros [n H].
Qed.

Definition add : N → N → N.
Proof.
  intros a b.
  pose proof PA2_ω.
  destruct (constructive_indefinite_description
              _ (function_construction ω ω succ PA2_ω)) as [X [H0 [H1 H2]]].
  destruct (constructive_indefinite_description
              _ (recursion X ω (value ω a) (in_set ω a) H0 H1))
    as [u_a [H3 [H4 [H5 H6]]]].
  assert (u_a (value ω b) ∈ ω) as H7.
  { rewrite <-H4.
    apply function_maps_domain_to_range.
    rewrite H3.
    apply in_set. }
  exact (mkSet ω (u_a (value ω b)) H7).
Defined.

Infix "+" := add : N_scope.

Definition add_right : N → set → set.
Proof.
  intros a x.
  destruct (excluded_middle_informative (x ∈ ω)).
  - exact (value ω (add (mkSet ω x i) a)).
  - exact ∅.
Defined.

Theorem add_right_lemma : ∀ a b, add_right a (value ω b) = (value ω (b + a)).
Proof.
  intros a b.
  unfold add_right.
  destruct excluded_middle_informative.
  - replace {| value := value ω b; in_set := i |} with b;
      auto using set_proj_injective.
  - contradiction (in_set ω b).
Qed.

Definition mul : N → N → N.
Proof.
  intros a b.
  assert (∀ x : set, x ∈ ω → add_right a x ∈ ω) as H.
  { intros x H.
    unfold add_right.
    destruct excluded_middle_informative; intuition.
    apply in_set. }
  destruct (constructive_indefinite_description
              _ (function_construction ω ω (add_right a) H))
    as [add_a [H0 [H1 H2]]].
  destruct (constructive_indefinite_description
              _ (recursion add_a ω ∅ PA1_ω H0 H1)) as [mul_b [H3 [H4 [H5 H6]]]].
  assert (mul_b (value ω b) ∈ ω) as H7.
  { rewrite <-H4.
    apply function_maps_domain_to_range.
    rewrite H3.
    apply in_set. }
  exact (mkSet ω (mul_b (value ω b)) H7).
Defined.

Infix "*" := mul : N_scope.

Theorem Induction : ∀ P : N → Prop,
    P 0 → (∀ n : N, P n → P (S n)) → ∀ n : N, P n.
Proof.
  intros P H H0 [_ n H1].
  induction n using Induction_ω; intuition.
  - rewrite <-(set_proj_injective ω 0); auto using set_proj_injective.
  - replace {| value := succ n; in_set := H1 |} with
        (S {| value := n; in_set := H2 |}); try apply set_proj_injective; auto.
Qed.

Definition PA3 := Induction.

Theorem PA4 : ∀ n, 0 ≠ S n.
Proof.
  intros n H.
  assert (value ω (S n) = value ω 0) by congruence.
  destruct n; simpl in *.
  contradiction (PA4_ω value).
Qed.

Theorem succ_0 : ∀ n : N, n ≠ 0 ↔ ∃ m, n = S m.
Proof.
  intros n.
  induction n using Induction; split; intros H.
  - now contradict H.
  - destruct H as [m H].
    contradiction (PA4 m).
  - now (exists n).
  - intros H0.
    now contradiction (PA4 n).
Qed.

Theorem PA5 : ∀ n m, S n = S m → n = m.
Proof.
  intros [n A] [m B] H.
  apply set_proj_injective; auto.
  simpl in *.
  apply PA5_ω; congruence.
Qed.

Theorem neq_succ : ∀ n, n ≠ S n.
Proof.
  induction n using Induction; intros H.
  - eapply PA4; eauto.
  - eauto using PA5.
Qed.

Theorem add_0_r : ∀ x, x + 0 = x.
Proof.
  intros x.
  unfold add.
  repeat (destruct constructive_indefinite_description; repeat destruct a).
  now apply set_proj_injective.
Qed.

Theorem add_succ_r : ∀ x y, x + S y = S (x + y).
Proof.
  intros x y.
  unfold add.
  repeat (destruct constructive_indefinite_description; repeat destruct a).
  apply set_proj_injective.
  destruct y.
  simpl.
  rewrite e5, e1; auto.
  rewrite <-e3.
  apply function_maps_domain_to_range.
  now rewrite e2.
Qed.

Theorem mul_0_r : ∀ x, x * 0 = 0.
Proof.
  intros x.
  unfold mul.
  repeat (destruct constructive_indefinite_description; repeat destruct a).
  now apply set_proj_injective.
Qed.

Theorem mul_succ_r : ∀ x y, x * (S y) = x * y + x.
Proof.
  intros x y.
  unfold mul.
  repeat (destruct constructive_indefinite_description; repeat destruct a).
  apply set_proj_injective.
  simpl.
  rewrite S_is_succ, e5, e1, <-add_right_lemma; auto using in_set.
  rewrite <-e3.
  apply function_maps_domain_to_range.
  rewrite e2.
  apply in_set.
Qed.

Theorem add_1_r : ∀ a, a + 1 = S a.
Proof.
  intros a.
  now rewrite add_succ_r, add_0_r.
Qed.

Theorem add_comm : ∀ a b, a + b = b + a.
Proof.
  induction a using Induction; induction b using Induction; auto.
  - now rewrite add_0_r, add_succ_r, IHb in *.
  - now rewrite add_0_r, add_succ_r, <-IHa, add_0_r.
  - now rewrite ? add_succ_r, IHb, <-? IHa, ? add_succ_r, IHa.
Qed.

Theorem add_assoc : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  induction c using Induction.
  - now rewrite ? add_0_r.
  - now rewrite ? add_succ_r, IHc.
Qed.

Theorem cancellation_0 : ∀ a b, a + b = a → b = 0.
Proof.
  induction a using Induction; intros b H.
  - now rewrite add_comm, add_0_r in H.
  - apply IHa, PA5.
    now rewrite add_comm, <-add_succ_r, add_comm.
Qed.

Theorem cancellation_add : ∀ a b c, a + c = b + c → a = b.
Proof.
  induction c using Induction; intros H.
  - now rewrite ? add_0_r in *.
  - apply IHc, PA5.
    now rewrite <-? add_succ_r.
Qed.

Theorem mul_1_r : ∀ a, a * 1 = a.
Proof.
  intros a.
  now rewrite mul_succ_r, mul_0_r, add_comm, add_0_r.
Qed.

Theorem mul_2_r : ∀ x, x * 2 = x + x.
Proof.
  intros x.
  now rewrite mul_succ_r, mul_1_r.
Qed.

Theorem mul_distr_r : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  induction c using Induction.
  - now rewrite ? mul_0_r, add_0_r.
  - now rewrite ? (mul_succ_r), IHc, ? add_assoc,
    <-(add_assoc (a*c)), (add_comm _ a), ? add_assoc.
Qed.

Theorem mul_comm : ∀ a b, a * b = b * a.
Proof.
  induction a using Induction; induction b using Induction; auto.
  - now rewrite mul_succ_r, IHb, ? mul_0_r, add_0_r.
  - now rewrite mul_succ_r, <-IHa, ? mul_0_r, add_0_r.
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
  - now rewrite ? mul_0_r.
  - now rewrite ? (mul_succ_r), mul_distr_l, IHc.
Qed.

Definition mul_right : N → set → set.
Proof.
  intros a x.
  destruct (excluded_middle_informative (x ∈ ω)).
  - exact (value ω (mul (mkSet ω x i) a)).
  - exact ∅.
Defined.

Theorem mul_right_lemma : ∀ a b, mul_right a (value ω b) = (value ω (b * a)).
Proof.
  intros a b.
  unfold mul_right.
  destruct excluded_middle_informative.
  - replace {| value := value ω b; in_set := i |} with b;
      auto using set_proj_injective.
  - now destruct b.
Qed.

Definition pow : N → N → N.
Proof.
  intros a b.
  assert (∀ x : set, x ∈ ω → mul_right a x ∈ ω) as H.
  { intros x H.
    unfold mul_right.
    destruct excluded_middle_informative; intuition.
    apply in_set. }
  destruct (constructive_indefinite_description
              _ (function_construction ω ω (mul_right a) H))
    as [add_a [H0 [H1 H2]]].
  destruct (constructive_indefinite_description
              _ (recursion add_a ω (value ω 1) (in_set ω 1) H0 H1))
    as [pow_b [H3 [H4 [H5 H6]]]].
  assert (pow_b (value ω b) ∈ ω) as H7.
  { rewrite <-H4.
    apply function_maps_domain_to_range.
    rewrite H3.
    apply in_set. }
  exact (mkSet ω (pow_b (value ω b)) H7).
Defined.

Infix "^" := pow : N_scope.

Theorem pow_0_r : ∀ x, x^0 = 1.
Proof.
  intros x.
  unfold pow.
  repeat (destruct constructive_indefinite_description; repeat destruct a).
  now apply set_proj_injective.
Qed.

Theorem pow_succ_r : ∀ x y, x^(S y) = x^y * x.
Proof.
  intros x y.
  unfold pow.
  repeat (destruct constructive_indefinite_description; repeat destruct a).
  apply set_proj_injective.
  simpl.
  rewrite S_is_succ, e5, e1, <-mul_right_lemma; auto using in_set.
  rewrite <-e3.
  apply function_maps_domain_to_range.
  rewrite e2.
  apply in_set.
Qed.

Theorem pow_1_r : ∀ x, x^1 = x.
Proof.
  intros x.
  now rewrite pow_succ_r, pow_0_r, mul_comm, mul_1_r.
Qed.

Theorem pow_0_l : ∀ x, x ≠ 0 → 0^x = 0.
Proof.
  intros x H.
  rewrite succ_0 in *.
  destruct H as [m H].
  subst.
  now rewrite pow_succ_r, mul_0_r.
Qed.

Theorem pow_1_l : ∀ x, 1^x = 1.
Proof.
  induction x using Induction.
  - now rewrite pow_0_r.
  - now rewrite pow_succ_r, mul_1_r.
Qed.

Theorem pow_2_r : ∀ x, x^2 = x*x.
Proof.
  intros x.
  now rewrite pow_succ_r, pow_1_r.
Qed.

Theorem pow_add_r : ∀ a b c, a^(b+c) = a^b * a^c.
Proof.
  induction c using Induction.
  - now rewrite add_0_r, pow_0_r, mul_1_r.
  - now rewrite add_succ_r, ? pow_succ_r, IHc, mul_assoc.
Qed.

Theorem pow_mul_l : ∀ a b c, (a*b)^c = a^c * b^c.
Proof.
  induction c using Induction.
  - now rewrite ? pow_0_r, mul_1_r.
  - now rewrite ? pow_succ_r, <-? mul_assoc,
    (mul_assoc a), (mul_comm _ (b^c)), IHc, ? mul_assoc.
Qed.

Theorem pow_mul_r : ∀ a b c, a^(b*c) = (a^b)^c.
Proof.
  induction c using Induction.
  - now rewrite mul_0_r, ? pow_0_r.
  - now rewrite mul_succ_r, pow_succ_r, pow_add_r, IHc.
Qed.

Definition le a b := ∃ c, a + c = b.

Infix "≤" := le : N_scope.
Notation "a ≥ b" := (b ≤ a) (only parsing) : N_scope.

Definition lt a b := a ≤ b ∧ a ≠ b.

Infix "<" := lt : N_scope.
Notation "a > b" := (b < a) (only parsing) : N_scope.

Theorem le_is_subset : ∀ a b, a ≤ b ↔ (value ω a) ⊂ (value ω b).
Proof.
  intros a b.
  split; intros H.
  - destruct H as [c H].
    revert b H.
    induction c using Induction; intros b H; rewrite <-H.
    + rewrite add_0_r.
      auto using Set_is_subset.
    + eapply Subset_transitive; eauto.
      rewrite add_succ_r, S_is_succ.
      intros x H0.
      now apply Pairwise_union_classification, or_introl.
  - induction b using Induction.
    + exists 0.
      rewrite add_0_r.
      apply set_proj_injective, NNPP.
      intros H0.
      apply Nonempty_classification in H0 as [x H0].
      contradiction (Empty_set_classification x).
      auto.
    + destruct (classic (value ω b ∈ value ω a)).
      * exists 0.
        rewrite add_0_r.
        apply set_proj_injective, Subset_equality_iff.
        split; auto.
        intros x H1.
        rewrite S_is_succ in H1.
        apply Pairwise_union_classification in H1 as [H1 | H1];
          try now (rewrite Singleton_classification in *; subst).
        now (eapply elements_of_naturals_are_subsets; eauto using in_set).
      * destruct IHb as [x H1].
        { intros x H1.
          pose proof H _ H1 as H2.
          rewrite S_is_succ in H2.
          apply Pairwise_union_classification in H2 as [H2 | H2]; auto.
          apply Singleton_classification in H2.
          now subst. }
        exists (S x).
        now rewrite add_succ_r, H1.
Qed.

Theorem lt_is_in : ∀ a b, a < b ↔ (value ω a) ∈ (value ω b).
  intros a b.
  split; intros H; unfold lt in *; rewrite le_is_subset in *.
  - destruct H as [H H0].
    eapply subsets_of_naturals_are_elements; auto using in_set.
    contradict H0.
    now apply set_proj_injective.
  - split.
    + apply elements_of_naturals_are_subsets; auto using in_set.
    + apply pigeonhole_precursor in H; auto using in_set.
      contradict H.
      subst.
      auto using Set_is_subset.
Qed.

Theorem le_trichotomy : ∀ a b, a ≤ b ∨ b ≤ a.
Proof.
  intros a b.
  rewrite ? le_is_subset.
  auto using ω_trichotomy, in_set.
Qed.

Theorem lt_trichotomy : ∀ a b, a < b ∨ a = b ∨ a > b.
Proof.
  intros a b.
  pose proof le_trichotomy a b.
  pose proof (classic (a = b)).
  unfold lt.
  intuition.
Qed.

Theorem le_antisymm : ∀ a b, a ≤ b ∧ b ≤ a → a = b.
Proof.
  intros a b H.
  rewrite ? le_is_subset in *.
  now apply set_proj_injective, Subset_equality_iff.
Qed.

Theorem lt_antisym : ∀ a b, a < b → ¬ b < a.
Proof.
  intros a b H H0.
  rewrite ? lt_is_in in *.
  eapply ω_irreflexive; eauto using in_set.
Qed.

Theorem lt_irrefl : ∀ a, ¬ a < a.
Proof.
  intros a.
  unfold lt.
  tauto.
Qed.

Theorem le_refl : ∀ a, a ≤ a.
Proof.
  intros a.
  exists 0.
  now rewrite add_0_r.
Qed.

Theorem lt_def : ∀ a b, a < b ↔ ∃ c : N, c ≠ 0 ∧ a + c = b.
Proof.
  unfold lt; split; intros [x H].
  - destruct x as [c H0].
    exists c.
    split; auto.
    contradict H.
    subst.
    now rewrite add_0_r.
  - destruct H as [H H0].
    split.
    + now (exists x).
    + contradict H.
      subst.
      eauto using cancellation_0.
Qed.

Theorem cancellation : ∀ a b, a * b = 0 → a = 0 ∨ b = 0.
Proof.
  induction a using Induction; induction b using Induction; auto.
  intros H.
  rewrite mul_succ_r, add_succ_r in H.
  exfalso.
  symmetry in H.
  eapply PA4; eauto.
Qed.

Theorem mul_lt_r : ∀ a b c, c ≠ 0 → a < b → a * c < b * c.
Proof.
  intros a b c H H0.
  rewrite lt_def in *.
  destruct H0 as [n [H0 H1]].
  exists (n*c).
  split.
  - contradict H.
    apply cancellation in H.
    tauto.
  - now rewrite <-mul_distr_r, H1.
Qed.

Theorem mul_le_r : ∀ a b c, a ≤ b → a * c ≤ b * c.
Proof.
  intros a b c [n H].
  exists (n*c).
  now rewrite <-mul_distr_r, H.
Qed.

Theorem cancellation_mul : ∀ a b c : N, c ≠ 0 → a * c = b * c → a = b.
Proof.
  intros a b c H H0.
  destruct (lt_trichotomy a b) as [H1 | [H1 | H1]]; auto;
    eapply mul_lt_r in H1; eauto; rewrite H0 in H1;
      exfalso; eapply lt_irrefl; eauto.
Qed.
