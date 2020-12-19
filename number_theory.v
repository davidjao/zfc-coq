Require Export set_theory.

Notation "0" := ∅.
Notation "1" := (succ 0).
Notation "2" := (succ 1).

Notation PA1 := N_has_zero.
Notation PA2 := N_is_inductive.
Notation PA3 := N_is_minimal_2.

Theorem PA4 : ∀ n, n ∈ N → succ n ≠ 0.
Proof.
  intros n H.
  apply Nonempty_classification.
  exists n.
  apply Pairwise_union_classification.
  right.
  apply Pairing_classification; auto.
Qed.

Theorem Induction : ∀ P : set → Prop,
    (∀ n, n ∉ N → P n) → P 0 → (∀ m, m ∈ N → P m → P (succ m)) → ∀ n, P n.
Proof.
  intros P H H0 H1 n.
  destruct (classic (n ∈ N)); auto.
  replace N with {x in N | P x} in H2;
    try (now rewrite Specify_classification in H2); clear n H H2.
  apply PA3; try intros y H; try rewrite Specify_classification in *;
    intuition; auto using PA1, PA2.
Qed.

Theorem elements_of_naturals_are_naturals : ∀ n m, n ∈ N → m ∈ n → m ∈ N.
Proof.
  induction n using Induction; intuition.
  - exfalso; eapply Empty_set_classification; eauto.
  - apply Pairwise_union_classification in H1 as [H1 | H1]; auto.
    apply Singleton_classification in H1; congruence.
Qed.

Lemma pigeonhole_precursor : ∀ n m, n ∈ N → m ∈ n → ¬ n ⊂ m.
Proof.
  induction n using Induction; intuition.
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

Lemma elements_of_naturals_are_subsets : ∀ n m, n ∈ N → m ∈ n → m ⊂ n.
Proof.
  induction n using Induction; intuition.
  - exfalso; eapply Empty_set_classification; eauto.
  - apply Pairwise_union_classification in H1 as [H1 | H1]; intros z H3;
      eapply Pairwise_union_classification, or_introl.
    + eapply IHn; eauto.
    + apply Singleton_classification in H1.
      congruence.
Qed.

Theorem PA5 : ∀ n m, n ∈ N → m ∈ N → succ n = succ m → n = m.
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
    ∃ u, domain u = N ∧ range u = X ∧ u[0] = a ∧
         ∀ n, n ∈ N → u[succ n] = f[u[n]].
Proof.
  intros f X a H H0 H1.
  set (C := {A in P (N × X) |
             (0,a) ∈ A ∧
             ∀ x n, x ∈ X → n ∈ N → (n,x) ∈ A → (succ n, f[x]) ∈ A}).
  set (u := ⋂ C).
  assert (N × X ∈ C) as H2.
  { apply Specify_classification.
    repeat split.
    - apply Powerset_classification, Set_is_subset.
    - apply Product_classification.
      eauto using PA1.
    - intros x n H2 H3 H4.
      subst.
      apply Product_classification.
      exists (succ n), (f[x]).
      repeat split; eauto using PA2.
      rewrite <-H1.
      now apply function_maps_domain_to_range. }
  assert (C ≠ ∅) as H3 by (rewrite Nonempty_classification; now exists (N × X)).
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
  assert (is_function u N X) as H7.
  { split; unfold u in *.
    - intros z H7.
      rewrite Intersection_classification in H7; auto.
    - intros n H7.
      induction n using Induction; intuition.
      + exists a.
        repeat split; auto.
        intros b [H8 H9].
        apply NNPP.
        intros H10.
        assert (u \ {(0, b), (0, b)} ∈ C) as H11.
        { apply Specify_classification.
          repeat split; unfold u in *; intros;
            try rewrite Complement_classification, Singleton_classification,
            Ordered_pair_iff in *; intuition.
          - rewrite Powerset_classification in *.
            intros z H11.
            rewrite Complement_classification, Intersection_classification in *;
              intuition.
          - contradiction (PA4 n). }
        rewrite Intersection_classification in *; auto.
        apply H9, Complement_classification in H11 as [H11 H12].
        now rewrite Singleton_classification in *.
      + destruct H9 as [y [[H9 H10] H11]].
        exists (f[y]).
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
            - now apply (PA4 n), eq_sym.
            - apply PA5 in H20; subst; eauto using f_equal. }
          rewrite Intersection_classification in *; auto.
          apply H13, Specify_classification in H15 as [H15 H16].
          contradict H16.
          now apply Singleton_classification. }
  set (g := (mkFunc N X u H7)).
  exists g.
  repeat split.
  - apply function_maps_domain_to_graph; auto using PA1.
  - intros n H8.
    apply function_maps_domain_to_graph; simpl; auto using PA2.
    + rewrite <-H1.
      apply function_maps_domain_to_range.
      rewrite H0.
      now apply function_maps_domain_to_range.
    + apply H6; auto; try now apply function_maps_domain_to_range.
      replace u with (graph g); auto.
      apply function_maps_domain_to_graph; auto.
      now apply function_maps_domain_to_range.
Qed.

Print Assumptions recursion.

Record natural : Type := mkNat { number : set; is_n : number ∈ N }.
(*
Definition add : natural → natural → natural.
Proof.
  intros a b.
  pose proof is_n a as A.
  pose proof is_n b as B.
  induction (number b) using Induction.
*)
