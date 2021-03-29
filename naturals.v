Require Export sets Ring.

Theorem Infinity_ω: ∃ X, ∅ ∈ X ∧ Inductive X.
Proof.
  destruct Infinity as [X [[e [H H0]] H1]].
  exists X.
  unfold Inductive, succ.
  split.
  - replace ∅ with e; auto.
    apply Extensionality.
    split; intros H2; firstorder.
    contradiction (Empty_set_classification z).
  - intros y H2.
    apply H1 in H2 as [Y [H2 H3]].
    replace (y ∪ {y,y}) with Y; auto.
    apply Extensionality.
    split; rewrite Pairwise_union_classification Singleton_classification;
      apply H3.
Qed.

Definition ω : set.
Proof.
  destruct (constructive_indefinite_description Infinity_ω) as [X].
  exact (⋂ {x in P X | ∅ ∈ x ∧ Inductive x}).
Defined.

Theorem PA1_ω : ∅ ∈ ω.
Proof.
  unfold empty_set, ω, intersection, union, specify.
  repeat destruct constructive_indefinite_description.
  destruct a as [H H0].
  replace x with ∅.
  - apply i.
    split.
    + apply i2.
      split.
      * eapply i0.
        split; try exact H; apply i1; eauto using Set_in_powerset.
      * exists x0.
        split; auto; apply i1; eauto using Set_in_powerset.
    + intros z H1.
      now apply i1 in H1.
  - apply Extensionality; split; intros H1.
    + now apply Empty_set_classification in H1.
    + now apply n in H1.
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
  now apply Pairwise_union_classification,
  or_intror, Pairing_classification, or_intror.
Qed.

Theorem Induction_ω : ∀ P : set → Prop,
    (∀ n, n ∉ ω → P n) → P ∅ → (∀ m, m ∈ ω → P m → P (succ m)) → ∀ n, P n.
Proof.
  intros P H H0 H1 n.
  destruct (classic (n ∈ ω)); auto.
  replace ω with {x in ω | P x} in H2;
    try (now rewrite -> Specify_classification in H2); clear n H H2.
  apply PA3_ω; try intros y H; try rewrite -> Specify_classification in *;
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
    + eauto using Subset_transitive, subset_succ.
    + apply Singleton_classification in H1.
      subst.
      eapply IHn; eauto using Set_is_subset, in_succ.
Qed.

Theorem no_quines_ω : ∀ n, n ∈ ω → ¬ n ∈ n.
Proof.
  intros n H H0.
  apply pigeonhole_precursor in H0; auto using Set_is_subset.
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
  - destruct (classic (m = n)) as [H4 | H4]; subst; auto using in_succ.
    eapply elements_of_naturals_are_subsets; auto.
    + now apply Pairwise_union_classification, or_intror,
      Singleton_classification.
    + apply IHn; auto.
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
      * eapply elements_of_naturals_are_subsets; eauto.
      * apply Singleton_classification in H6.
        congruence.
Qed.

Lemma ω_trichotomy : ∀ n m, n ∈ ω → m ∈ ω → m ⊂ n ∨ n ⊂ m.
Proof.
  intros n m H H0.
  induction n using Induction_ω; intuition;
    eauto using Empty_set_is_subset, Subset_transitive, subset_succ.
  destruct (classic (n = m)); [ left | right ]; intros x H4; subst.
  - now apply subset_succ.
  - apply subsets_of_naturals_are_elements in H2; auto.
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

Theorem union_succ : ∀ n, n ∈ ω → ⋃ succ n = n.
Proof.
  intros n H.
  unfold succ.
  apply Extensionality.
  split; intros H0; rewrite -> Union_classification in *; eauto using in_succ.
  destruct H0 as [x [H0 H1]].
  rewrite -> Pairwise_union_classification, Singleton_classification in H0.
  destruct H0; try congruence.
  apply (ω_is_transitive _ x); eauto using elements_of_naturals_are_naturals.
Qed.

Theorem union_ω : ∀ {n}, n ∈ ω → ⋃ n ∈ ω.
Proof.
  induction n using Induction_ω; rewrite -> ? Empty_union, ? union_succ; tauto.
Qed.

Theorem PA5_ω : ∀ n m, n ∈ ω → m ∈ ω → succ n = succ m → n = m.
Proof.
  intros n m H H0 H1.
  now rewrite <-union_succ, <-H1, union_succ.
Qed.

Theorem ω_WOP : ∀ X, X ≠ ∅ → X ⊂ ω → ∃ x, x ∈ X ∧ ∀ y, y ∈ X → x ⊂ y.
Proof.
  intros X H H0.
  apply Nonempty_classification in H as [x H].
  assert (x ∈ ω) as H1 by now apply H0.
  revert x X H0 H1 H.
  induction x using Induction_ω; intuition; eauto using Empty_set_is_subset.
  destruct (IHx (X ∪ {x,x})) as [y [H3 H4]];
    rewrite ? Pairwise_union_classification ? Singleton_classification; auto.
  { intros y H3.
    rewrite -> Pairwise_union_classification, Singleton_classification in H3.
    destruct H3; subst; auto. }
  destruct (classic (x ∈ X)) as [H5 | H5].
  - assert (X ∪ {x,x} = X); auto.
    apply Extensionality.
    split; intros H6;
      rewrite -> Pairwise_union_classification, Singleton_classification in *;
      try destruct H6; subst; auto.
  - apply Pairwise_union_classification in H3 as [H3 | H3].
    + exists y.
      split; auto.
      intros y0 H7.
      now apply H4, Pairwise_union_classification, or_introl.
    + rewrite -> Singleton_classification in H3.
      subst.
      exists (x ∪ {x,x}).
      split; auto.
      intros y H3 z H6.
      assert (x ⊂ y) as H7.
      { apply H4; auto.
        now apply Pairwise_union_classification, or_introl. }
      rewrite -> Pairwise_union_classification, Singleton_classification in H6.
      destruct H6; subst; auto.
      apply subsets_of_naturals_are_elements; auto.
      contradict H5.
      congruence.
Qed.

Definition 𝐍 := ω.
Definition N := elts ω.

Declare Scope N_scope.
Delimit Scope N_scope with N.
Open Scope N_scope.
Bind Scope N_scope with N.

Definition INS (a : N) := elt_to_set a : set.
Coercion INS : N >-> set.

Definition zero := (exist PA1_ω) : N. (* PA1 : Zero is a natural. *)

Definition S : N → N. (* PA2 : The successor of a natural is a natural. *)
Proof.
  intros [n H].
  exact (exist (PA2_ω n H)).
Defined.

Notation "0" := zero : N_scope.
Definition one := S 0.
Notation "1" := one : N_scope.
Notation "2" := (S 1) : N_scope.

Theorem S_is_succ : ∀ n : N, succ n = S n.
Proof.
  now intros [n H].
Qed.

Theorem Induction : ∀ P : N → Prop,
    P 0 → (∀ n : N, P n → P (S n)) → ∀ n : N, P n.
Proof.
  intros P H H0 [n H1].
  induction n using Induction_ω; intuition.
  - rewrite <-(set_proj_injective ω 0); auto using set_proj_injective.
  - replace (exist H1 : N) with (S (exist H2 : N));
      eauto using set_proj_injective.
Qed.

Definition PA3 := Induction.

Theorem Strong_Induction_ω : ∀ P : N → Prop,
    (∀ n : N, (∀ k : N, k ∈ n → P k) → P n) → ∀ n : N, P n.
Proof.
  intros P H n.
  set (S := {x in ω | ∃ n : N, x = n ∧ ¬ P n}).
  assert (S ⊂ ω) as H0.
  { intros x H0.
    now apply Specify_classification in H0 as [H0 H1]. }
  destruct (classic (S = ∅)) as [H1 | H1].
  { apply NNPP.
    intros H2.
    contradict H1.
    apply Nonempty_classification.
    exists n.
    apply Specify_classification.
    eauto using elts_in_set. }
  apply ω_WOP in H1 as [s [H1 H2]]; auto.
  apply Specify_classification in H1 as [H1 [σ [H3 H4]]].
  subst.
  contradict H4.
  apply H.
  intros k H3.
  apply NNPP.
  intros H4.
  assert (k ∈ S) as H5.
  { apply Specify_classification.
    eauto using elts_in_set. }
  apply H2 in H5.
  contradiction (no_quines_ω k); eauto using elts_in_set.
Qed.

Theorem PA4 : ∀ n, 0 ≠ S n.
Proof.
  intros [n H] H0.
  inversion H0.
  now contradiction (PA4_ω n).
Qed.

Theorem succ_0 : ∀ n : N, n ≠ 0 ↔ ∃ m, n = S m.
Proof.
  intros n.
  induction n using Induction; split; intros H; eauto; try tauto.
  - destruct H as [m H].
    contradiction (PA4 m).
  - intros H0.
    now contradiction (PA4 n).
Qed.

Theorem PA5 : ∀ n m, S n = S m → n = m.
Proof.
  intros [n A] [m B] H.
  inversion H.
  now apply set_proj_injective, PA5_ω.
Qed.

Theorem PA5_iff : ∀ n m, S n = S m ↔ n = m.
Proof.
  intuition eauto using PA5; congruence.
Qed.

Theorem neq_succ : ∀ n, n ≠ S n.
Proof.
  induction n using Induction; intros H.
  - eapply PA4; eauto.
  - eauto using PA5.
Qed.

Section Iterated_op_construction.

  Context {X : Type}.
  Variable op : X → X → X.
  Variable start : X.
  Variable f : N → X.
  Infix "·" := op (at level 40, left associativity).

  Theorem iterated_op_construction : ∀ n : N, ∃ g : N → X,
        (g 0%N) = start ∧ ∀ m : N, m ∈ n → g (S m) = (g m) · (f m).
  Proof.
    induction n using Induction.
    - exists (λ x, start).
      split; auto.
      intros m H.
      contradict H.
      intros H.
      contradiction (Empty_set_classification m).
    - destruct IHn as [g [H H0]].
      exists (λ x, If x = S n then g n · f n else g x).
      split.
      { destruct excluded_middle_informative; auto.
        contradiction (PA4_ω n); eauto using elts_in_set.
        now rewrite -> S_is_succ, <-e. }
      intros m H1.
      repeat destruct excluded_middle_informative; subst;
        try now contradiction (no_quines_ω (S n)); eauto using elts_in_set.
      + apply PA5 in e.
        now subst.
      + apply H0.
        rewrite <-S_is_succ in H1.
        apply Pairwise_union_classification in H1 as [H1 | H1]; auto.
        apply Singleton_classification, set_proj_injective in H1.
        now subst.
  Qed.

  Definition iterated_op : N → X.
  Proof.
    intros n.
    destruct (constructive_indefinite_description
                (iterated_op_construction n)) as [i].
    exact (i n).
  Defined.

  Theorem iterated_op_0 : iterated_op 0 = start.
  Proof.
    unfold iterated_op.
    destruct constructive_indefinite_description.
    tauto.
  Qed.

  Theorem iterated_op_succ : ∀ n, iterated_op (S n) = (iterated_op n) · (f n).
  Proof.
    induction n using Strong_Induction_ω.
    unfold iterated_op at 1.
    destruct constructive_indefinite_description as [g], a as [H0 H1].
    rewrite <-? S_is_succ, ? H1 in *; auto using in_succ.
    f_equal.
    enough (∀ k : N, k ⊂ n → g k = iterated_op k); auto using Set_is_subset.
    induction k using Induction; intros H2; rewrite <-? S_is_succ in *.
    - now rewrite -> H0, iterated_op_0.
    - rewrite -> H1, H, IHk; try eapply Subset_transitive;
        eauto using in_succ, subset_succ, Set_is_subset, Subset_transitive.
  Qed.

End Iterated_op_construction.

Definition add a b := (iterated_op (λ x _, S x) a id b).

Infix "+" := add : N_scope.

Theorem add_0_r : ∀ x, x + 0 = x.
Proof.
  intros x.
  apply iterated_op_0.
Qed.

Theorem add_succ_r : ∀ x y, x + S y = S (x + y).
Proof.
  intros x y.
  apply @iterated_op_succ.
Qed.

Definition mul a b := (iterated_op add 0 (λ x, a) b).

Infix "*" := mul : N_scope.

Theorem mul_0_r : ∀ x, x * 0 = 0.
Proof.
  intros x.
  apply iterated_op_0.
Qed.

Theorem mul_succ_r : ∀ x y, x * (S y) = x * y + x.
Proof.
  intros x y.
  apply iterated_op_succ.
Qed.

Theorem add_1_r : ∀ a, a + 1 = S a.
Proof.
  intros a.
  unfold one.
  now rewrite -> add_succ_r, add_0_r.
Qed.

Theorem add_comm : ∀ a b, a + b = b + a.
Proof.
  induction a using Induction; induction b using Induction; auto.
  - now rewrite -> add_0_r, add_succ_r, IHb in *.
  - now rewrite -> add_0_r, add_succ_r, <-IHa, add_0_r.
  - now rewrite -> ? add_succ_r, IHb, <-? IHa, ? add_succ_r, IHa.
Qed.

Theorem add_assoc : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  induction c using Induction.
  - now rewrite ? add_0_r.
  - now rewrite -> ? add_succ_r, IHc.
Qed.

Theorem add_0_l : ∀ x, 0 + x = x.
Proof.
  intros x.
  now rewrite -> add_comm, add_0_r.
Qed.

Theorem cancellation_add : ∀ a b c, a + b = a + c → b = c.
Proof.
  induction a using Induction; intros b c H.
  - now rewrite -> ? add_0_l in *.
  - apply IHa, PA5.
    now rewrite -> ? (add_comm a), <-? add_succ_r, ? (add_comm _ (S a)).
Qed.

Theorem cancellation_0 : ∀ a b, a + b = a → b = 0.
Proof.
  intros a b H.
  rewrite <-(add_0_r a) in H at 2.
  eauto using cancellation_add.
Qed.

Theorem mul_1_r : ∀ a, a * 1 = a.
Proof.
  intros a.
  unfold one.
  now rewrite -> mul_succ_r, mul_0_r, add_0_l.
Qed.

Theorem mul_2_r : ∀ x, x * 2 = x + x.
Proof.
  intros x.
  now rewrite -> mul_succ_r, mul_1_r.
Qed.

Theorem mul_distr_r : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  induction c using Induction.
  - now rewrite -> ? mul_0_r, add_0_r.
  - now rewrite -> ? (mul_succ_r), IHc, ? add_assoc,
    <-(add_assoc (a*c)), (add_comm _ a), ? add_assoc.
Qed.

Theorem mul_comm : ∀ a b, a * b = b * a.
Proof.
  induction a using Induction; induction b using Induction; auto.
  - now rewrite -> mul_succ_r, IHb, ? mul_0_r, add_0_r.
  - now rewrite -> mul_succ_r, <-IHa, ? mul_0_r, add_0_r.
  - now rewrite -> ? mul_succ_r, ? IHb, <-? IHa, ? mul_succ_r,
    <-? add_assoc, ? add_succ_r, IHa, (add_comm a).
Qed.

Theorem mul_distr_l : ∀ a b c, a * (b + c) = a * b + a * c.
Proof.
  intros a b c.
  now rewrite -> mul_comm, mul_distr_r, ? (mul_comm a).
Qed.

Theorem mul_assoc : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  induction c using Induction.
  - now rewrite ? mul_0_r.
  - now rewrite -> ? (mul_succ_r), mul_distr_l, IHc.
Qed.

Theorem mul_0_l : ∀ a, 0 * a = 0.
Proof.
  intros a.
  now rewrite -> mul_comm, mul_0_r.
Qed.

Theorem mul_1_l : ∀ a, 1 * a = a.
Proof.
  intros a.
  now rewrite -> mul_comm, mul_1_r.
Qed.

Definition pow a b := (iterated_op mul 1 (λ x, a) b).

Infix "^" := pow : N_scope.

Theorem pow_0_r : ∀ x, x^0 = 1.
Proof.
  intros x.
  apply iterated_op_0.
Qed.

Theorem pow_succ_r : ∀ x y, x^(S y) = x^y * x.
Proof.
  intros x y.
  apply iterated_op_succ.
Qed.

Theorem pow_1_r : ∀ x, x^1 = x.
Proof.
  intros x.
  unfold one.
  now rewrite -> pow_succ_r, pow_0_r, mul_comm, mul_1_r.
Qed.

Theorem pow_0_l : ∀ x, x ≠ 0 → 0^x = 0.
Proof.
  intros x H.
  apply succ_0 in H as [m H].
  subst.
  now rewrite -> pow_succ_r, mul_0_r.
Qed.

Theorem pow_1_l : ∀ x, 1^x = 1.
Proof.
  induction x using Induction.
  - now rewrite pow_0_r.
  - now rewrite -> pow_succ_r, mul_1_r.
Qed.

Theorem pow_2_r : ∀ x, x^2 = x*x.
Proof.
  intros x.
  now rewrite -> pow_succ_r, pow_1_r.
Qed.

Theorem pow_add_r : ∀ a b c, a^(b+c) = a^b * a^c.
Proof.
  induction c using Induction.
  - now rewrite -> add_0_r, pow_0_r, mul_1_r.
  - now rewrite -> add_succ_r, ? pow_succ_r, IHc, mul_assoc.
Qed.

Theorem pow_mul_l : ∀ a b c, (a*b)^c = a^c * b^c.
Proof.
  induction c using Induction.
  - now rewrite -> ? pow_0_r, mul_1_r.
  - now rewrite -> ? pow_succ_r, <-? mul_assoc,
    (mul_assoc a), (mul_comm _ (b^c)), IHc, ? mul_assoc.
Qed.

Theorem pow_mul_r : ∀ a b c, a^(b*c) = (a^b)^c.
Proof.
  induction c using Induction.
  - now rewrite -> mul_0_r, ? pow_0_r.
  - now rewrite -> mul_succ_r, pow_succ_r, pow_add_r, IHc.
Qed.

Definition le a b := ∃ c, a + c = b.

Infix "≤" := le : N_scope.
Notation "a ≥ b" := (b ≤ a) (only parsing) : N_scope.

Definition lt a b := a ≤ b ∧ a ≠ b.

Infix "<" := lt : N_scope.
Notation "a > b" := (b < a) (only parsing) : N_scope.
Notation "a < b < c" := (a < b ∧ b < c) : N_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level): N_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level): N_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level): N_scope.

Theorem le_is_subset : ∀ a b, a ≤ b ↔ a ⊂ b.
Proof.
  intros a b.
  split; intros H.
  - destruct H as [c H].
    revert b H.
    induction c using Induction; intros b H; rewrite <-H.
    + rewrite add_0_r.
      auto using Set_is_subset.
    + eapply Subset_transitive; eauto.
      rewrite -> add_succ_r, <-S_is_succ.
      apply subset_succ.
  - induction b using Induction.
    + exists 0.
      rewrite add_0_r.
      apply set_proj_injective, Extensionality.
      split; intros H0; contradiction (Empty_set_classification z); eauto.
    + destruct (classic (b ∈ a)).
      * exists 0.
        rewrite add_0_r.
        apply set_proj_injective, Subset_equality_iff.
        split; auto.
        intros x H1.
        rewrite <-S_is_succ in H1.
        apply Pairwise_union_classification in H1 as [H1 | H1];
          try now (rewrite -> Singleton_classification in *; subst).
        eapply elements_of_naturals_are_subsets; eauto using elts_in_set.
      * destruct IHb as [x H1].
        { move: H => /[swap] => x /[swap] /[dup] => H => /[swap] /[apply].
          rewrite -S_is_succ /succ Pairwise_union_classification.
          rewrite Singleton_classification; elim => ?; subst; tauto. }
        exists (S x).
        now rewrite -> add_succ_r, H1.
Qed.

Theorem lt_is_in : ∀ a b, a < b ↔ a ∈ b.
  intros a b.
  split; intros H; unfold lt in *; rewrite -> le_is_subset in *.
  - destruct H as [H H0].
    eapply subsets_of_naturals_are_elements; eauto using elts_in_set.
    contradict H0.
    now apply set_proj_injective.
  - split.
    + apply elements_of_naturals_are_subsets; eauto using elts_in_set.
    + apply pigeonhole_precursor in H; eauto using elts_in_set.
      contradict H.
      subst.
      auto using Set_is_subset.
Qed.

Theorem lt_is_subsetneq : ∀ a b, a < b ↔ a ⊊ b.
Proof.
  split; intros [H H0].
  - rewrite -> le_is_subset in H.
    split; auto.
    contradict H0.
    now apply set_proj_injective.
  - split; try congruence.
    now apply le_is_subset.
Qed.

Theorem le_trichotomy : ∀ a b, a ≤ b ∨ b ≤ a.
Proof.
  intros a b.
  rewrite ? le_is_subset.
  apply ω_trichotomy; eauto using elts_in_set.
Qed.

Theorem lt_trichotomy : ∀ a b, a < b ∨ a = b ∨ a > b.
Proof.
  intros a b.
  pose proof le_trichotomy a b.
  pose proof (classic (a = b)).
  unfold lt.
  intuition.
Qed.

Theorem le_antisymm : ∀ a b, a ≤ b → b ≤ a → a = b.
Proof.
  intros a b H H0.
  rewrite -> ? le_is_subset in *.
  now apply set_proj_injective, Subset_equality_iff.
Qed.

Theorem lt_antisym : ∀ a b, a < b → ¬ b < a.
Proof.
  intros a b H H0.
  rewrite -> ? lt_is_in in *.
  eapply ω_irreflexive; eauto using elts_in_set.
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
  apply le_is_subset, Set_is_subset.
Qed.

Add Ring N_semiring :
  (mk_srt 0 1 add mul eq add_0_l add_comm add_assoc
          mul_1_l mul_0_l mul_comm mul_assoc mul_distr_r).

Theorem lt_def : ∀ a b, a < b ↔ ∃ c : N, 0 ≠ c ∧ a + c = b.
Proof.
  unfold lt; split; intros [x H].
  - destruct x as [c H0].
    exists c.
    split; auto.
    contradict H.
    subst.
    ring.
  - destruct H as [H H0].
    split.
    + now (exists x).
    + contradict H.
      subst.
      eauto using eq_sym, cancellation_0.
Qed.

Theorem cancellation_0_add : ∀ a b, a + b = 0 → a = 0 ∧ b = 0.
Proof.
  intros a b H.
  induction a using Induction; induction b using Induction;
    rewrite -> ? add_0_l, ? add_0_r in *; try tauto.
  rewrite -> add_succ_r in *.
  now contradiction (PA4 (S a + b)).
Qed.

Theorem cancellation_1_add : ∀ a b, a + b = 1 → a = 0 ∨ b = 0.
Proof.
  intros a b H.
  induction a using Induction; induction b using Induction; auto.
  rewrite add_succ_r in H.
  apply PA5 in H.
  rewrite -> add_comm, add_succ_r in H.
  now contradiction (PA4 (b+a)).
Qed.

Theorem cancellation_0_mul : ∀ a b, a * b = 0 → a = 0 ∨ b = 0.
Proof.
  induction a using Induction; induction b using Induction; auto.
  intros H.
  rewrite -> mul_succ_r, add_succ_r in H.
  now contradiction (PA4 (S a * b + a)).
Qed.

Theorem mul_lt_r : ∀ a b c, a ≠ 0 → b < c → a * b < a * c.
Proof.
  intros a b c H H0.
  rewrite -> lt_def in *.
  destruct H0 as [n [H0 H1]].
  exists (a*n).
  split.
  - contradict H.
    apply eq_sym, cancellation_0_mul in H as [H | H]; auto; now contradict H0.
  - subst; ring.
Qed.

Theorem mul_le_r : ∀ a b c, a ≤ b → a * c ≤ b * c.
Proof.
  intros a b c [n H].
  exists (n*c).
  subst; ring.
Qed.

Theorem cancellation_mul : ∀ a b c : N, c ≠ 0 → a * c = b * c → a = b.
Proof.
  intros a b c H H0.
  destruct (lt_trichotomy a b) as [H1 | [H1 | H1]]; auto;
    eapply mul_lt_r in H1; eauto; rewrite -> ? (mul_comm c), H0 in H1;
      exfalso; eapply lt_irrefl; eauto.
Qed.

Theorem trichotomy : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ (a > b)) ∨
                            (¬ (a < b) ∧ a = b ∧ ¬ (a > b)) ∨
                            (¬ (a < b) ∧ a ≠ b ∧ a > b).
Proof.
  intros a b.
  destruct (lt_trichotomy a b) as [H | [H | H]], (classic (a = b));
    try subst; auto using lt_antisym, lt_irrefl; congruence.
Qed.

Theorem lt_trans : ∀ a b c, a < b → b < c → a < c.
Proof.
  intros a b c H H0.
  rewrite -> lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  exists (x+y).
  split.
  - intros H3.
    apply eq_sym, cancellation_0_add in H3 as [H3 H4].
    now subst.
  - subst; ring.
Qed.

Theorem O1 : ∀ {a b} c, a < b → a + c < b + c.
Proof.
  intros a b c H.
  rewrite -> lt_def in *.
  destruct H as [x [H H0]].
  exists x.
  split; auto.
  subst; ring.
Qed.

Theorem O1_iff : ∀ {a b} c, a < b ↔ a + c < b + c.
Proof.
  intros a b c.
  split; intros H; auto using O1.
  rewrite -> lt_def in *.
  destruct H as [x [H H0]].
  exists x.
  split; auto.
  apply (cancellation_add c).
  rewrite -> (add_comm _ b), <-H0.
  ring.
Qed.

Theorem O1_le : ∀ {a b} c, a ≤ b → a + c ≤ b + c.
Proof.
  intros a b c [x H].
  exists x.
  subst; ring.
Qed.

Theorem O1_le_iff : ∀ {a b} c, a ≤ b ↔ a + c ≤ b + c.
Proof.
  intros a b c.
  split; intros H; auto using O1_le.
  destruct H as [x H].
  exists x.
  apply (cancellation_add c).
  rewrite -> (add_comm _ b), <-H.
  ring.
Qed.

Theorem lt_add : ∀ a b, 0 < a → 0 < b → 0 < a + b.
Proof.
  intros a b H H0.
  rewrite <-(add_0_l b) in H0.
  eauto using lt_trans, O1.
Qed.

Theorem O2 : ∀ a b, 0 < a → 0 < b → 0 < a * b.
Proof.
  intros a b H H0.
  rewrite -> lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  exists (x*y).
  rewrite -> add_0_l in *.
  subst.
  split; auto.
  intros H1.
  apply eq_sym, cancellation_0_mul in H1 as [H1 | H1]; congruence.
Qed.

Theorem O3 : ∀ {a b} c, a < b → 0 < c → a * c < b * c.
Proof.
  intros a b c H H0.
  rewrite -> lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  rewrite -> add_0_l in *.
  subst.
  exists (x*c).
  split; try ring.
  intros H1.
  apply eq_sym, cancellation_0_mul in H1 as [H1 | H1]; congruence.
Qed.

Theorem lt_0_1 : ∀ a, ¬ 0 < a < 1.
Proof.
  induction a using Induction; intros [H H0].
  - eapply lt_irrefl; eauto.
  - rewrite -> lt_def in *.
    destruct H0 as [c [H0 H1]].
    rewrite -> add_comm, add_succ_r, neq_sym in *.
    now apply PA5, cancellation_0_add in H1 as [H1 H2].
Qed.

Theorem lt_succ : ∀ m, 0 < S m.
Proof.
  intros m.
  rewrite lt_def.
  exists (S m).
  split; auto using PA4; ring.
Qed.

Theorem nonzero_lt : ∀ m, m ≠ 0 ↔ 0 < m.
Proof.
  split; intros H.
  - apply succ_0 in H as [k H]; subst.
    apply lt_succ.
  - intros H0.
    subst.
    contradiction (lt_irrefl 0).
Qed.

Theorem succ_lt : ∀ m, m < S m.
Proof.
  intros m.
  rewrite lt_def.
  exists 1.
  unfold one.
  split; auto using PA4, add_1_r.
Qed.

Theorem S_lt : ∀ m n, m < n ↔ S m < S n.
Proof.
  split; intros H.
  - rewrite <-? (add_1_r m), <-? (add_1_r n).
    now apply O1.
  - apply lt_def in H as [c [H H0]].
    rewrite -> add_comm, add_succ_r, add_comm in H0.
    apply lt_def.
    eauto using PA5.
Qed.

Theorem zero_le : ∀ n, 0 ≤ n.
Proof.
  intros n.
  apply le_is_subset, Empty_set_is_subset.
Qed.

Theorem lt_not_ge : ∀ a b, a < b ↔ ¬ b ≤ a.
Proof.
  split; intros H.
  - destruct H as [H H0].
    contradict H0.
    now apply le_antisymm.
  - destruct (lt_trichotomy b a) as [[H0 H1] | [H0 | H0]]; try tauto.
    contradict H.
    subst.
    apply le_refl.
Qed.

Theorem le_not_gt : ∀ a b, a ≤ b ↔ ¬ b < a.
Proof.
  split; intros H.
  - intros [H0 H1].
    contradict H1.
    now apply le_antisymm.
  - apply NNPP.
    intros H0.
    now rewrite <-lt_not_ge in H0.
Qed.

Theorem lt_1_eq_0 : ∀ n, n < 1 → n = 0.
Proof.
  intros n H.
  induction n as [| n _ ] using Induction; auto.
  apply le_not_gt in H; intuition.
  exists n.
  rewrite <-add_1_r; ring.
Qed.

Definition pred (n : N) := (exist (union_ω (elts_in_set n)) : N).

Definition sub a b := (iterated_op (λ x _, pred x) a id b).

Infix "-" := sub : N_scope.

Theorem pred_0 : pred 0 = 0.
Proof.
  apply set_proj_injective; simpl.
  apply Empty_union.
Qed.

Theorem pred_succ : ∀ a, pred (S a) = a.
Proof.
  intros a.
  apply set_proj_injective; simpl.
  rewrite <-S_is_succ, union_succ; eauto using elts_in_set.
Qed.

Theorem sub_0_r : ∀ a, a - 0 = a.
Proof.
  intros a.
  unfold sub.
  now rewrite iterated_op_0.
Qed.

Theorem sub_0_l : ∀ a, 0 - a = 0.
Proof.
  induction a using Induction; unfold sub in *.
  - now rewrite iterated_op_0.
  - now rewrite -> iterated_op_succ, IHa, pred_0.
Qed.

Theorem sub_succ_r : ∀ a b, a - S b = pred (a - b).
Proof.
  induction b using Induction; unfold sub;
    now rewrite -> iterated_op_succ, ? iterated_op_0.
Qed.

Theorem sub_succ : ∀ a b, S a - S b = a - b.
Proof.
  induction b using Induction.
  - now rewrite -> sub_succ_r, ? sub_0_r, pred_succ.
  - now rewrite -> sub_succ_r, IHb, sub_succ_r.
Qed.

Theorem sub_abba : ∀ a b, a + b - b = a.
Proof.
  induction b using Induction.
  - now rewrite -> add_0_r, sub_0_r.
  - now rewrite -> add_succ_r, sub_succ.
Qed.

Theorem sub_diag : ∀ a, a - a = 0.
Proof.
  intros a.
  now rewrite <-(add_0_l a), sub_abba at 1.
Qed.

Theorem sub_spec : ∀ a b c, a + c = b → c = b - a.
Proof.
  intros a b c H.
  now rewrite <-H, add_comm, sub_abba.
Qed.

Theorem sub_0_le : ∀ a b, a - b = 0 → a ≤ b.
Proof.
  intros a b H.
  destruct (le_trichotomy a b) as [H0 | [c H0]]; auto.
  apply sub_spec in H0 as H1.
  rewrite <-H0, H1, H, add_0_r.
  apply le_refl.
Qed.

Theorem sub_abab : ∀ a b, a ≤ b → a + (b - a) = b.
Proof.
  intros a b [c H].
  subst.
  now rewrite -> (add_comm _ c), sub_abba, add_comm.
Qed.

Theorem sub_ne_0_lt : ∀ a b, a - b ≠ 0 → b < a.
Proof.
  intros a b H.
  apply lt_not_ge.
  contradict H.
  destruct H as [c H].
  subst.
  induction c using Induction.
  - now rewrite -> add_0_r, <-(add_0_l a), sub_abba at 1.
  - now rewrite -> add_succ_r, sub_succ_r, IHc, pred_0.
Qed.

Definition min : N → N → N.
Proof.
  intros a b.
  destruct (excluded_middle_informative (a < b)).
  - exact a.
  - exact b.
Defined.

Theorem min_le_l : ∀ a b, min a b ≤ a.
Proof.
  intros a b.
  unfold min.
  destruct excluded_middle_informative.
  - apply le_refl.
  - now rewrite <-le_not_gt in n.
Qed.

Theorem min_le_r : ∀ a b, min a b ≤ b.
Proof.
  intros a b.
  unfold min.
  destruct excluded_middle_informative.
  - now destruct l.
  - apply le_refl.
Qed.

Theorem min_eq : ∀ a b, min a b = a ∨ min a b = b.
Proof.
  intros a b.
  unfold min.
  destruct excluded_middle_informative; intuition.
Qed.

Definition max : N → N → N.
Proof.
  intros a b.
  destruct (excluded_middle_informative (a < b)).
  - exact b.
  - exact a.
Defined.

Theorem max_le_l : ∀ a b, a ≤ max a b.
Proof.
  intros a b.
  unfold max.
  destruct excluded_middle_informative.
  - now destruct l.
  - apply le_refl.
Qed.

Theorem max_le_r : ∀ a b, b ≤ max a b.
Proof.
  intros a b.
  unfold max.
  destruct excluded_middle_informative.
  - apply le_refl.
  - now rewrite <-le_not_gt in n.
Qed.

Theorem max_eq : ∀ a b, max a b = a ∨ max a b = b.
Proof.
  intros a b.
  unfold max.
  destruct excluded_middle_informative; intuition.
Qed.

Theorem max_sym : ∀ a b, max a b = max b a.
Proof.
  intros a b.
  unfold max.
  repeat destruct excluded_middle_informative; auto.
  - contradiction (lt_antisym a b).
  - rewrite <-le_not_gt in *.
    auto using le_antisymm.
Qed.

Theorem max_0_l : ∀ a, max 0 a = a.
Proof.
  intros a.
  unfold max.
  destruct excluded_middle_informative; auto.
  apply NNPP.
  contradict n.
  apply neq_sym, succ_0 in n as [m H].
  subst.
  auto using lt_succ.
Qed.

Theorem max_0_r : ∀ a, max a 0 = a.
Proof.
  intros a.
  now rewrite -> max_sym, max_0_l.
Qed.

Theorem le_trans : ∀ a b c, a ≤ b → b ≤ c → a ≤ c.
Proof.
  intros a b c [d H] [e H0].
  exists (d + e).
  subst; ring.
Qed.

Theorem le_lt_trans : ∀ a b c, a ≤ b → b < c → a < c.
Proof.
  intros a b c [d H] [[e H0] H1].
  rewrite lt_def.
  exists (d + e).
  split.
  - intros H2.
    apply eq_sym, cancellation_0_add in H2 as [H2 H3].
    subst.
    now rewrite -> ? add_0_r in *.
  - subst; ring.
Qed.

Theorem lt_le_trans : ∀ a b c, a < b → b ≤ c → a < c.
Proof.
  intros a b c [[d H] H0] [e H1].
  rewrite lt_def.
  exists (d + e).
  split.
  - intros H2.
    apply eq_sym, cancellation_0_add in H2 as [H2 H3].
    subst.
    now rewrite -> ? add_0_r in *.
  - subst; ring.
Qed.

Theorem lt_cross_add : ∀ a b c d, a < b → c < d → a + c < b + d.
Proof.
  intros a b c d H H0.
  apply (O1 c) in H.
  apply (O1 b) in H0.
  rewrite ? (add_comm _ b) in H0.
  eauto using lt_trans.
Qed.

Theorem le_cross_add : ∀ a b c d, a ≤ b → c ≤ d → a + c ≤ b + d.
Proof.
  intros a b c d [e H] [f H0].
  exists (e + f).
  subst; ring.
Qed.

Theorem lub : ∀ P, (∃ n : N, P n) → (∃ m : N, ∀ n : N, P n → n ≤ m)
                   → ∃ s : N, P s ∧ ∀ n : N, P n → n ≤ s.
Proof.
  intros P H [m H0].
  revert P H H0.
  induction m using Induction; intros P [x H] H0.
  - replace x with 0 in H; eauto using le_antisymm, zero_le.
  - destruct (classic (P (S m))) as [H1 | H1]; eauto.
    destruct (IHm P) as [s [H2 H3]]; eauto.
    intros n H2.
    apply NNPP.
    intros H3.
    apply lt_not_ge in H3.
    pose proof H2 as H4.
    apply H0 in H4 as [c H4].
    destruct (classic (c = 0)) as [H5 | H5]; subst.
    + rewrite add_0_r in H4.
      now subst.
    + apply succ_0 in H5 as [d H5].
      subst.
      rewrite add_succ_r in H4.
      apply PA5 in H4.
      subst.
      apply le_not_gt in H3; auto.
      now (exists d).
Qed.

Theorem squeeze_upper : ∀ n m, n < m → m ≤ S n → m = S n.
Proof.
  intros n m H [c H0].
  replace c with 0 in H0; try ring [H0].
  apply NNPP.
  intros H1.
  apply neq_sym, succ_0 in H1 as [d H1].
  subst.
  rewrite add_succ_r in H0.
  apply PA5 in H0.
  subst.
  contradiction (lt_irrefl m).
  eapply le_lt_trans; eauto.
  now exists d.
Qed.

Theorem squeeze_lower : ∀ n m, n ≤ m → m < S n → m = n.
Proof.
  intros n m [c H] H0.
  replace c with 0 in H; try ring [H].
  apply NNPP.
  intros H1.
  apply neq_sym, succ_0 in H1 as [d H1].
  subst.
  rewrite -> add_succ_r, <-S_lt in H0.
  contradiction (lt_irrefl n).
  eapply le_lt_trans; eauto.
  now exists d.
Qed.

Theorem succ_le : ∀ a b, a ≤ b ↔ S a ≤ S b.
Proof.
  split; intros [c H]; exists c; subst; [ | apply PA5 ];
    now rewrite -> add_comm, add_succ_r, add_comm in *.
Qed.

Theorem le_lt_succ : ∀ n m, m ≤ n ↔ m < S n.
Proof.
  split; rewrite lt_def; intros [c H].
  - exists (S c).
    rewrite add_succ_r.
    split; auto using PA4; congruence.
  - destruct H as [H H0].
    apply neq_sym, succ_0 in H as [d H].
    subst.
    exists d.
    rewrite add_succ_r in H0.
    now apply PA5.
Qed.

Theorem lt_le_succ : ∀ n m, m < n ↔ S m ≤ n.
Proof.
  split; rewrite lt_def; intros [c H].
  - destruct H as [H H0].
    apply neq_sym, succ_0 in H as [d H].
    subst.
    exists d.
    now rewrite -> add_comm, ? add_succ_r, add_comm.
  - exists (S c).
    split; auto using PA4.
    now rewrite <-H, (add_comm _ c), ? add_succ_r, add_comm.
Qed.

Theorem no_quines : ∀ n : N, n ∉ n.
Proof.
  eauto using no_quines_ω, elts_in_set.
Qed.

Theorem disjoint_succ : ∀ n : N, n ∩ {n,n} = ∅.
Proof.
  intros n.
  apply Extensionality.
  split; intros H.
  - apply Pairwise_intersection_classification in H as [H H0].
    apply Singleton_classification in H0.
    subst.
    contradiction (no_quines n).
  - contradiction (Empty_set_classification z).
Qed.

Theorem le_lt_or_eq : ∀ a b, a ≤ b ↔ a < b ∨ a = b.
Proof.
  split; intros H; unfold lt in *.
  - destruct (classic (a = b)); tauto.
  - destruct H as [[H H0] | H]; subst; auto using le_refl.
Qed.

Theorem le_succ : ∀ n, n ≤ S n.
Proof.
  intros n.
  exists 1.
  now rewrite add_1_r.
Qed.

Theorem one_le_succ : ∀ n, 1 ≤ S n.
Proof.
  intros n.
  exists n.
  now rewrite -> add_comm, add_1_r.
Qed.

Theorem Strong_Induction : ∀ P : N → Prop,
    (∀ n : N, (∀ k : N, k < n → P k) → P n) → ∀ n : N, P n.
Proof.
  intros P H n.
  apply Strong_Induction_ω.
  intros n0 H0.
  apply H.
  intros k H1.
  now apply H0, lt_is_in.
Qed.

Theorem not_succ_le : ∀ n, ¬ S n ≤ n.
Proof.
  intros n H.
  apply le_not_gt in H.
  eauto using succ_lt.
Qed.

Theorem WOP : ∀ P, (∃ n : N, P n) → ∃ m : N, P m ∧ (∀ k : N, P k → m ≤ k).
Proof.
  intros P [n H].
  destruct (ω_WOP {x of type ω | P x}) as [x [H0 H1]].
  - apply Nonempty_classification.
    exists n.
    apply Specify_classification.
    rewrite despecify.
    eauto using elts_in_set.
  - intros x H0.
    now apply Specify_classification in H0.
  - apply Specify_classification in H0 as [H0 H2].
    rewrite -> (reify H0), despecify in H2.
    exists (exist H0 : N).
    split; auto.
    intros k H3.
    apply le_is_subset, H1, Specify_classification.
    rewrite despecify.
    eauto using elts_in_set.
Qed.

Theorem lt_0_le_1 : ∀ n, 0 < n ↔ 1 ≤ n.
Proof.
  split; intros H.
  - apply nonzero_lt, succ_0 in H as [m H]; subst; apply one_le_succ.
  - apply nonzero_lt, succ_0.
    destruct H as [m H].
    exists m.
    now rewrite <-add_1_r, add_comm, H.
Qed.
