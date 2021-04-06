Require Export sets Ring.

Theorem Infinity_ω: ∃ X, ∅ ∈ X ∧ Inductive X.
Proof.
  move: Infinity => [X [[e [H H0]] H1]].
  exists X.
  rewrite /Inductive /succ.
  split => [ | y /H1 [Y [H2 H3]]].
  - suff -> : ∅ = e => //.
    apply Subset_equality_iff;
      intuition eauto using Empty_set_is_subset => x /H //.
  - suff -> : y ∪ {y,y} = Y => //.
    apply Extensionality => z.
    rewrite H3 Pairwise_union_classification Singleton_classification //.
Qed.

Definition ω : set.
Proof.
  elim (constructive_indefinite_description Infinity_ω) => [X H].
  exact (⋂ {x in P X | ∅ ∈ x ∧ Inductive x}).
Defined.

Theorem PA1_ω : ∅ ∈ ω.
Proof.
  rewrite /ω.
  elim constructive_indefinite_description => X [H H0] /=.
  rewrite Intersection_classification ? Specify_classification
          ? Union_classification => [_ /Specify_classification [_ []] | ] //.
  eapply Nonempty_classification, ex_intro, Specify_classification.
  eauto using Set_in_powerset.
Qed.

Theorem PA2_ω : Inductive ω.
Proof.
  rewrite /ω.
  elim constructive_indefinite_description => /= => x [H H0] y.
  rewrite ? Intersection_classification;
    try eapply Nonempty_classification, ex_intro, Specify_classification;
    eauto using Set_in_powerset.
  move=> H1 X /[dup] /H1 /[swap] /Specify_classification [H2] [H3] /[apply] //.
Qed.

Theorem ω_is_minimal : ∀ s, s ⊂ ω → ∅ ∈ s → Inductive s → ω ⊂ s.
Proof.
  rewrite /ω => s.
  elim constructive_indefinite_description => /= =>
  X [H H0] H1 /[dup] H2 /H1 H3 H4 x /Intersection_classification H5.
  apply H5, Specify_classification, conj; auto.
  - eapply Nonempty_classification, ex_intro, Specify_classification;
      eauto using Set_in_powerset.
  - apply Powerset_classification => y /H1 /Intersection_classification H6.
    apply H6.
    + eapply Nonempty_classification, ex_intro, Specify_classification;
        eauto using Set_in_powerset.
    + apply Specify_classification; eauto using Set_in_powerset.
Qed.

Theorem PA3_ω : ∀ s, s ⊂ ω → ∅ ∈ s → Inductive s → s = ω.
Proof.
  auto using Subset_equality, ω_is_minimal.
Qed.

Theorem PA4_ω : ∀ n, n ∈ ω → succ n ≠ ∅.
Proof.
  move=> n H.
  apply /Nonempty_classification /ex_intro /in_succ.
Qed.

Theorem Induction_ω : ∀ P : set → Prop,
    (∀ n, n ∉ ω → P n) → P ∅ → (∀ m, m ∈ ω → P m → P (succ m)) → ∀ n, P n.
Proof.
  move=> P H H0 H1 n.
  elim (classic (n ∈ ω)); auto.
  suff <- : {x in ω | P x} = ω => [/Specify_classification [] | ] //.
  apply /PA3_ω =>
  [y /Specify_classification [] | | y /Specify_classification]
    //; rewrite Specify_classification; intuition auto using PA1_ω, PA2_ω.
Qed.

Theorem elements_of_naturals_are_naturals : ∀ n m, n ∈ ω → m ∈ n → m ∈ ω.
Proof.
  elim/Induction_ω => [* | _ _ /Empty_set_classification |
                       ? H H0 ? ? /Pairwise_union_classification
                         [ /(H0 _ H) | /Singleton_classification ->] ] //.
Qed.

Lemma pigeonhole_precursor : ∀ n m, n ∈ ω → m ∈ n → ¬ n ⊂ m.
Proof.
  elim /Induction_ω =>
  [* | _ _ /Empty_set_classification |
   n H H0 m ? /Pairwise_union_classification
     [/(H0 _ H) | /Singleton_classification ->]]
    //; intuition eauto using Subset_transitive,
  subset_succ, Set_is_subset, in_succ.
Qed.

Theorem no_quines_ω : ∀ n, n ∈ ω → ¬ n ∈ n.
Proof.
  move=> n /[swap] /pigeonhole_precursor /[apply].
  eauto using Set_is_subset.
Qed.

Lemma elements_of_naturals_are_subsets : ∀ n m, n ∈ ω → m ∈ n → m ⊂ n.
Proof.
  elim/Induction_ω =>
  [* | _ _ /Empty_set_classification |
   n H H0 m H1 /Pairwise_union_classification
     [/(H0 _ H) | /Singleton_classification -> ]]
    //; eauto using Subset_transitive, subset_succ.
Qed.

Lemma ω_is_transitive : ∀ x y z,
    x ∈ ω → y ∈ ω → z ∈ ω → x ∈ y → y ∈ z → x ∈ z.
Proof.
  move=> x y z H H0 /[swap] H1 /[swap] /elements_of_naturals_are_subsets
           /(_ _ H1) /[apply] //.
Qed.

Lemma subsets_of_naturals_are_elements :
  ∀ n m, n ∈ ω → m ∈ ω → m ⊂ n → m ≠ n → m ∈ n.
Proof.
  elim/Induction_ω => [* | m H H0 /[swap] /Nonempty_classification [x] /[swap]
                             /[apply] /Empty_set_classification |
                       n H H0 m] //; elim (classic (m = n)) =>
  [-> | H1 H2 H3 H4 H5]; try apply subset_succ, H0; eauto using in_succ =>
  x /[dup] /H4 /Pairwise_union_classification
    [H7 | /Singleton_classification ->] H6 //; contradict H5.
  apply Subset_equality_iff, conj; auto =>
  y /Pairwise_union_classification [ | /Singleton_classification ->] //.
  move: H6 H3 => /elements_of_naturals_are_subsets /[apply] /[apply] //.
Qed.

Lemma ω_trichotomy : ∀ n m, n ∈ ω → m ∈ ω → m ⊂ n ∨ n ⊂ m.
Proof.
  elim/Induction_ω =>
  [ | | n ? H m ? /[dup] ? /H ] //; intuition eauto using Empty_set_is_subset,
  Subset_transitive, subset_succ.
  elim (classic (n = m)) => [-> | /[dup] ? /subsets_of_naturals_are_elements];
                              intuition eauto using subset_succ.
  right => x /Pairwise_union_classification [ | /Singleton_classification ->];
             eauto using ω_is_transitive.
Qed.

Lemma ω_irreflexive : ∀ n m, n ∈ ω → m ∈ ω → ¬ (n ∈ m ∧ m ∈ n).
Proof.
  move=> n m H H0 [/(elements_of_naturals_are_subsets _ _ H0) H1 H2].
  apply /pigeonhole_precursor; eauto using Set_is_subset.
Qed.

Theorem union_succ : ∀ n, n ∈ ω → ⋃ succ n = n.
Proof.
  rewrite /succ => n H.
  apply Extensionality => z.
  split; rewrite Union_classification; eauto using in_succ =>
  [[x [/Pairwise_union_classification [ | /Singleton_classification ->]]]] //.
  intuition eauto using ω_is_transitive, elements_of_naturals_are_naturals.
Qed.

Theorem union_ω : ∀ {n}, n ∈ ω → ⋃ n ∈ ω.
Proof.
  elim/Induction_ω => [ | | m H]; rewrite ? Empty_union ? union_succ //.
Qed.

Theorem PA5_ω : ∀ n m, n ∈ ω → m ∈ ω → succ n = succ m → n = m.
Proof.
  move=> n m H H0 H1.
  rewrite -(union_succ m) // -(union_succ n) // H1 //.
Qed.

Theorem ω_WOP : ∀ X, X ≠ ∅ → X ⊂ ω → ∃ x, x ∈ X ∧ ∀ y, y ∈ X → x ⊂ y.
Proof.
  move=> X /Nonempty_classification [x H] H0.
  have H1: x ∈ ω by eauto.
  elim/Induction_ω: x X H0 H H1; intuition eauto using Empty_set_is_subset.
  elim (classic (m ∈ X)) => [H4 | H4]; auto.
  (elim (H0 (X ∪ {m,m}));
   rewrite ? Pairwise_union_classification ? Singleton_classification; auto)
  => [x [/Pairwise_union_classification
          [? | /Singleton_classification ->]] H5 | y].
  - eapply ex_intro, conj; eauto => y ?.
    apply /H5 /Pairwise_union_classification; eauto.
  - exists (m ∪ {m,m}).
    split; auto => y ? z /Pairwise_union_classification
                     [/(H5 y) | /Singleton_classification ->].
    + rewrite Pairwise_union_classification Singleton_classification; tauto.
    + apply subsets_of_naturals_are_elements; eauto.
      apply /H5 /Pairwise_union_classification /or_introl => //.
      congruence.
  - rewrite Pairwise_union_classification Singleton_classification
    => [[/H1 | ->]] //.
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
  move=> [n H].
  exact (exist (PA2_ω n H)).
Defined.

Notation "0" := zero : N_scope.
Definition one := S 0.
Notation "1" := one : N_scope.
Notation "2" := (S 1) : N_scope.

Theorem S_is_succ : ∀ n : N, succ n = S n.
Proof.
  move=> [n H] //.
Qed.

Theorem in_S_succ : ∀ (n : N) (x : set), x ∈ succ n ↔ x ∈ S n.
Proof.
  move=> n m.
  rewrite S_is_succ //.
Qed.

Theorem subset_S : ∀ n : N, n ⊂ S n.
Proof.
  move=> n.
  rewrite -S_is_succ.
  apply subset_succ.
Qed.

Theorem in_S : ∀ n : N, n ∈ S n.
Proof.
  move=> n.
  apply in_S_succ, in_succ.
Qed.

Theorem Induction : ∀ P : N → Prop,
    P 0 → (∀ n : N, P n → P (S n)) → ∀ n : N, P n.
Proof.
  move=> P H H0 [n H1]; elim/Induction_ω: n H1 =>
  [* | H1 | m H1 /(_ H1) /H0 H2 H3] //; erewrite <-set_proj_injective; eauto.
Qed.

Definition PA3 := Induction.

Theorem Strong_Induction_ω : ∀ P : N → Prop,
    (∀ n : N, (∀ k : N, k ∈ n → P k) → P n) → ∀ n : N, P n.
Proof.
  move=> P H n.
  have: {x of type ω | ¬ P x} ⊂ ω by move=> x /Specify_classification [H0] //.
  elim (classic ({x of type ω | ¬ P x} = ∅)) =>
  [H0 H1 | /[swap] /ω_WOP /[apply] [[x [/Specify_classification [H0]]]]].
  - apply NNPP.
    move: H0 => /[swap] H0.
    eapply Nonempty_classification, ex_intro, Specify_classification.
    erewrite despecify.
    eauto using elts_in_set.
  - rewrite (reify H0) despecify => H1 H2.
    contradict H1.
    apply /H => k H1.
    apply NNPP => H3.
    contradiction (no_quines_ω k); eauto using elts_in_set.
    apply /H2; eauto.
    apply Specify_classification.
    erewrite despecify.
    eauto using elts_in_set.
Qed.

Theorem PA4 : ∀ n, 0 ≠ S n.
Proof.
  move=> [n H] H0.
  inversion H0.
  contradiction (PA4_ω n) => //.
Qed.

Theorem succ_0 : ∀ n : N, n ≠ 0 ↔ ∃ m, n = S m.
Proof.
  (elim/Induction; split; try now intuition eauto) => [[x /PA4] | H0] //.
  apply /neq_sym /PA4.
Qed.

Theorem PA5 : ∀ n m, S n = S m → n = m.
Proof.
  move=> [n A] [m B] H.
  inversion H.
  apply /set_proj_injective /PA5_ω => //.
Qed.

Theorem PA5_iff : ∀ n m, S n = S m ↔ n = m.
Proof.
  intuition eauto using PA5; congruence.
Qed.

Theorem neq_succ : ∀ n, n ≠ S n.
Proof.
  elim/Induction => [/PA4 | ] //.
  eauto using PA5.
Qed.

Theorem no_quines : ∀ n : N, n ∉ n.
Proof.
  eauto using no_quines_ω, elts_in_set.
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
    elim/Induction => [| n [g [H H0]]].
    - exists (λ x, start).
      split; auto => m /Empty_set_classification //.
    - (exists (λ x, If x = S n then g n · f n else g x);
              split => [| m]; repeat elim excluded_middle_informative; eauto) =>
      [/PA4 | -> _ /no_quines | _ /PA5 -> | -> _ /no_quines |
       H1 /[swap] /in_S_succ /Pairwise_union_classification
          [/H0 | /Singleton_classification /set_proj_injective ->]] //.
  Qed.

  Definition iterated_op : N → X.
  Proof.
    move=> n.
    elim (constructive_indefinite_description (iterated_op_construction n))
    => [i H].
    exact (i n).
  Defined.

  Theorem iterated_op_0 : iterated_op 0 = start.
  Proof.
    rewrite /iterated_op.
    elim constructive_indefinite_description => x [H H0] /= //.
  Qed.

  Theorem iterated_op_succ : ∀ n, iterated_op (S n) = (iterated_op n) · (f n).
  Proof.
    elim/Strong_Induction_ω.
    rewrite {3}/iterated_op /sig_rect => n /= H.
    elim constructive_indefinite_description =>
    g [H0 /[dup] H1 ->]; auto using in_S.
    f_equal.
    have: ∀ k : N, k ⊂ n → g k = iterated_op k; auto using Set_is_subset.
    elim/Induction =>
    [H2 | m /[swap] /[dup] H2 H3 H4]; rewrite ? iterated_op_0 ? H1 ? H4 ? H;
      try eapply Subset_transitive; eauto using Set_is_subset, subset_S, in_S.
  Qed.

End Iterated_op_construction.

Definition add a b := (iterated_op (λ x _, S x) a id b).

Infix "+" := add : N_scope.

Theorem add_0_r : ∀ x, x + 0 = x.
Proof.
  move=> x.
  apply iterated_op_0.
Qed.

Theorem add_succ_r : ∀ x y, x + S y = S (x + y).
Proof.
  move=> x y.
  apply @iterated_op_succ.
Qed.

Definition mul a b := (iterated_op add 0 (λ x, a) b).

Infix "*" := mul : N_scope.

Theorem mul_0_r : ∀ x, x * 0 = 0.
Proof.
  move=> x.
  apply iterated_op_0.
Qed.

Theorem mul_succ_r : ∀ x y, x * (S y) = x * y + x.
Proof.
  move=> x y.
  apply iterated_op_succ.
Qed.

Theorem add_1_r : ∀ a, a + 1 = S a.
Proof.
  move=> a.
  rewrite /one add_succ_r add_0_r //.
Qed.

Theorem add_comm : ∀ a b, a + b = b + a.
Proof.
  induction a using Induction; induction b using Induction; auto.
  - rewrite add_0_r add_succ_r IHb add_0_r //.
  - rewrite add_0_r add_succ_r -IHa add_0_r //.
  - rewrite ? add_succ_r IHb -? IHa ? add_succ_r IHa //.
Qed.

Theorem add_assoc : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  induction c using Induction.
  - rewrite ? add_0_r //.
  - rewrite ? add_succ_r IHc //.
Qed.

Theorem add_0_l : ∀ x, 0 + x = x.
Proof.
  move=> x.
  rewrite add_comm add_0_r //.
Qed.

Theorem cancellation_add : ∀ a b c, a + b = a + c → b = c.
Proof.
  induction a using Induction => [b c | b c H].
  - rewrite ? add_0_l //.
  - apply IHa, PA5.
    rewrite ? (add_comm a) -? add_succ_r -? (add_comm (S a)) //.
Qed.

Theorem cancellation_0 : ∀ a b, a + b = a → b = 0.
Proof.
  move=> a b.
  rewrite -{2}(add_0_r a) => /cancellation_add //.
Qed.

Theorem mul_1_r : ∀ a, a * 1 = a.
Proof.
  move=> a.
  rewrite /one mul_succ_r mul_0_r add_0_l //.
Qed.

Theorem mul_2_r : ∀ x, x * 2 = x + x.
Proof.
  move=> x.
  rewrite /one mul_succ_r -/one mul_1_r //.
Qed.

Theorem mul_distr_r : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  induction c using Induction.
  - rewrite ? mul_0_r add_0_r //.
  - rewrite ? (mul_succ_r) IHc ? add_assoc
    -(add_assoc (a*c)) (add_comm _ a) ? add_assoc //.
Qed.

Theorem mul_comm : ∀ a b, a * b = b * a.
Proof.
  induction a using Induction; induction b using Induction; auto.
  - rewrite mul_succ_r IHb ? mul_0_r add_0_r //.
  - rewrite mul_succ_r -IHa ? mul_0_r add_0_r //.
  - rewrite ? mul_succ_r ? IHb -? IHa ? mul_succ_r
            -? add_assoc ? add_succ_r IHa (add_comm a) //.
Qed.

Theorem mul_distr_l : ∀ a b c, a * (b + c) = a * b + a * c.
Proof.
  move=> a b c.
  rewrite mul_comm mul_distr_r ? (mul_comm a) //.
Qed.

Theorem mul_assoc : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  induction c using Induction.
  - rewrite ? mul_0_r //.
  - rewrite ? (mul_succ_r) mul_distr_l IHc //.
Qed.

Theorem mul_0_l : ∀ a, 0 * a = 0.
Proof.
  move=> a.
  rewrite mul_comm mul_0_r //.
Qed.

Theorem mul_1_l : ∀ a, 1 * a = a.
Proof.
  move=> a.
  rewrite mul_comm mul_1_r //.
Qed.

Definition pow a b := (iterated_op mul 1 (λ x, a) b).

Infix "^" := pow : N_scope.

Theorem pow_0_r : ∀ x, x^0 = 1.
Proof.
  move=> x.
  apply iterated_op_0.
Qed.

Theorem pow_succ_r : ∀ x y, x^(S y) = x^y * x.
Proof.
  move=> x y.
  apply iterated_op_succ.
Qed.

Theorem pow_1_r : ∀ x, x^1 = x.
Proof.
  move=> x.
  rewrite /one pow_succ_r pow_0_r mul_comm mul_1_r //.
Qed.

Theorem pow_0_l : ∀ x, x ≠ 0 → 0^x = 0.
Proof.
  move=> x /succ_0 [m ->].
  rewrite pow_succ_r mul_0_r //.
Qed.

Theorem pow_1_l : ∀ x, 1^x = 1.
Proof.
  induction x using Induction.
  - rewrite pow_0_r //.
  - rewrite pow_succ_r mul_1_r //.
Qed.

Theorem pow_2_r : ∀ x, x^2 = x*x.
Proof.
  move=> x.
  rewrite pow_succ_r pow_1_r //.
Qed.

Theorem pow_add_r : ∀ a b c, a^(b+c) = a^b * a^c.
Proof.
  induction c using Induction.
  - rewrite add_0_r pow_0_r mul_1_r //.
  - rewrite add_succ_r ? pow_succ_r IHc mul_assoc //.
Qed.

Theorem pow_mul_l : ∀ a b c, (a*b)^c = a^c * b^c.
Proof.
  induction c using Induction.
  - rewrite ? pow_0_r mul_1_r //.
  - rewrite ? pow_succ_r -? mul_assoc (mul_assoc a)
            (mul_comm _ (b^c)) IHc ? mul_assoc //.
Qed.

Theorem pow_mul_r : ∀ a b c, a^(b*c) = (a^b)^c.
Proof.
  induction c using Induction.
  - rewrite mul_0_r ? pow_0_r //.
  - rewrite mul_succ_r pow_succ_r pow_add_r IHc //.
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
  split => [[c H] | H].
  - elim/Induction: c b H => [b <- | b H c <-].
    + rewrite add_0_r.
      auto using Set_is_subset.
    + eapply Subset_transitive; eauto.
      rewrite add_succ_r.
      apply subset_S.
  - elim/Induction: b H => [H | b].
    + eapply ex_intro, set_proj_injective, Subset_equality_iff, conj;
        auto using Empty_set_is_subset.
      erewrite add_0_r => //.
    + elim (classic (b ∈ a)) => [| ? H H0].
      * exists 0.
        rewrite add_0_r.
        apply set_proj_injective, Subset_equality_iff, conj; auto =>
        x /in_S_succ /Pairwise_union_classification
          [H2 | /Singleton_classification ->] //.
        eapply elements_of_naturals_are_subsets; eauto using elts_in_set.
      * elim H => [x <- | x /[dup] /H0 /in_S_succ /Pairwise_union_classification
                             [? | /Singleton_classification ->]] //.
        exists (S x).
        rewrite add_succ_r //.
Qed.

Theorem lt_is_in : ∀ a b, a < b ↔ a ∈ b.
  rewrite /lt => a b.
  (repeat split; rewrite ? le_is_subset) => [[H H0] | x |].
  - eapply subsets_of_naturals_are_elements;
      eauto using elts_in_set, set_proj_injective.
  - apply elements_of_naturals_are_subsets; eauto using elts_in_set.
  - move: H (elts_in_set b) => /pigeonhole_precursor /[apply] /[swap] ->.
    auto using Set_is_subset.
Qed.

Theorem lt_is_subsetneq : ∀ a b, a < b ↔ a ⊊ b.
Proof.
  split => [[/le_is_subset H H0] | [/le_is_subset H H0]];
             split; eauto using set_proj_injective; congruence.
Qed.

Theorem le_trichotomy : ∀ a b, a ≤ b ∨ b ≤ a.
Proof.
  move=> a b.
  rewrite ? le_is_subset.
  apply ω_trichotomy; eauto using elts_in_set.
Qed.

Theorem lt_trichotomy : ∀ a b, a < b ∨ a = b ∨ a > b.
Proof.
  rewrite /lt=> a b.
  elim (le_trichotomy a b); elim (classic (a = b)); intuition.
Qed.

Theorem le_antisymm : ∀ a b, a ≤ b → b ≤ a → a = b.
Proof.
  move=> a b.
  rewrite ? le_is_subset => H H0.
  apply /set_proj_injective /Subset_equality_iff => //.
Qed.

Theorem lt_antisym : ∀ a b, a < b → ¬ b < a.
Proof.
  move=> a b.
  rewrite ? lt_is_in => H H0.
  eapply ω_irreflexive; eauto using elts_in_set.
Qed.

Theorem lt_irrefl : ∀ a, ¬ a < a.
Proof.
  rewrite /lt => a [H H0] //.
Qed.

Theorem le_refl : ∀ a, a ≤ a.
Proof.
  move=> a.
  apply /le_is_subset /Set_is_subset.
Qed.

Add Ring N_semiring :
  (mk_srt 0 1 add mul eq add_0_l add_comm add_assoc
          mul_1_l mul_0_l mul_comm mul_assoc mul_distr_r).

Theorem lt_def : ∀ a b, a < b ↔ ∃ c : N, 0 ≠ c ∧ a + c = b.
Proof.
  rewrite /lt /le => a b.
  (repeat split) => [[[c H] H0] | | ].
  - exists c.
    split; auto.
    move: H H0 <- => /[swap] <-.
    rewrite add_0_r //.
  - move: H => [c] [H] <-.
    eauto.
  - move: H => [c] /[swap] <- [/neq_sym H /cancellation_0 H0] //.
Qed.

Theorem cancellation_0_add : ∀ a b, a + b = 0 → a = 0 ∧ b = 0.
Proof.
  (do 2 elim/Induction) =>
  [n | n | H b | n H H0 b ]; rewrite ? add_0_l ? add_0_r; try tauto;
    rewrite add_comm add_succ_r => *; exfalso; eapply PA4; eauto.
Qed.

Theorem cancellation_1_add : ∀ a b, a + b = 1 → a = 0 ∨ b = 0.
Proof.
  (do 2 elim/Induction) =>
  [n | n | H b | n H H0 b]; rewrite ? add_0_l ? add_0_r; try tauto.
  - rewrite add_comm add_succ_r add_0_r => /PA5; tauto.
  - rewrite add_comm add_succ_r => /PA5 /cancellation_0_add; tauto.
Qed.

Theorem cancellation_0_mul : ∀ a b, a * b = 0 → a = 0 ∨ b = 0.
Proof.
  ((do 2 elim/Induction) =>
   [ | | H b | n _ _ b]; rewrite ? mul_1_l 1 ? mul_comm ? mul_succ_r;
   try tauto) => /cancellation_0_add; tauto.
Qed.

Theorem mul_lt_l : ∀ a b c, a ≠ 0 → b < c → a * b < a * c.
Proof.
  move=> a b c.
  rewrite ? lt_def => H [n [H0 <-]].
  exists (a*n).
  split => [/(@eq_sym N) /cancellation_0_mul [H1 | H1] | ]; auto; ring.
Qed.

Theorem mul_lt_r : ∀ a b c, a ≠ 0 → b < c → b * a < c * a.
Proof.
  move=> a b c.
  rewrite -? (mul_comm a).
  auto using mul_lt_l.
Qed.

Theorem mul_le_r : ∀ a b c, a ≤ b → a * c ≤ b * c.
Proof.
  move=> a b c [n] <-.
  exists (n*c).
  ring.
Qed.

Theorem mul_le_l : ∀ a b c, a ≤ b → c * a ≤ c * b.
Proof.
  move=> a b c.
  rewrite ? (mul_comm c).
  auto using mul_le_r.
Qed.

Theorem cancellation_mul : ∀ a b c : N, c ≠ 0 → a * c = b * c → a = b.
Proof.
  move: lt_trichotomy =>
  /[swap] a /[swap] b /[swap] c /(_ a b)
   [/(mul_lt_r c) H /H /[swap] -> /lt_irrefl |
    [H | /(mul_lt_r c) /[apply] /[swap] -> /lt_irrefl]] //.
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
