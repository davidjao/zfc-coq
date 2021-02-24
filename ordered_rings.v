Set Warnings "-notation-overridden,-ambiguous-paths".
Require Export integral_domains.

Record ordered_ring :=
  mkOring {
      ring_OR : ring where
      "a + b" :=
        (add_R ring_OR a b)
          and "a * b" :=
        (mul_R ring_OR a b)
          and "0" :=
          (zero_R ring_OR)
          and "1" :=
            (one_R ring_OR);
      lt_OR : elts (set_R ring_OR) → elts (set_R ring_OR) → Prop
      where "a < b" := (lt_OR a b);
      lt_trans_OR : ∀ a b c, a < b → b < c → a < c;
      T_OR : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ b < a) ∨
                    (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
                    (¬ a < b ∧ a ≠ b ∧ b < a);
      O1_OR : ∀ a b c, b < c → a + b < a + c;
      O2_OR : ∀ a b, 0 < a → 0 < b → 0 < a * b;
      nontrivial_OR : 1 ≠ 0;
    }.

Section Ordered_ring_theorems.

  Variable OR : ordered_ring.

  Definition R := (ring_OR OR).
  Notation "0" := (zero R).
  Notation "1" := (one R).
  Infix "+" := (add R).
  Notation "2" := (1 + 1).
  Infix "*" := (mul R).
  Notation "- a" := (neg R a).
  Infix "-" := (sub R).
  Infix "^" := (pow R).
  Definition lt := lt_OR OR : rings.R R → rings.R R → Prop.
  Infix "<" := lt.
  Definition lt_trans := lt_trans_OR OR : ∀ a b c, a < b → b < c → a < c.
  Definition O1 := O1_OR OR : ∀ a b c, b < c → a + b < a + c.
  Definition O2 := O2_OR OR : ∀ a b, 0 < a → 0 < b → 0 < a * b.
  Definition T := T_OR OR : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ b < a) ∨
                                   (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
                                   (¬ a < b ∧ a ≠ b ∧ b < a).
  Notation "a > b" := (b < a) (only parsing).
  Definition le a b := a < b ∨ a = b.
  Infix "≤" := le.
  Notation "x < y < z" := (x < y ∧ y < z).
  Notation "a ≥ b" := (b ≤ a) (only parsing).
  Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level).
  Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level).
  Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level).

  Add Ring generic_ordered_ring :
    (mk_rt 0 1 (add R) (mul R) (sub R) (neg R) eq (A3 R) (A1 R)
           (A2 R) (M3 R) (M1 R) (M2 R) (D1 R) (sub_is_neg R) (A4 R)).

  Theorem O1_r : ∀ a b c, b < c → b + a < c + a.
  Proof.
    intros a b c H.
    rewrite ? (A1_R _ _ a).
    auto using O1.
  Qed.

  Theorem add_le_r : ∀ a b c, b ≤ c → b + a ≤ c + a.
  Proof.
    intros a b c [H | H].
    - left.
      auto using O1_r.
    - right.
      ring [H].
  Qed.

  Theorem add_le_l : ∀ a b c, b ≤ c → a + b ≤ a + c.
  Proof.
    intros a b c H.
    rewrite ? (A1 R a) in *.
    now apply add_le_r.
  Qed.

  Theorem O0 : ∀ a b, 0 < a → 0 < b → 0 < a + b.
  Proof.
    intros a b H H0.
    apply (O1 0) in H.
    apply (O1 a) in H0.
    rewrite A3, A1 in H.
    eauto using lt_trans.
  Qed.

  Theorem lt_shift : ∀ a b, a < b ↔ 0 < b + -a.
  Proof.
    split; intros H.
    - apply (O1_r (-a)) in H.
      now rewrite A4 in H.
    - apply (O1_r a) in H.
      now rewrite A3, <-A2, A4_l, A3_r in H.
  Qed.

  Theorem O3 : ∀ a b c, 0 < a → b < c → a * b < a * c.
  Proof.
    intros a b c H H0.
    rewrite lt_shift in *.
    replace (a*c+-(a*b)) with ((a+-0)*(c+-b)) by ring.
    auto using O2.
  Qed.

  Theorem O3_r : ∀ a b c, 0 < a → b < c → b * a < c * a.
  Proof.
    intros a b c H H0.
    rewrite ? (M1 _ _ a).
    now apply O3.
  Qed.

  Definition mul_lt_l := O3.
  Definition mul_lt_r := O3_r.

  Theorem neg_lt_0 : ∀ a, 0 < a ↔ -a < 0.
  Proof.
    split; intros H.
    - rewrite lt_shift in *.
      replace (a+-0) with a in * by ring.
      now replace (0+--a) with a by ring.
    - rewrite lt_shift in H.
      now replace (0+--a) with a in * by ring.
  Qed.

  Theorem lt_neg_0 : ∀ a, a < 0 ↔ 0 < -a.
  Proof.
    intros a.
    rewrite neg_lt_0.
    now replace (--a) with a by ring.
  Qed.

  Definition mul_pos_pos := O2.

  Theorem mul_pos_neg : ∀ a b, 0 < a → b < 0 → a * b < 0.
  Proof.
    intros a b H H0.
    rewrite lt_neg_0 in *.
    eapply O2 in H; eauto.
    replace (-(a*b)) with (-b*a) in * by ring; auto.
  Qed.

  Theorem mul_neg_pos : ∀ a b, a < 0 → 0 < b → a * b < 0.
  Proof.
    intros a b H H0.
    rewrite M1.
    now apply mul_pos_neg.
  Qed.

  Theorem mul_neg_neg : ∀ a b, a < 0 → b < 0 → 0 < a * b.
  Proof.
    intros a b H H0.
    rewrite lt_neg_0 in *.
    replace (a*b) with (-a*-b) by ring; eauto using mul_pos_pos.
  Qed.

  Theorem pos_mul : ∀ a b, 0 < a * b → (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0).
  Proof.
    intros a b H.
    destruct (T (a*b) 0), (T a 0), (T b 0); intuition; subst;
      try replace (a*0) with 0 in * by ring;
      try replace (0*b) with 0 in * by ring;
      try replace (0*0) with 0 in * by ring; auto;
        exfalso; eauto using mul_neg_pos, mul_pos_neg.
  Qed.

  Theorem neg_mul : ∀ a b, a * b < 0 → (0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b).
  Proof.
    intros a b H.
    destruct (T (a*b) 0), (T a 0), (T b 0); intuition; subst;
      try replace (a*0) with 0 in * by ring;
      try replace (0*b) with 0 in * by ring;
      try replace (0*0) with 0 in * by ring; auto;
        exfalso; eauto using mul_neg_neg, mul_pos_pos.
  Qed.

  Theorem cancellation_0_mul : ∀ a b, a * b = 0 → a = 0 ∨ b = 0.
  Proof.
    intros a b H.
    destruct (T (a*b) 0), (T a 0), (T b 0); intuition;
      eauto using pos_mul, neg_mul; exfalso;
        eauto using mul_neg_neg, mul_neg_pos, mul_pos_neg, mul_pos_pos.
  Qed.

  Definition integral_domain_OR :=
    mkID (ring_OR OR) cancellation_0_mul (nontrivial_OR OR).

  Lemma zero_lt_1 : 0 < 1.
  Proof.
    destruct (T 0 1) as [[H [H0 H1]] | [[H [H0 H1]] | [H [H0 H1]]]];
      try tauto.
    - now contradiction (nontrivial_OR OR).
    - apply (O1_r (-(1))) in H1.
      rewrite A4, A3 in H1.
      eapply O2 in H1; eauto.
      now replace 1 with (-(1)*-(1)) by ring.
  Qed.

  Lemma lt_succ : ∀ m, m < m + 1.
  Proof.
    intros m.
    rewrite <-(A3 _ m), A1_R at 1.
    eauto using O1, zero_lt_1.
  Qed.

  Lemma succ_lt : ∀ n m, n < m → n < m + 1.
  Proof.
    eauto using lt_succ, lt_trans.
  Qed.

  Theorem lt_irrefl : ∀ a, ¬ a < a.
  Proof.
    intros a.
    destruct (T a a); intuition.
  Qed.

  Theorem lt_antisym : ∀ a b, a < b → ¬ b < a.
  Proof.
    intros a b H.
    destruct (T a b); intuition.
  Qed.

  Theorem le_antisymm : ∀ a b, a ≤ b → b ≤ a → a = b.
  Proof.
    intros a b [H | H] [H0 | H0]; destruct (T a b); intuition.
  Qed.

  Lemma square_ne0 : ∀ a, a ≠ 0 → a*a > 0.
  Proof.
    intros a H.
    destruct (T a 0) as [[H0 _] | [[_ [H0 _]] | [_ [_ H0]]]];
      try now subst; auto using mul_pos_pos, mul_neg_neg.
  Qed.

  Theorem le_trans : ∀ a b c, a ≤ b → b ≤ c → a ≤ c.
  Proof.
    intros a b c [H | H] [H0 | H0]; subst; unfold le; eauto using lt_trans.
  Qed.

  Lemma pos_div_l : ∀ a b, 0 < a → 0 < a * b → 0 < b.
  Proof.
    intros a b H H0.
    pose proof (pos_mul a b).
    destruct (T 0 a), (T 0 b); intuition.
  Qed.

  Lemma pos_div_r : ∀ a b, 0 < a → 0 < b * a → 0 < b.
  Proof.
    intros a b H H0.
    rewrite M1_R in *.
    eauto using pos_div_l.
  Qed.

  Lemma one_lt : ∀ a, 1 < a → 0 < a.
  Proof.
    eauto using lt_trans, zero_lt_1.
  Qed.

  Theorem mul_le_l : ∀ a b c, 0 < a → b ≤ c → a * b ≤ a * c.
  Proof.
    intros a b c H H0.
    unfold le in *.
    destruct H0 as [H0 | H0]; [ left | right ]; subst; simpl in *; auto.
    apply mul_lt_l; eauto.
  Qed.

  Theorem mul_le_r : ∀ a b c, a ≤ b → 0 < c → a * c ≤ b * c.
  Proof.
    intros a b c H H0.
    rewrite ? (M1 _ _ c).
    now apply mul_le_l.
  Qed.

  Theorem neg_neg_lt : ∀ a b, a < b → -b < -a.
  Proof.
    intros a b H.
    apply (O1 (-a+-b)) in H.
    now ring_simplify in H.
  Qed.

  Theorem lt_neq : ∀ a b, a < b → b ≠ a.
  Proof.
    intros a b H H0.
    subst.
    contradiction (lt_irrefl a).
  Qed.

  Theorem lt_sub_pos : ∀ a b, 0 < b → a - b < a.
  Proof.
    intros.
    rewrite lt_shift.
    now ring_simplify.
  Qed.

  Theorem lt_cross_mul : ∀ a b c d,
      0 < a → 0 < c → a < b → c < d → a * c < b * d.
  Proof.
    intros a b c d H H0 H1 H2.
    apply (O3 c) in H1 as H3; auto.
    apply (O3 b) in H2; eauto using lt_trans.
    rewrite ? (M1 _ c) in H3.
    eauto using lt_trans.
  Qed.

  Theorem lt_or_ge : ∀ a b, a < b ∨ b ≤ a.
  Proof.
    intros a b.
    unfold le.
    destruct (T a b) as [[H _] | [[_ [H _]] | [_ [_ H]]]];
      try symmetry in H; tauto.
  Qed.

  Theorem lt_not_ge : ∀ a b, a < b ↔ ¬ b ≤ a.
  Proof.
    intros a b.
    unfold le.
    pose proof (T b a).
    tauto.
  Qed.

  Theorem le_not_gt : ∀ a b, a ≤ b ↔ ¬ b < a.
  Proof.
    intros a b.
    unfold le.
    pose proof (T a b).
    tauto.
  Qed.

  Theorem O0_opp : ∀ a b, 0 < a + b → 0 < a ∨ 0 < b.
  Proof.
    intros a b H.
    destruct (T 0 a) as [[H0 _] | [[_ [H0 _]] | [_ [_ H0]]]]; try tauto.
    - subst.
      rewrite A3 in H.
      now right.
    - assert (a < a + b) as H1 by eauto using lt_trans.
      rewrite lt_shift in H1.
      right.
      now ring_simplify in H1.
  Qed.

  Theorem pow_pos : ∀ a b, 0 < a → 0 < a^b.
  Proof.
    induction b using Induction; intros H.
    - rewrite pow_0_r.
      exact zero_lt_1.
    - rewrite pow_succ_r.
      auto using O2.
  Qed.

  Theorem pow_ge_1 : ∀ a n, 1 < a → 1 ≤ a^n.
  Proof.
    induction n using Induction; intros H.
    - rewrite pow_0_r.
      now right.
    - rewrite pow_succ_r.
      left.
      destruct (IHn H) as [H0 | H0].
      + eapply lt_cross_mul in H; try exact H0; auto using zero_lt_1.
        now ring_simplify in H.
      + now rewrite <-H0, M3.
  Qed.

  Theorem pow_gt_1 : ∀ a n, 1 < a → (0 < n)%N → 1 < a^n.
  Proof.
    induction n using Induction; intros H H0.
    - contradiction (naturals.lt_irrefl 0).
    - rewrite pow_succ_r.
      destruct (classic (n = 0%N)).
      + now rewrite H1, pow_0_r, M3.
      + apply succ_0 in H1 as [m H1].
        subst.
        apply (lt_cross_mul 1 (a ^ S m) 1 a) in H;
          eauto using zero_lt_1, naturals.lt_succ.
        now ring_simplify in H.
  Qed.

  Theorem one_lt_2 : 1 < 1 + 1.
  Proof.
    rewrite <-(A3_r _ 1) at 1.
    apply O1, zero_lt_1.
  Qed.

  Definition min : rings.R R → rings.R R → rings.R R.
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
    - now right.
    - now rewrite <-le_not_gt in n.
  Qed.

  Theorem min_le_r : ∀ a b, min a b ≤ b.
  Proof.
    intros a b.
    unfold min.
    destruct excluded_middle_informative.
    - now left.
    - now right.
  Qed.

  Theorem min_eq : ∀ a b, min a b = a ∨ min a b = b.
  Proof.
    intros a b.
    unfold min.
    destruct excluded_middle_informative.
    - now left.
    - now right.
  Qed.

  Definition max : rings.R R → rings.R R → rings.R R.
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
    - now left.
    - now right.
  Qed.

  Theorem max_le_r : ∀ a b, b ≤ max a b.
  Proof.
    intros a b.
    unfold max.
    destruct excluded_middle_informative.
    - now right.
    - now rewrite <-le_not_gt in n.
  Qed.

  Theorem max_eq : ∀ a b, max a b = a ∨ max a b = b.
  Proof.
    intros a b.
    unfold max.
    destruct excluded_middle_informative.
    - now right.
    - now left.
  Qed.

  Theorem lt_cross_add : ∀ a b c d, a < b → c < d → a + c < b + d.
  Proof.
    intros a b c d H H0.
    apply (O1_r c) in H.
    apply (O1 b) in H0.
    eauto using lt_trans.
  Qed.

  Theorem le_cross_add : ∀ a b c d, a ≤ b → c ≤ d → a + c ≤ b + d.
  Proof.
    intros a b c d H H0.
    apply (add_le_r c) in H.
    apply (add_le_l b) in H0.
    eauto using le_trans.
  Qed.

  Lemma square_ge_1 : ∀ r, 0 < r → 1 < r * r → 1 < r.
  Proof.
    intros r H H0.
    destruct (T 1 r) as [[H1 [H2 H3]] | [[H1 [H2 H3]] | [H1 [H2 H3]]]];
      try tauto.
    - subst.
      rewrite M3 in *.
      contradiction (lt_irrefl 1).
    - contradiction (lt_antisym 1 (r*r)); auto; simpl.
      rewrite <-(M3 _ 1).
      now apply lt_cross_mul.
  Qed.

  Theorem zero_lt_2 : 0 < 2.
  Proof.
    eapply lt_trans; eauto using zero_lt_1.
    rewrite lt_shift.
    ring_simplify.
    exact zero_lt_1.
  Qed.

  Theorem zero_ne_2 : 2 ≠ 0.
  Proof.
    intros H.
    contradiction (lt_irrefl 0).
    rewrite <-H at 2.
    exact zero_lt_2.
  Qed.

  Theorem le_lt_trans : ∀ a b c, a ≤ b → b < c → a < c.
  Proof.
    intros a b c [H | H] H0.
    - eauto using lt_trans.
    - subst; auto.
  Qed.

  Theorem lt_le_trans : ∀ a b c, a < b → b ≤ c → a < c.
  Proof.
    intros a b c H [H0 | H0].
    - eauto using lt_trans.
    - subst; auto.
  Qed.

  Theorem le_refl : ∀ a, a ≤ a.
  Proof.
    intros a.
    now right.
  Qed.

  Theorem mul_le_l_nonneg : ∀ a b c, 0 ≤ a → b ≤ c → a * b ≤ a * c.
  Proof.
    intros a b c [H | H] H0.
    - auto using mul_le_l.
    - subst.
      ring_simplify.
      auto using le_refl.
  Qed.

  Theorem mul_le_r_nonneg : ∀ a b c, a ≤ b → 0 ≤ c → a * c ≤ b * c.
  Proof.
    intros a b c H [H0 | H0].
    - auto using mul_le_r.
    - subst.
      ring_simplify.
      auto using le_refl.
  Qed.

  Theorem mul_nonneg_nonneg : ∀ a b, 0 ≤ a → 0 ≤ b → 0 ≤ a * b.
  Proof.
    intros a b H H0.
    replace 0 with (a*0) by ring.
    auto using mul_le_l_nonneg.
  Qed.

End Ordered_ring_theorems.
