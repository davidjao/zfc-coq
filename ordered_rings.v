Require Export integral_domains.
Set Warnings "-notation-overridden".

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

  Notation R := (ring_OR OR).
  Notation "0" := (zero_R R).
  Notation "1" := (one_R R).
  Infix "+" := (add_R R).
  Infix "*" := (mul_R R).
  Notation "- a" := (neg_R R a).
  Infix "-" := (sub_R R).
  Infix "^" := (pow R).
  Infix "<" := (lt_OR OR).
  Notation "a > b" := (b < a) (only parsing).
  Definition le a b := a < b ∨ a = b.
  Infix "≤" := le.
  Notation "x < y < z" := (x < y ∧ y < z).
  Notation "a ≥ b" := (b ≤ a) (only parsing).
  Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level).
  Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level).
  Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level).

  Add Ring generic_ordered_ring :
    (mk_rt 0 1 (add_R R) (mul_R R) (sub_R R) (neg_R R) eq (A3_R R) (A1_R R)
           (A2_R R) (M3_R R) (M1_R R) (M2_R R) (D1_R R) (sub_neg_R R) (A4_R R)).

  Theorem O1_r : ∀ a b c, b < c → b + a < c + a.
  Proof.
    intros a b c H.
    rewrite ? (A1_R _ _ a).
    auto using O1_OR.
  Qed.

  Theorem add_le_r : ∀ a b c, b ≤ c → b + a ≤ c + a.
  Proof.
    intros a b c [H | H].
    - left.
      auto using O1_r.
    - right.
      now subst.
  Qed.

  Theorem add_le_l : ∀ a b c, b ≤ c → a + b ≤ a + c.
  Proof.
    intros a b c H.
    rewrite ? (A1_R R a) in *.
    now apply add_le_r.
  Qed.

  Theorem O0 : ∀ a b, 0 < a → 0 < b → 0 < a + b.
  Proof.
    intros a b H H0.
    apply (O1_OR _ 0) in H.
    apply (O1_OR _ a) in H0.
    rewrite A3_R, A1_R in H.
    eauto using lt_trans_OR.
  Qed.

  Theorem lt_shift : ∀ a b, a < b ↔ 0 < b + -a.
  Proof.
    split; intros H.
    - apply (O1_r (-a)) in H.
      now rewrite A4_R in H.
    - apply (O1_r a) in H.
      now rewrite A3_R, <-A2_R, A4_l, A3_r in H.
  Qed.

  Theorem O3 : ∀ a b c, 0 < a → b < c → a * b < a * c.
  Proof.
    intros a b c H H0.
    rewrite lt_shift in *.
    replace (a*c+-(a*b)) with ((a+-0)*(c+-b)) by ring.
    auto using O2_OR.
  Qed.

  Theorem O3_r : ∀ a b c, 0 < a → b < c → b * a < c * a.
  Proof.
    intros a b c H H0.
    rewrite ? (M1_R _ _ a).
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

  Definition mul_pos_pos := O2_OR.

  Theorem mul_pos_neg : ∀ a b, 0 < a → b < 0 → a * b < 0.
  Proof.
    intros a b H H0.
    rewrite lt_neg_0 in *.
    eapply O2_OR in H; eauto.
    replace (-(a*b)) with (-b*a) in * by ring; auto.
  Qed.

  Theorem mul_neg_pos : ∀ a b, a < 0 → 0 < b → a * b < 0.
  Proof.
    intros a b H H0.
    rewrite M1_R.
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
    destruct (T_OR _ (a*b) 0), (T_OR _ a 0), (T_OR _ b 0); intuition; subst;
      try replace (a*0) with 0 in * by ring;
      try replace (0*b) with 0 in * by ring;
      try replace (0*0) with 0 in * by ring; auto;
        exfalso; eauto using mul_neg_pos, mul_pos_neg.
  Qed.

  Theorem neg_mul : ∀ a b, a * b < 0 → (0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b).
  Proof.
    intros a b H.
    destruct (T_OR _ (a*b) 0), (T_OR _ a 0), (T_OR _ b 0); intuition; subst;
      try replace (a*0) with 0 in * by ring;
      try replace (0*b) with 0 in * by ring;
      try replace (0*0) with 0 in * by ring; auto;
        exfalso; eauto using mul_neg_neg, mul_pos_pos.
  Qed.

  Theorem cancellation_0_mul : ∀ a b, a * b = 0 → a = 0 ∨ b = 0.
  Proof.
    intros a b H.
    destruct (T_OR _ (a*b) 0), (T_OR _ a 0), (T_OR _ b 0); intuition;
      eauto using pos_mul, neg_mul; exfalso;
        eauto using mul_neg_neg, mul_neg_pos, mul_pos_neg, mul_pos_pos.
  Qed.

  Definition integral_domain_OR :=
    mkID (ring_OR OR) cancellation_0_mul (nontrivial_OR OR).

  Lemma zero_lt_1 : 0 < 1.
  Proof.
    destruct (T_OR _ 0 1) as [[H [H0 H1]] | [[H [H0 H1]] | [H [H0 H1]]]];
      try tauto.
    - now contradiction (nontrivial_OR OR).
    - apply (O1_r (-(1))) in H1.
      rewrite A4_R, A3_R in H1.
      eapply O2_OR in H1; eauto.
      now replace 1 with (-(1)*-(1)) by ring.
  Qed.

  Lemma lt_succ : ∀ m, m < m + 1.
  Proof.
    intros m.
    rewrite <-(A3_R _ m), A1_R at 1.
    eauto using O1_OR, zero_lt_1.
  Qed.

  Lemma succ_lt : ∀ n m, n < m → n < m + 1.
  Proof.
    eauto using lt_succ, lt_trans_OR.
  Qed.

  Theorem lt_irrefl : ∀ a, ¬ a < a.
  Proof.
    intros a.
    destruct (T_OR _ a a); intuition.
  Qed.

  Theorem lt_antisym : ∀ a b, a < b → ¬ b < a.
  Proof.
    intros a b H.
    destruct (T_OR _ a b); intuition.
  Qed.

  Theorem le_antisymm : ∀ a b, a ≤ b → b ≤ a → a = b.
  Proof.
    intros a b [H | H] [H0 | H0]; destruct (T_OR _ a b); intuition.
  Qed.

  Lemma square_ne0 : ∀ a, a ≠ 0 → a*a > 0.
  Proof.
    intros a H.
    destruct (T_OR _ a 0) as [[H0 _] | [[_ [H0 _]] | [_ [_ H0]]]];
      try now subst; auto using mul_pos_pos, mul_neg_neg.
  Qed.

  Theorem le_trans : ∀ a b c, a ≤ b → b ≤ c → a ≤ c.
  Proof.
    intros a b c [H | H] [H0 | H0]; subst; unfold le; eauto using lt_trans_OR.
  Qed.

  Lemma pos_div_l : ∀ a b, 0 < a → 0 < a * b → 0 < b.
  Proof.
    intros a b H H0.
    pose proof (pos_mul a b).
    destruct (T_OR _ 0 a), (T_OR _ 0 b); intuition.
  Qed.

  Lemma pos_div_r : ∀ a b, 0 < a → 0 < b * a → 0 < b.
  Proof.
    intros a b H H0.
    rewrite M1_R in *.
    eauto using pos_div_l.
  Qed.

  Lemma one_lt : ∀ a, 1 < a → 0 < a.
  Proof.
    eauto using lt_trans_OR, zero_lt_1.
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
    rewrite ? (M1_R _ _ c).
    now apply mul_le_l.
  Qed.

  Theorem neg_neg_lt : ∀ a b, a < b → -b < -a.
  Proof.
    intros a b H.
    apply (O1_r (-a+-b)) in H.
    now rewrite A2_R, A4_R, A3_R, A1_R, <-A2_R, A4_l, A3_r in H.
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
    unfold sub_R.
    rewrite lt_shift in *.
    now replace (a+-(a+-b)) with (b+-0) by ring.
  Qed.

  Theorem lt_cross_mul : ∀ a b c d,
      0 < a → 0 < c → a < b → c < d → a * c < b * d.
  Proof.
    intros a b c d H H0 H1 H2.
    apply (O3 c) in H1 as H3; auto.
    apply (O3 b) in H2; eauto using lt_trans_OR.
    rewrite ? (M1_R _ c) in H3.
    eauto using lt_trans_OR.
  Qed.

  Theorem lt_or_ge : ∀ a b, a < b ∨ b ≤ a.
  Proof.
    intros a b.
    unfold le.
    destruct (T_OR _ a b) as [[H _] | [[_ [H _]] | [_ [_ H]]]];
      try symmetry in H; tauto.
  Qed.

  Theorem lt_not_ge : ∀ a b, a < b ↔ ¬ b ≤ a.
  Proof.
    intros a b.
    unfold le.
    pose proof (T_OR _ b a).
    tauto.
  Qed.

  Theorem le_not_gt : ∀ a b, a ≤ b ↔ ¬ b < a.
  Proof.
    intros a b.
    unfold le.
    pose proof (T_OR _ a b).
    tauto.
  Qed.

  Theorem O0_opp : ∀ a b, 0 < a + b → 0 < a ∨ 0 < b.
  Proof.
    intros a b H.
    destruct (T_OR _ 0 a) as [[H0 _] | [[_ [H0 _]] | [_ [_ H0]]]]; try tauto.
    - subst.
      rewrite A3_R in H.
      now right.
    - assert (a < a + b) as H1 by eauto using lt_trans_OR.
      rewrite lt_shift in H1.
      ring_simplify in H1.
      now right.
  Qed.

  Theorem pow_pos : ∀ a b, 0 < a → 0 < a^b.
  Proof.
    induction b using Induction; intros H.
    - rewrite pow_0_r.
      exact zero_lt_1.
    - rewrite pow_succ_r.
      auto using O2_OR.
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
        now rewrite M3_R in H.
      + now rewrite <-H0, M3_R.
  Qed.

  Theorem pow_gt_1 : ∀ a n, 1 < a → (0 < n)%N → 1 < a^n.
  Proof.
    induction n using Induction; intros H H0.
    - contradiction (naturals.lt_irrefl 0).
    - rewrite pow_succ_r.
      destruct (classic (n = 0)%N).
      + now rewrite H1, pow_0_r, M3_R.
      + apply succ_0 in H1 as [m H1].
        subst.
        apply (lt_cross_mul 1 (a ^ S m) 1 a) in H; auto using zero_lt_1.
        * now rewrite M3_R in H.
        * apply IHn; auto.
          apply naturals.lt_succ.
  Qed.

  Theorem one_lt_2 : 1 < 1 + 1.
  Proof.
    rewrite <-(A3_r _ 1) at 1.
    apply O1_OR, zero_lt_1.
  Qed.

  Definition min : (elts (set_R R)) → (elts (set_R R)) → (elts (set_R R)).
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

  Definition max : (elts (set_R R)) → (elts (set_R R)) → (elts (set_R R)).
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
    apply (O1_OR _ b) in H0.
    eauto using lt_trans_OR.
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
    destruct (T_OR _ 1 r) as [[H1 [H2 H3]] | [[H1 [H2 H3]] | [H1 [H2 H3]]]];
      try tauto.
    - subst.
      rewrite M3_R in *.
      contradiction (lt_irrefl 1).
    - contradiction (lt_antisym 1 (r*r)); auto; simpl.
      rewrite <-(M3_R _ 1).
      now apply lt_cross_mul.
  Qed.

End Ordered_ring_theorems.
