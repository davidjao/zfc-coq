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
  Infix "<" := (lt_OR OR).
  Notation "a > b" := (b < a) (only parsing).
  Definition le a b := a < b ∨ a = b.
  Infix "≤" := le.
  Notation "x < y < z" := (x < y ∧ y < z).
  Notation "a ≥ b" := (b ≤ a) (only parsing).
  Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level).
  Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level).
  Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level).

  Add Ring R_ring :
    (mk_rt 0 1 (add_R R) (mul_R R) (sub_R R) (neg_R R) eq (A3_R R) (A1_R R)
           (A2_R R) (M3_R R) (M1_R R) (M2_R R) (D1_R R) (sub_neg_R R) (A4_R R)).

  Theorem O1_r : ∀ a b c, b < c → b + a < c + a.
  Proof.
    intros a b c H.
    rewrite ? (A1_R _ _ a).
    auto using O1_OR.
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

  Definition cancellation_0_add := cancellation_0_add R.
  Definition cancellation_add := cancellation_add R.
  Definition cancellation_ne0 := cancellation_ne0 R.

  Theorem cancellation_0_mul : ∀ a b, a * b = 0 → a = 0 ∨ b = 0.
  Proof.
    intros a b H.
    destruct (T_OR _ (a*b) 0), (T_OR _ a 0), (T_OR _ b 0); intuition;
      eauto using pos_mul, neg_mul; exfalso;
        eauto using mul_neg_neg, mul_neg_pos, mul_pos_neg, mul_pos_pos.
  Qed.

  Definition integral_domain_OR :=
    mkID (ring_OR OR) cancellation_0_mul (nontrivial_OR OR).

End Ordered_ring_theorems.
