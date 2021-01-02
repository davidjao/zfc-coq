Require Export rings.
Set Warnings "-notation-overridden".

Record ordered_ring :=
  mkOring {
      ring_OR : ring where
      "a + b" :=
        (add_R ring_OR a b)
          and "a * b" :=
        (mul_R ring_OR a b)
          and "0" :=
          (zero_R ring_OR);
      lt_OR : elts (set_R ring_OR) → elts (set_R ring_OR) → Prop
      where "a < b" := (lt_OR a b);
      lt_trans_OR : ∀ a b c, a < b → b < c → a < c;
      T_OR : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ b < a) ∨
                    (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
                    (¬ a < b ∧ a ≠ b ∧ b < a);
      O1_OR : ∀ a b c, b < c → a + b < a + c;
      O2_OR : ∀ a b, 0 < a → 0 < b → 0 < a * b;
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
  Notation "a > b" := (b < a).
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
    rewrite (A3_R _), (A1_R _) in H.
    eauto using lt_trans_OR.
  Qed.

  Theorem lt_shift : ∀ a b, a < b ↔ 0 < b + -a.
  Proof.
    split; intros H.
    - apply (O1_r (-a)) in H.
      now rewrite (A4_R _) in H.
    - apply (O1_r a) in H.
      now rewrite (A3_R _), <-(A2_R _), (A4_l _), (A3_r _) in H.
  Qed.

  Theorem O3 : ∀ a b c, 0 < a → b < c → a * b < a * c.
  Proof.
    intros a b c H H0.
    rewrite lt_shift in *.
    replace (a*c+-(a*b)) with ((a+-0)*(c+-b)) by ring.
    auto using O2_OR.
  Qed.

End Ordered_ring_theorems.
