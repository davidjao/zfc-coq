Require Export rings.
Set Warnings "-notation-overridden".

Record integral_domain :=
  mkID {
      ring_ID : ring where
      "a + b" :=
        (add_R ring_ID a b)
          and "a * b" :=
        (mul_R ring_ID a b)
          and "0" :=
          (zero_R ring_ID)
            and "1" :=
            (one_R ring_ID);
      cancellation_ID : ∀ a b, a * b = 0 → a = 0 ∨ b = 0;
      nontrivial_ID : 1 ≠ 0;
    }.

Section Integral_domain_theorems.

  Variable ID : integral_domain.

  Notation R := (ring_ID ID).
  Notation "0" := (zero_R R).
  Notation "1" := (one_R R).
  Infix "+" := (add_R R).
  Infix "-" := (sub_R R).
  Infix "*" := (mul_R R).
  Notation "- a" := (neg_R R a).
  Infix "^" := (pow R).
  
  Add Ring R_ring :
    (mk_rt 0 1 (add_R R) (mul_R R) (sub_R R) (neg_R R) eq (A3_R R) (A1_R R)
           (A2_R R) (M3_R R) (M1_R R) (M2_R R) (D1_R R) (sub_neg_R R) (A4_R R)).

  Lemma ne0_cancellation : ∀ a b, a ≠ 0 → b ≠ 0 → a * b ≠ 0.
  Proof.
    intros a b H H0 H1.
    now apply cancellation_ID in H1 as [H1 | H1].
  Qed.

  Theorem cancellation_mul_l : ∀ a b c, a ≠ 0 → a * b = a * c → b = c.
  Proof.
    intros a b c H H0.
    assert (a * (b - c) = 0) as H1 by ring [H0].
    apply cancellation_ID in H1 as [H1 | H1]; intuition.
    apply cancellation_0_add in H1.
    ring [H1].
  Qed.

  Theorem cancellation_mul_r : ∀ a b c, a ≠ 0 → b * a = c * a → b = c.
  Proof.
    eauto using M1_R, eq_trans, cancellation_mul_l.
  Qed.

  Theorem pow_ne_0 : ∀ a b, a ≠ 0 → a^b ≠ 0.
  Proof.
    induction b using Induction; intros H.
    - rewrite (pow_0_r R); auto using nontrivial_ID.
    - rewrite pow_succ_r.
      intros H0.
      contradiction (IHb H).
      apply cancellation_ID in H0.
      tauto.
  Qed.
             
End Integral_domain_theorems.
