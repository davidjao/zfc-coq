Set Warnings "-ambiguous-paths".
Require Export rings.

Record integral_domain :=
  mkID {
      ring where
      "a + b" :=
        (add ring a b)
          and "a * b" :=
        (mul ring a b)
          and "0" :=
          (zero ring)
            and "1" :=
            (one ring);
      cancellation : ∀ a b, a * b = 0 → a = 0 ∨ b = 0;
      nontriviality : 1 ≠ 0;
    }.

Section Integral_domain_theorems.

  Variable ID : integral_domain.

  Notation Ring := (ring ID).
  Notation R := (elts (Rset Ring)).
  Notation "0" := (zero Ring).
  Notation "1" := (one Ring).
  Infix "+" := (add Ring).
  Infix "-" := (sub Ring).
  Infix "*" := (mul Ring).
  Notation "- a" := (neg Ring a).
  Infix "^" := (pow Ring).

  Add Ring R_ring : (ringify Ring).

  Lemma ne0_cancellation : ∀ a b, a ≠ 0 → b ≠ 0 → a * b ≠ 0.
  Proof.
    intros a b H H0 H1.
    now apply cancellation in H1 as [H1 | H1].
  Qed.

  Theorem cancellation_mul_l : ∀ a b c, a ≠ 0 → a * b = a * c → b = c.
  Proof.
    intros a b c H H0.
    assert (a * (b - c) = 0) as H1 by ring [H0].
    apply cancellation in H1 as [H1 | H1]; intuition.
    apply cancellation_0_add in H1.
    ring [H1].
  Qed.

  Theorem cancellation_mul_r : ∀ a b c, a ≠ 0 → b * a = c * a → b = c.
  Proof.
    eauto using M1, eq_trans, cancellation_mul_l.
  Qed.

  Theorem pow_ne_0 : ∀ a b, a ≠ 0 → a^b ≠ 0.
  Proof.
    induction b using Induction; intros H.
    - rewrite pow_0_r.
      auto using (nontriviality ID).
    - rewrite pow_succ_r.
      intros H0.
      contradiction (IHb H).
      apply cancellation in H0.
      tauto.
  Qed.

End Integral_domain_theorems.
