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

Section Integral_domain_construction.

  Variable ring : rings.ring.
  Notation R := (elts (Rset ring)).
  Notation "0" := (zero ring).
  Notation "1" := (one ring).
  Infix "+" := (add ring).
  Infix "-" := (sub ring).
  Infix "*" := (mul ring).
  Notation "- a" := (neg ring a).
  Infix "^" := (pow ring).

  Add Ring R_ring : (ringify ring).

  Definition has_cancellation := ∀ a b, a * b = 0 → a = 0 ∨ b = 0.
  Definition has_nontriviality := 1 ≠ 0.
  Definition is_integral_domain := has_cancellation ∧ has_nontriviality.

  Hypothesis is_ID : is_integral_domain.

  Definition integral_domain_from_ring :=
    mkID ring (Logic.proj1 is_ID) (Logic.proj2 is_ID).

End Integral_domain_construction.

Section Integral_domain_theorems.

  Variable ID : integral_domain.

  Notation ring := (ring ID).
  Notation R := (elts (Rset ring)).
  Notation "0" := (zero ring).
  Notation "1" := (one ring).
  Infix "+" := (add ring).
  Infix "-" := (sub ring).
  Infix "*" := (mul ring).
  Notation "- a" := (neg ring a).
  Infix "^" := (pow ring).

  Add Ring R_ring : (ringify ring).

  Lemma has_nontriviality_ID : has_nontriviality ring.
  Proof.
    exact (nontriviality ID).
  Qed.

  Lemma has_cancellation_ID : has_cancellation ring.
  Proof.
    exact (cancellation ID).
  Qed.

  Lemma is_integral_domain_ID : is_integral_domain ring.
  Proof.
    split; try apply has_nontriviality_ID; apply has_cancellation_ID.
  Qed.

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

  Theorem unit_nonzero : ∀ a, unit a → a ≠ 0.
  Proof.
    intros a H H0.
    subst.
    destruct H as [x H].
    apply (nontriviality ID).
    now ring_simplify in H.
  Qed.

  Theorem minus_one_nonzero : -(1) ≠ 0.
  Proof.
    intros H.
    apply (f_equal (neg ring)) in H.
    ring_simplify in H.
    contradiction (nontriviality ID).
  Qed.

End Integral_domain_theorems.
