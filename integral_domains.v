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
  Infix "*" := (mul_R R).
  Notation "- a" := (neg_R R a).

  Lemma ne0_cancellation : ∀ a b, a ≠ 0 → b ≠ 0 → a * b ≠ 0.
  Proof.
    intros a b H H0 H1.
    now apply cancellation_ID in H1 as [H1 | H1].
  Qed.

End Integral_domain_theorems.
