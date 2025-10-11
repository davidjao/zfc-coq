Set Warnings "-ambiguous-paths,-non-reference-hint-using".
Require Export rationals.

Notation "6" := (3+3)%Z.

Goal 2/3 = 4/6.
Proof.
  apply Qequiv; last ring;
    (move: (lt_irrefl ℤ_order 0%Z) => /[swap] {2}<- [] /=);
    repeat apply (ordered_rings.O0 ℤ_order);
    auto using (ordered_rings.zero_lt_1 ℤ_order).
Qed.
