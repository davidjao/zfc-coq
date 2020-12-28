Require Export sets.

(* Short proof of Russell's paradox. *)

Axiom Frege : ∀ P, ∃ x, ∀ y, y ∈ x ↔ P y.

Goal False.
Proof.
  destruct (Frege (λ x, x ∉ x)) as [x H].
  destruct (H x) as [H0 H1], (classic (x ∈ x)) as [H2 | H2].
  - contradiction H0.
  - contradiction (H1 H2).
Qed.
