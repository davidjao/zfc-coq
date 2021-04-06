Require Export sets.

(* Short proof of Russell's paradox. *)

Section Russell's_paradox.

  Hypothesis Universal_comprehension : ∀ P, ∃ x, ∀ y, y ∈ x ↔ P y.
  Hypothesis Universal_set : ∃ x, ∀ y, y ∈ x.

  (* Proof of False from Frege's universal comprehension axiom. *)
  Theorem UC_False : False.
  Proof.
    elim (Universal_comprehension (λ x, x ∉ x)) => [x /(_ x)] // [H H0].
    elim (classic (x ∈ x)) => [/[dup] /H | /[dup] /H0] //.
  Qed.

  (* Proof of False from universal set axiom. *)
  Theorem US_False : False.
  Proof.
    move: Universal_set => [X H].
    elim (classic ({x in X | x ∉ x} ∈ {x in X | x ∉ x})) =>
    [/[dup] H0 /Specify_classification [H1 H2] | /[dup] H0 H1] //.
    apply /H1 /Specify_classification => //.
  Qed.

  (* Proof that universal comprehension implies universal set. *)
  Theorem UC_implies_US : ∃ x, ∀ y, y ∈ x.
  Proof.
    move: (Universal_comprehension (λ x, ∀ y : set, y = y)) => [x H].
    exists x => y.
    apply /H => //.
  Qed.

  (* Proof that universal set implies universal comprehension. *)
  Theorem US_implies_UC : ∀ P, ∃ x, ∀ y, y ∈ x ↔ P y.
  Proof.
    move: Universal_set => [X H] P.
    exists {x in X | P x} => y.
    rewrite Specify_classification.
    split; auto => [[H0 H1]] //.
  Qed.

End Russell's_paradox.
