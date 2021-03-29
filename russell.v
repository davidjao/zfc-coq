Require Export sets.

(* Short proof of Russell's paradox. *)

Section Russell's_paradox.

  Hypothesis Universal_comprehension : ∀ P, ∃ x, ∀ y, y ∈ x ↔ P y.
  Hypothesis Universal_set : ∃ x, ∀ y, y ∈ x.

  (* Proof of False from Frege's universal comprehension axiom. *)
  Theorem UC_False : False.
  Proof.
    destruct (Universal_comprehension (λ x, x ∉ x)) as [x H].
    destruct (H x) as [H0 H1], (classic (x ∈ x)) as [H2 | H2].
    - contradiction H0.
    - contradiction (H1 H2).
  Qed.

  (* Proof of False from universal set axiom. *)
  Theorem US_False : False.
  Proof.
    destruct Universal_set as [X H].
    destruct (classic ({x in X | x ∉ x} ∈ {x in X | x ∉ x})).
    - apply Specify_classification in H0 as H1.
      tauto.
    - pose proof H0 as H1.
      contradict H1.
      now apply Specify_classification.
  Qed.

  (* Proof that universal comprehension implies universal set. *)
  Theorem UC_implies_US : ∃ x, ∀ y, y ∈ x.
  Proof.
    destruct (Universal_comprehension (λ x, ∀ y : set, y = y)) as [x H].
    exists x.
    intros y.
    now rewrite H.
  Qed.

  (* Proof that universal set implies universal comprehension. *)
  Theorem US_implies_UC : ∀ P, ∃ x, ∀ y, y ∈ x ↔ P y.
  Proof.
    move: Universal_set => [X H] P.
    exists {x in X | P x}.
    split; rewrite Specify_classification//; tauto.
  Qed.

End Russell's_paradox.
