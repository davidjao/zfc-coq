Require Export Utf8 IndefiniteDescription FunctionalExtensionality
        PropExtensionality ChoiceFacts.

(* See https://github.com/coq/coq/wiki/CoqAndAxioms for explanations. *)

(* Diaconescu's theorem: Axiom of choice implies law of the excluded middle. *)

Lemma classic : ∀ P, P ∨ ¬ P.
Proof.
  intros P.
  assert (∃ b, b = true ∨ P) as H1; assert (∃ b, b = false ∨ P) as H2; eauto.
  destruct (proj2_sig (constructive_indefinite_description _ H1)),
  (proj2_sig (constructive_indefinite_description _ H2)); auto.
  right.
  intros HP.
  assert ((λ b, b = true ∨ P) = (λ b, b = false ∨ P)) as EB.
  { extensionality x.
    firstorder using propositional_extensionality. }
  destruct EB.
  now rewrite (proof_irrelevance _ H1 H2), H in *.
Qed.

(* Strong law of the excluded middle: We can always construct P or ¬ P. *)

Theorem excluded_middle_informative : ∀ P, {P} + {¬ P}.
Proof.
  firstorder using constructive_definite_descr_excluded_middle,
  classic, constructive_definite_description.
Qed.

(* not not P implies P. Requires law of the excluded middle. *)

Lemma NNPP : ∀ P, ¬ ¬ P → P.
Proof.
  intros P H.
  now destruct (classic P).
Qed.
