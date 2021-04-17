Require Export Utf8 IndefiniteDescription FunctionalExtensionality
        PropExtensionality ChoiceFacts ssrfun ssreflect ssrbool.

(* See https://github.com/coq/coq/wiki/CoqAndAxioms for explanations. *)

(* Diaconescu's theorem: Axiom of choice implies law of the excluded middle. *)

Lemma classic : ∀ P, P ∨ ¬ P.
Proof.
  move=> P.
  have H: ∃ b, b = true ∨ P; have H0: ∃ b, b = false ∨ P; eauto.
  elim (proj2_sig (constructive_indefinite_description _ H));
    elim (proj2_sig (constructive_indefinite_description _ H0)); auto.
  right => HP.
  have EB: (λ b, b = true ∨ P) = (λ b, b = false ∨ P).
  { extensionality x.
    firstorder using propositional_extensionality. }
  destruct EB.
  move: H1 H2; rewrite (proof_irrelevance _ H H0) => -> //.
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
  move: classic => /[swap] P /[swap] H /(_ P) => [[? | ?]] //.
Qed.

Arguments constructive_indefinite_description {A P}.

Notation "'If' P 'then' v1 'else' v2" :=
  match (excluded_middle_informative P) with
   | left _ => v1
   | right _ => v2
  end (at level 200, right associativity) : type_scope.
