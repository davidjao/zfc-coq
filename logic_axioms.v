Require Export Utf8 Constructive_sets IndefiniteDescription
        FunctionalExtensionality PropExtensionality ChoiceFacts.

(* See https://github.com/coq/coq/wiki/CoqAndAxioms for explanations. *)

(* Lambda calculus version of ∀ A B, A ⊂ B ∧ B ⊂ A → A = B. *)
Theorem Extensionality_Ensembles :
  ∀ (U : Type) (A B : Ensemble U), Same_set U A B → A = B.
Proof.
  intros U A B [H H0].
  apply functional_extensionality_dep.
  intros x.
  apply propositional_extensionality.
  firstorder.
Qed.

(* Diaconescu's theorem: Axiom of choice implies law of the excluded middle. *)
Lemma classic : ∀ (P : Prop), P ∨ ¬ P.
Proof.
  intros P.
  assert (∃ b, b = true ∨ P) as H1 by eauto.
  assert (∃ b, b = false ∨ P) as H2 by eauto.
  destruct (proj2_sig (constructive_indefinite_description _ H1)),
  (proj2_sig (constructive_indefinite_description _ H2)); auto.
  right.
  intros HP.
  assert ((λ b, b = true ∨ P) = (λ b, b = false ∨ P)) as EB
      by firstorder using Extensionality_Ensembles.
  destruct EB.
  rewrite (proof_irrelevance _ H1 H2) in *.
  congruence.
Qed.

(* Strong law of the excluded middle: We can always construct P or ¬ P. *)

Theorem excluded_middle_informative : ∀ P : Prop, {P} + {¬ P}.
Proof.
  exact (constructive_definite_descr_excluded_middle
           constructive_definite_description classic).
Qed.

(* not not P implies P. Requires law of the excluded middle. *)
Lemma NNPP : ∀ P : Prop, ¬ ¬ P → P.
Proof.
  intros P H.
  now destruct (classic P).
Qed.
