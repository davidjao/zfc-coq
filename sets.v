Require Export logic_axioms Basics.

(* Beginning of axioms. *)

Parameter set : Type.
Parameter IN: set → set → Prop.
Declare Scope set_scope.
Delimit Scope set_scope with set.
Open Scope set_scope.
Bind Scope set_scope with set.

Infix "∈" := IN (at level 75) : set_scope.
Notation "a ∉ b" := (¬ a ∈ b) (at level 75) : set_scope.

(* Axiom list from https://math.stackexchange.com/questions/916072/ *)

Axiom Extensionality : ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y.
Axiom Regularity : ∀ x, (∃ a, a ∈ x) → ∃ y, y ∈ x ∧ ¬ ∃ z, (z ∈ y ∧ z ∈ x).
Axiom Replacement : ∀ A R, (∀ x, x ∈ A → exists ! y, R x y) →
                           ∃ B, ∀ y, y ∈ B ↔ ∃ x, x ∈ A ∧ R x y.
Axiom Union : ∀ F, ∃ A, ∀ x y, (x ∈ y ∧ y ∈ F) → x ∈ A.
Axiom Powerset : ∀ x, ∃ y, ∀ z, (∀ u, u ∈ z → u ∈ x) → z ∈ y.
Axiom Infinity : ∃ X, (∃ y, (∀ z, z ∉ y) ∧ y ∈ X) ∧ ∀ x,
      x ∈ X → ∃ y, y ∈ X ∧ ∀ z, (z ∈ y ↔ z ∈ x ∨ z = x).

(* End of axioms. *)

Record elts S := mkSet { elt_to_set :> set; elts_in_set : elt_to_set ∈ S; }.
Arguments mkSet {S} {elt_to_set}.
Arguments elt_to_set {S}.
Arguments elts_in_set {S}.

Theorem set_proj_injective :
  ∀ X (n m : elts X), (n : set) = (m : set) → n = m.
Proof.
  move=> S [n N] [m M] /= H.
  move: H N M -> => N M.
  apply /f_equal /proof_irrelevance.
Qed.

Theorem reify : ∀ {x} {S} (H : x ∈ S), x = (mkSet H : elts S).
Proof.
  auto.
Qed.

Theorem Empty_Set : ∃ w, ∀ x, x ∉ w.
Proof.
  move: Infinity => [x [[w [H _]] _]].
  eauto.
Qed.

Definition empty_set : set.
Proof.
  elim: (constructive_indefinite_description Empty_Set) => [w] //.
Defined.

Notation "∅" := empty_set : set_scope.

Theorem Empty_set_classification : ∀ w, w ∉ ∅.
Proof.
  rewrite /empty_set.
    by elim: constructive_indefinite_description.
Qed.

Theorem Nonempty_classification : ∀ y, y ≠ ∅ ↔ ∃ x, x ∈ y.
Proof.
  split => [H | [x] /[swap] -> /Empty_set_classification] //.
  apply NNPP => H0.
  apply /H /Extensionality => z.
  split => [H1 | /Empty_set_classification] //.
  contradict H0.
  eauto.
Qed.

(* The axiom of specification is a theorem in ZFC under classical logic. *)
Theorem Specification : ∀ z p, ∃ y, ∀ x, (x ∈ y ↔ (x ∈ z ∧ (p x))).
Proof.
  move=> z p.
  elim (classic (∃ x, x ∈ z ∧ p x)) => [[e [H H0]] | H].
  - elim (Replacement z (λ x y, p x ∧ x = y ∨ ¬ p x ∧ e = y)) => x H1.
    + exists x => x0.
      split => [ /H1 [w [H2 [ [H3 <-] | [H3 <-] ]]] | ] //.
      rewrite H1.
      intuition eauto.
    + elim (classic (p x)); [ exists x | exists e ]; split; intuition tauto.
  - exists ∅ => x.
    split => [/Empty_set_classification | H0] //.
    contradict H.
    eauto.
Qed.

Definition specify : set → (set → Prop) → set.
Proof.
  move=> A p.
  elim (constructive_indefinite_description (Specification A p)) => [S] //.
Defined.

Definition specify_lift (A : set) (p : elts A → Prop) : set → Prop.
Proof.
  move=> a.
  elim (excluded_middle_informative (a ∈ A)) => H.
  - exact (p (mkSet H)).
  - exact False.
Defined.

Definition specify_type (A : set) (p : elts A → Prop) : set.
Proof.
  elim (constructive_indefinite_description
          (Specification A (specify_lift A p))) => [S] //.
Defined.

Theorem despecify :
  ∀ A (p : elts A → Prop) (x : elts A), specify_lift A p x = p x.
Proof.
  rewrite /specify_lift => A p x.
  elim excluded_middle_informative => a /=.
  - by apply /f_equal /set_proj_injective.
  - exfalso; eauto using elts_in_set.
Qed.

Notation "{ x 'in' A | P }" := (specify A (λ x, P)) : set_scope.

Notation "{ x 'of' 'type' A | P }" := (specify_type A (λ x, P)) : set_scope.

Definition subset a b := ∀ x, x ∈ a → x ∈ b.
Infix "⊂" := subset (at level 70) : set_scope.

Theorem replacement_construction : ∀ S (f : elts S → set),
  ∃ X, ∀ x, x ∈ X ↔ ∃ s, f s = x.
Proof.
  move=> S f.
  elim (Replacement S (λ x y, ∃ s, f s = y ∧ x = s)) => X H.
  - exists X => x.
    rewrite H.
    split => [[_] [_ [s [H0 _]]] | [[s H0]] H1]; eauto using elts_in_set.
  - exists (f (mkSet H)).
    split; eauto => _ [s [<- H1]].
      by apply /f_equal /set_proj_injective.
Qed.

Definition replacement (S : set) (f : elts S → set) : set.
Proof.
  elim (constructive_indefinite_description (replacement_construction S f))
  => [X H] //.
Defined.

Notation "{ f '|' x 'in' S }" := (replacement S (λ x, f)).

Theorem replacement_classification :
  ∀ S (f : elts S → set) z, z ∈ {f x | x in S} ↔ ∃ s, z = f s.
Proof.
  split; rewrite /replacement; elim constructive_indefinite_description =>
  x i /=; rewrite i; move => [s]; eauto.
Qed.

Definition P : set → set.
Proof.
  move=> x.
  elim (constructive_indefinite_description (Powerset x)) => [y H].
  exact ({s in y | s ⊂ x}).
Defined.

Theorem Empty_set_is_subset : ∀ X, ∅ ⊂ X.
Proof.
  move=> X z /Empty_set_classification //.
Qed.

Theorem Set_is_subset : ∀ X, X ⊂ X.
Proof.
  firstorder.
Qed.

Theorem Powerset_classification : ∀ X x, x ∈ P X ↔ x ⊂ X.
Proof.
  rewrite /P /specify => X x.
  repeat (elim constructive_indefinite_description => /= ?).
  split; rewrite p; firstorder.
Qed.

Theorem Empty_set_in_powerset : ∀ X, ∅ ∈ P X.
Proof.
  firstorder using Powerset_classification, Empty_set_is_subset.
Qed.

Theorem Set_in_powerset : ∀ X, X ∈ P X.
Proof.
  firstorder using Powerset_classification, Set_is_subset.
Qed.

Theorem Powerset_nonempty : ∀ x, ∅ ≠ P x.
Proof.
  move: Empty_set_classification => /[swap] x /[swap] -> /(_ x) => H.
  apply /H /Set_in_powerset.
Qed.

Theorem Subset_transitive : ∀ X Y Z, X ⊂ Y → Y ⊂ Z → X ⊂ Z.
Proof.
  move=> X Y Z H H0 x /H /H0 //.
Qed.

Theorem Subset_equality : ∀ A B, A ⊂ B → B ⊂ A → A = B.
Proof.
  move=> A B H H0.
  apply /Extensionality; intuition.
Qed.

Theorem Subset_equality_iff : ∀ A B, (A ⊂ B ∧ B ⊂ A) ↔ A = B.
Proof.
  split => H; subst; firstorder using Subset_equality, Set_is_subset.
Qed.

Theorem Subset_extensionality :
  ∀ A B, A = B ↔ (∀ X, X ⊂ A ↔ X ⊂ B).
Proof.
  split => [-> X| H] //.
  apply /Subset_equality_iff.
  rewrite H -H.
  eauto using Set_is_subset.
Qed.

Lemma Subset_of_subsets_of_emptyset : ∀ a, a ∈ P (P ∅) → a = ∅ ∨ a = P ∅.
Proof.
  move=> a.
  (elim (classic (a = ∅)); try tauto) => H /Powerset_classification => H0.
  apply or_intror, Subset_equality_iff, conj;
    auto => z /Powerset_classification H1.
  suff -> : z = ∅.
  - move: H H0 => /Nonempty_classification => [[x H]].
    move: (H) => /[swap] /[apply] /Powerset_classification => H0.
    suff -> : ∅ = x => //.
    apply Subset_equality_iff, conj; auto using Empty_set_is_subset.
  - apply Subset_equality_iff, conj; auto using Empty_set_is_subset.
Qed.

(* The axiom of pairing is a theorem in ZFC under classical logic. *)
Theorem Pairing : ∀ x y, ∃ z, ((x ∈ z) ∧ (y ∈ z)).
Proof.
  move=> x y.
  elim (Replacement (P (P ∅)) (λ a b, ∅ = a ∧ x = b ∨ P ∅ = a ∧ y = b)) => z.
  - exists z; split; apply /H;
      eauto using Empty_set_in_powerset, Set_in_powerset.
  - move => /Subset_of_subsets_of_emptyset; elim; [ exists x | exists y ];
              split; intuition; subst; by contradiction (Powerset_nonempty ∅).
Qed.

Definition pair : set → set → set.
Proof.
  move=> x y.
  elim (constructive_indefinite_description (Pairing x y)) => z H.
  exact ({t in z | t = x ∨ t = y}).
Defined.

Notation " { x , y } " := (pair x y) : set_scope.
Notation " { x } " := (pair x x) : set_scope.

Definition union : set → set.
Proof.
  move=> F.
  elim (constructive_indefinite_description (Union F)) => A H.
  exact ({x in A | ∃ y, (x ∈ y ∧ y ∈ F)}).
Defined.

Notation "⋃ x" := (union x) (at level 60) : set_scope.

Definition pairwise_union A B := (⋃ {A, B}).

Infix "∪" := pairwise_union (at level 60) : set_scope.

Definition succ w := w ∪ {w, w}.

Definition Inductive X := ∀ y, y ∈ X → succ y ∈ X.

Lemma neq_sym : ∀ A (a b : A), a ≠ b ↔ b ≠ a.
Proof.
  split => H; now contradict H.
Qed.

Theorem Specify_classification : ∀ A P x, x ∈ {x in A | P x} ↔ x ∈ A ∧ P x.
Proof.
  rewrite /specify => A p x.
  repeat elim constructive_indefinite_description => //.
Qed.

Theorem Specify_subset : ∀ A p, {x in A | p x} ⊂ A.
Proof.
  now move=> A p x /Specify_classification.
Qed.

Theorem Specify_type_classification :
  ∀ A p x, p x ∧ x ∈ A ↔ x ∈ {x of type A | p x}.
Proof.
  move=> A p x.
  rewrite Specify_classification.
  split; intuition; by rewrite -> ? (reify H1), ? (reify H0), despecify in *.
Qed.

Theorem Specify_type_subset : ∀ A P, {x of type A | P x} ⊂ A.
Proof.
  now move=> A P x /Specify_classification.
Qed.

Lemma Pairing_classification : ∀ x y z, z ∈ {x,y} ↔ (z = x ∨ z = y).
Proof.
  rewrite /pair => x y z.
  repeat elim constructive_indefinite_description => ? /=.
  rewrite Specify_classification; intuition; congruence.
Qed.

Theorem Pairing_nonempty : ∀ x y, {x,y} ≠ ∅.
Proof.
  move: Empty_set_classification => /[swap] x /[swap] y /[swap] <- /(_ x) => H.
  apply /H /Pairing_classification /or_introl /eq_refl.
Qed.

Theorem Pairing_comm : ∀ x y, {x,y} = {y,x}.
Proof.
  move=> x y.
  apply /Extensionality => z.
  rewrite ? Pairing_classification; tauto.
Qed.

Lemma in_singleton : ∀ x, x ∈ {x,x}.
Proof.
  move=> x.
  apply /Pairing_classification /or_introl => //.
Qed.

Lemma Singleton_classification : ∀ x y, y ∈ {x,x} ↔ y = x.
Proof.
  move=> x y.
  rewrite Pairing_classification; tauto.
Qed.

Definition proper_subset a b := a ⊂ b ∧ a ≠ b.
Infix "⊊" := proper_subset (at level 70) : set_scope.

Lemma not_proper_subset_inhab : ∀ x y, ¬ x ⊊ y → x ≠ y → ∃ z, z ∈ x ∧ z ∉ y.
Proof.
  move=> x y H H0.
  apply NNPP => H1.
  apply H, conj; auto => z H2.
  apply NNPP => H3.
  eauto.
Qed.

Theorem subset_subsetneq_trans : ∀ A B C, A ⊂ B → B ⊊ C → A ⊊ C.
Proof.
  move=> A B C H [H0 H1].
  split => [a /H /H0 | ] //.
  move: H => /[swap] -> H.
    by apply /H1 /Subset_equality_iff.
Qed.

Theorem subsetneq_subset_trans : ∀ A B C, A ⊊ B → B ⊂ C → A ⊊ C.
Proof.
  move=> A B C [H H0] H1.
  split => [a /H /H1 | ] //.
  move: H1 => /[swap] <- H1.
    by apply /H0 /Subset_equality_iff.
Qed.

Lemma proper_subset_inhab : ∀ x y, x ⊊ y → ∃ z, z ∈ y ∧ z ∉ x.
Proof.
  move=> x y [H H0].
  apply NNPP => H1.
  apply /H0 /Subset_equality_iff.
  split; auto => z H2.
  apply NNPP => H3.
  eauto.
Qed.

Theorem Union_classification : ∀ x C, x ∈ ⋃ C ↔ ∃ X, X ∈ C ∧ x ∈ X.
Proof.
  rewrite /union /specify => x C.
  repeat (elim: constructive_indefinite_description => /= ?).
  split; rewrite p; firstorder.
Qed.

Theorem Empty_union : ⋃ ∅ = ∅.
Proof.
  apply Subset_equality_iff, conj; auto using Empty_set_is_subset => x.
  rewrite Union_classification => [[y [H H0]]].
  move: H => /Empty_set_classification //.
Qed.

Lemma Pairwise_union_classification :
  ∀ A B x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B.
Proof.
  ((split; rewrite /pairwise_union Union_classification) =>
   [[X] | [H | H]]; last 1 [exists A | exists B];
   rewrite Pairing_classification) => [[[<- | <-]] | | ]; tauto.
Qed.

Lemma Pairing_union_singleton : ∀ x y, {x,y} = {x,x} ∪ {y,y}.
Proof.
  move=> x y.
  apply /Extensionality => z.
  rewrite ? Pairwise_union_classification ? Singleton_classification
          ? Pairing_classification //.
Qed.

Theorem Singleton_union : ∀ A, ⋃ {A, A} = A.
Proof.
  move=> A.
  apply /Extensionality => z.
  rewrite ? Pairwise_union_classification; tauto.
Qed.

Theorem Union_comm : ∀ A B, A ∪ B = B ∪ A.
Proof.
  move=> A B.
  apply /Extensionality => z.
  rewrite ? Pairwise_union_classification; tauto.
Qed.

Theorem Union_assoc : ∀ A B C, A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof.
  move=> A B C.
  apply /Extensionality => z.
  rewrite ? Pairwise_union_classification; tauto.
Qed.

Theorem Union_empty : ∀ A, A ∪ ∅ = A.
Proof.
  move=> A.
  apply /Extensionality => z.
  rewrite Pairwise_union_classification;
    intuition (contradiction (Empty_set_classification z)).
Qed.

Theorem Union_idempotent : ∀ A, A ∪ A = A.
Proof.
  move=> A.
  apply /Extensionality => z.
  rewrite Pairwise_union_classification; tauto.
Qed.

Theorem Union_subset : ∀ A B, A ⊂ B ↔ A ∪ B = B.
Proof.
  move=> A B.
  rewrite <-Subset_equality_iff.
  (split => [H | [H H0]]; repeat split) =>
  x; rewrite ? Pairwise_union_classification; try tauto;
    firstorder using Pairwise_union_classification.
Qed.

Theorem Union_left : ∀ A B, A ⊂ A ∪ B.
Proof.
  move=> A B x.
  rewrite Pairwise_union_classification; tauto.
Qed.

Theorem Union_right : ∀ A B, B ⊂ A ∪ B.
Proof.
  move=> A B x.
  rewrite Pairwise_union_classification; tauto.
Qed.

Definition intersection X := {y in ⋃ X | ∀ x, x ∈ X → y ∈ x}.

Notation "⋂ x" := (intersection x) (at level 60) : set_scope.

Definition pairwise_intersection A B := (⋂ {A, B}).

Infix "∩" := pairwise_intersection (at level 60) : set_scope.

Theorem Intersection_classification : ∀ C,
    C ≠ ∅ → ∀ x, x ∈ ⋂ C ↔ ∀ X, X ∈ C → x ∈ X.
Proof.
  move=> C => /[swap] x /Nonempty_classification => [[z H]].
  rewrite /intersection /union /specify /=.
  (repeat (elim constructive_indefinite_description => ? /=)) => H0 H1.
  (split; rewrite H0 H1) => [[_ H2] X | H2]; intuition eauto.
Qed.

Theorem Pairwise_intersection_classification :
  ∀ A B x, x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B.
Proof.
  rewrite /pairwise_intersection => A B x.
  rewrite Intersection_classification; auto using Pairing_nonempty.
  (split => [/[dup] /(_ A) /[swap] /(_ B)| [H H0] z];
            rewrite ? Pairing_classification) => [| [-> | ->]]; tauto.
Qed.

Theorem Pairing_intersection_disjoint : ∀ x y, x ≠ y ↔ {x,x} ∩ {y,y} = ∅.
Proof.
  move=> x y.
  split => H.
  - apply /Extensionality => z.
    split => [/Pairwise_intersection_classification |
              /Empty_set_classification] //.
    rewrite ? Singleton_classification; elim => -> //.
  - move: Empty_set_classification H =>
    /(_ y) /[swap] <- /[swap] -> /Pairwise_intersection_classification.
    rewrite Singleton_classification; tauto.
Qed.

Theorem Empty_intersection : (⋂ ∅ = ∅).
Proof.
  rewrite /intersection /specify /sig_rect.
  repeat (elim constructive_indefinite_description => /=) => x H.
  apply /Extensionality => z.
  rewrite H Empty_union.
  split => [[/Empty_set_classification] | /Empty_set_classification] //.
Qed.

Theorem Intersection_empty : ∀ A, A ∩ ∅ = ∅.
Proof.
  move=> A.
  apply /Extensionality => z.
  rewrite Pairwise_intersection_classification.
  split => [[_] | /Empty_set_classification] //.
Qed.

Theorem Intersection_comm : ∀ A B, A ∩ B = B ∩ A.
Proof.
  move=> A B.
  apply /Extensionality => z.
  rewrite ? Pairwise_intersection_classification; tauto.
Qed.

Theorem Intersection_assoc : ∀ A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof.
  move=> A B C.
  apply /Extensionality => z.
  rewrite ? Pairwise_intersection_classification; tauto.
Qed.

Theorem Intersection_idempotent : ∀ A, A ∩ A = A.
Proof.
  move=> A.
  apply /Extensionality => z.
  rewrite Pairwise_intersection_classification; tauto.
Qed.

Theorem Intersection_subset : ∀ A B, A ⊂ B ↔ A ∩ B = A.
Proof.
  move=> A B.
  rewrite -Subset_equality_iff.
  (repeat split) => [z | z | [H H0] z];
                      rewrite ? Pairwise_intersection_classification;
                      auto; try tauto.
  move: Pairwise_intersection_classification =>
  /[swap] /H0 /[swap] /[apply] [[H1 H2]] //.
Qed.

Theorem Intersection_union : ∀ A B C, A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
Proof.
  move=> A B C.
  apply /Extensionality => z.
  repeat rewrite ? Pairwise_intersection_classification
         ? Pairwise_union_classification; tauto.
Qed.

Theorem Union_intersection : ∀ A B C, A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
Proof.
  move=> A B C.
  apply /Extensionality => z.
  repeat rewrite ? Pairwise_intersection_classification
         ? Pairwise_union_classification; tauto.
Qed.

Theorem Halmos_4_1 : ∀ A B C, (A ∩ B) ∪ C = A ∩ (B ∪ C) ↔ C ⊂ A.
Proof.
  split => [/Subset_equality_iff /[swap] x [/(_ x)H H0] | H];
             [ | apply /Extensionality => z; move: H => /(_ z) ];
             repeat rewrite -> ? Pairwise_intersection_classification,
             ? Pairwise_union_classification in *; tauto.
Qed.

Definition complement A B := {x in A | x ∉ B}.

Infix "\" := complement (at level 45) : set_scope.

Theorem Complement_classification : ∀ A B x, x ∈ A \ B ↔ x ∈ A ∧ x ∉ B.
Proof.
  move=> A B x.
  rewrite /complement /specify.
    by repeat elim constructive_indefinite_description => /=.
Qed.

Theorem Complement_subset : ∀ A B, A ⊂ B ↔ A \ B = ∅.
Proof.
  split => [H | /[swap] x /[swap] H].
  - apply /Extensionality => z; rewrite Complement_classification;
                              firstorder using Empty_set_classification.
  - move: Empty_set_classification =>
    /(_ x) /[swap] <- /Complement_classification H0; apply NNPP; tauto.
Qed.

Theorem Complement_intersection : ∀ A B, A \ (A \ B) = A ∩ B.
Proof.
  move=> A B.
  apply /Extensionality => z.
  rewrite Pairwise_intersection_classification ? Complement_classification.
  split => H; move: classic => /(_ (z ∈ B)); tauto.
Qed.

Theorem Intersection_complement : ∀ A B C, A ∩ (B \ C) = (A ∩ B) \ (A ∩ C).
Proof.
  move=> A B C.
  apply /Extensionality => z.
  repeat rewrite ? Pairwise_intersection_classification
         ? Complement_classification; tauto.
Qed.

Definition ordered_pair x y := {{x,x},{x,y}}.

Notation " ( x , y ) " := (ordered_pair x y) : set_scope.

Theorem Ordered_pair_iff : ∀ a b c d, (a, b) = (c, d) ↔ (a = c ∧ b = d).
Proof.
  rewrite /ordered_pair => a b c d.
  split => [ | [-> ->]] //.
  wlog: a b c d / a = c => [H /[dup] H0 /(H a) H1 | -> H].
  - apply H1.
    have: {a,a} ∈ {{c,c}, {c,d}}.
    { move: H0 <-; apply /Pairing_classification /or_introl => //. }
    move => /Pairing_classification =>
    [[H2 | H2]]; symmetry; apply /Singleton_classification;
      rewrite H2; apply /Pairing_classification; auto.
  - have: {c,b} ∈ {{c,c}, {c,d}}.
    { move: H <-; apply /Pairing_classification /or_intror => //. }
    move => /Pairing_classification =>
    [[/Subset_equality_iff [/(_ b) H0 _] |
      /Subset_equality_iff [/(_ b) H0 /(_ d) H1]]].
    + have: {c,d} ∈ {{c,c}, {c,b}}.
      { move: H ->; apply /Pairing_classification /or_intror => //. }
      move => /Pairing_classification =>
      [[/Subset_equality_iff [/(_ d) H1 _] |
        /Subset_equality_iff [/(_ d) H1 _]]];
        rewrite -> ? Pairing_classification in *; intuition congruence.
    + rewrite -> ? Pairing_classification in *; intuition congruence.
Qed.

Definition product A B :=
  {x in P (P (A ∪ B)) | ∃ a b, a ∈ A ∧ b ∈ B ∧ x = (a,b)}.

Infix "×" := product (at level 60) : set_scope.

Theorem Product_classification : ∀ A B x,
    x ∈ A × B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ x = (a,b).
Proof.
  move=> A B x.
  rewrite /product Specify_classification.
  split => [[H [a [b [H0 [H1 H2]]]]] | [a [b [H0 [H1 ->]]]]];
             repeat split; eauto; apply /Powerset_classification =>
  y /Pairing_classification [->|->]; apply /Powerset_classification =>
  z /Pairing_classification [->|->]; apply Pairwise_union_classification; tauto.
Qed.

Definition proj1 : set → set → set → set.
Proof.
  move=> A B x.
  elim (excluded_middle_informative (x ∈ A × B)) => H.
  - move: H => /Product_classification /constructive_indefinite_description
                [a] /constructive_indefinite_description [b] H0.
    exact a.
  - exact ∅.
Defined.

Definition proj2 : set → set → set → set.
Proof.
  move=> A B x.
  elim (excluded_middle_informative (x ∈ A × B)) => H.
  - move: H => /Product_classification /constructive_indefinite_description
                [a] /constructive_indefinite_description [b] H0.
    exact b.
  - exact ∅.
Defined.

Theorem proj1_eval : ∀ A B a b, a ∈ A → b ∈ B → proj1 A B (a,b) = a.
Proof.
  move=> A B a b H H0.
  rewrite /proj1.
  elim excluded_middle_informative => /= // => H1.
  - repeat (elim constructive_indefinite_description => >).
    rewrite Ordered_pair_iff; intuition congruence.
  - contradict H1; apply Product_classification; eauto.
Qed.

Theorem proj2_eval : ∀ A B a b, a ∈ A → b ∈ B → proj2 A B (a,b) = b.
Proof.
  move=> A B a b H H0.
  rewrite /proj2.
  elim excluded_middle_informative => /= // => H1.
  - repeat (elim constructive_indefinite_description => >).
    rewrite Ordered_pair_iff; intuition congruence.
  - contradict H1; apply Product_classification; eauto.
Qed.

Section Projections.

  Context {A B : set}.

  Definition π1 : elts (A × B) → elts A.
  Proof.
    move=> z.
    move: (elts_in_set z) => /Product_classification
    => /constructive_indefinite_description [a] =>
    /constructive_indefinite_description [b] [H0 [H1 H2]].
    exact (mkSet H0).
  Defined.

  Definition π2 : elts (A × B) → elts B.
  Proof.
    move=> z.
    move: (elts_in_set z) => /Product_classification
    => /constructive_indefinite_description [a] =>
    /constructive_indefinite_description [b] [H0 [H1 H2]].
    exact (mkSet H1).
  Defined.

  Theorem π1_action :
    ∀ a b (Ha : a ∈ A) (Hb : b ∈ B)
      (H : (mkSet Ha : elts A, mkSet Hb : elts B) ∈ A × B),
      π1 (mkSet H) = mkSet Ha.
  Proof.
    rewrite /π1 => a b Ha Hb H.
    elim constructive_indefinite_description => x [z [p [p0 p1]]].
    elim constructive_indefinite_description => y [q [q0 q1]].
    move: p1 q1 q => /Ordered_pair_iff /[swap] /Ordered_pair_iff [<- _] _ q.
    apply /f_equal /proof_irrelevance.
  Qed.

  Theorem π2_action :
    ∀ a b (Ha : a ∈ A) (Hb : b ∈ B)
      (H : (mkSet Ha : elts A, mkSet Hb : elts B) ∈ A × B),
      π2 (mkSet H) = mkSet Hb.
  Proof.
    rewrite /π2 => a b Ha Hb H.
    elim constructive_indefinite_description => x [z [p [p0 p1]]].
    elim constructive_indefinite_description => y [q [q0 q1]].
    move: p1 q1 q0 => /Ordered_pair_iff /[swap] /Ordered_pair_iff [_ <-] _ q0.
    apply /f_equal /proof_irrelevance.
  Qed.

  Theorem π_image : ∀ z, (π1 z, π2 z) = z.
  Proof.
    rewrite /π1 /π2 => z.
    elim constructive_indefinite_description => x [p [p0 [p1 p2]]].
    elim constructive_indefinite_description => y [q [q0 q1]].
    rewrite q1 Ordered_pair_iff //.
  Qed.

End Projections.

Theorem Product_union_distr_l : ∀ A B X, (A ∪ B) × X = (A × X) ∪ (B × X).
Proof.
  move=> A B X.
  apply /Extensionality => z.
  rewrite ? Pairwise_union_classification ? Product_classification.
  split => [[a [b [/Pairwise_union_classification [H | H] [H0 ->]]]]
           | [[a [b [H [H0 ->]]]] | [a [b [H [H0 ->]]]]]];
             [ left | right | | ]; eauto; exists a, b;
               rewrite Pairwise_union_classification; tauto.
Qed.

Theorem Product_intersection :
  ∀ A B X Y, (A ∩ B) × (X ∩ Y) = (A × X) ∩ (B × Y).
Proof.
  move=> A B X Y.
  apply Extensionality => z.
  rewrite ? Pairwise_intersection_classification ? Product_classification.
  split => [[a [b [H [H0 H1]]]] | [[a [b [H [H0 ->]]]] [c [d [H1 [H2 H3]]]]]];
             [ | exists a, b ]; rewrite -> ? Ordered_pair_iff,
                                ? Pairwise_intersection_classification
               in *; intuition (eauto; congruence).
Qed.

Theorem Product_in_left : ∀ a b A B, (a, b) ∈ A × B → a ∈ A.
Proof.
  move=> a b A B /Product_classification
           [a' [b' [H [H0 /Ordered_pair_iff [->]]]]] //.
Qed.

Theorem Product_in_right : ∀ a b A B, (a, b) ∈ A × B → b ∈ B.
Proof.
  move=> a b A B /Product_classification
           [a' [b' [H [H0 /Ordered_pair_iff [_ ->]]]]] //.
Qed.

Theorem Product_intersection_distr_l :
  ∀ A B X, (A ∩ B) × X = (A × X) ∩ (B × X).
Proof.
  move=> A B X.
  rewrite -Product_intersection Intersection_idempotent //.
Qed.

Theorem Product_complement : ∀ A B X, (A \ B) × X = (A × X) \ (B × X).
Proof.
  move=> A B X.
  apply Extensionality => z.
  repeat rewrite ? Complement_classification ? Product_classification.
  split => [[a [b [/Complement_classification [H H0] [H1 ->]]]] |
            [[a [b [H [H0 H1]]]] H2]]; repeat split; eauto.
  - move: H0 => /[swap] [[x [y [H2 [H3 /Ordered_pair_iff [-> _]]]]]] //.
  - exists a, b.
    rewrite Complement_classification.
    repeat split; eauto.
    contradict H2.
    eauto.
Qed.

Theorem Empty_product_left : ∀ S, ∅ × S = ∅.
Proof.
  move=> S.
  apply Extensionality => z.
  (split; rewrite Product_classification) =>
  [[a [b [/Empty_set_classification]]] | /Empty_set_classification] //.
Qed.

Theorem Empty_product_right : ∀ S, S × ∅ = ∅.
Proof.
  move=> S.
  apply Extensionality => z.
  (split; rewrite Product_classification) =>
  [[a [b [_ [/Empty_set_classification]]]] | /Empty_set_classification] //.
Qed.

Definition quotient X R := {{y in X | (x,y) ∈ R} | x in X}.

Infix "/" := quotient : set_scope.

Theorem quotient_classification : ∀ X R s,
    s ∈ X/R ↔ s ⊂ X ∧ ∃ x, x ∈ X ∧ (∀ y, y ∈ s ↔ y ∈ X ∧ (x,y) ∈ R).
Proof.
  ((split; rewrite /quotient replacement_classification) =>
   [[σ ->] | [_ [x [H H0]]]]; repeat split) =>
  [x /Specify_classification [H _] | | ] //.
  - exists σ.
    split; auto using elts_in_set => y; rewrite Specify_classification //.
  - exists (mkSet H : elts X).
    apply Extensionality => z.
    rewrite Specify_classification H0 //.
Qed.

Definition reflexive X R := ∀ x, x ∈ X → (x,x) ∈ R.

Definition symmetric X R := ∀ x y, x ∈ X → y ∈ X → (x,y) ∈ R → (y,x) ∈ R.

Definition transitive X R := ∀ x y z,
    x ∈ X → y ∈ X → z ∈ X → (x,y) ∈ R → (y,z) ∈ R → (x,z) ∈ R.

Definition is_partition X C :=
  (⋃ C = X) ∧ (∀ c, c ∈ C → c ≠ ∅) ∧
  (∀ c1 c2, c1 ∈ C → c2 ∈ C → c1 ≠ c2 → c1 ∩ c2 = ∅).

Definition is_equivalence X R :=
  (reflexive X R) ∧ (symmetric X R) ∧ (transitive X R).

Theorem Equivalence_classes_are_partitions : ∀ X R,
    is_equivalence X R → is_partition X (X/R).
Proof.
  move=> X R [H [H0 H1]].
  (repeat split) => [ | c /quotient_classification [H2 [x [H3 H4]]] |
                      c1 c2 /quotient_classification [H2 [x [H3 H4]]]
                         /quotient_classification [H5 [y [H6 H7]]] H8 ].
  - apply /Extensionality => z.
    rewrite Union_classification.
    split => [[S [/quotient_classification [H2 [x [H3 H4]]] H5]] | H2]; auto.
    exists {y in X | (z,y) ∈ R}.
    rewrite quotient_classification Specify_classification.
    (repeat split; auto) => [ x /Specify_classification [H3 H4] | ] //.
    exists z; split; auto => y.
    rewrite Specify_classification //.
  - eapply Nonempty_classification, ex_intro, H4; eauto.
  - apply NNPP.
    move: H8 => /[swap] /Nonempty_classification =>
    [[z]] /Pairwise_intersection_classification =>
    [[/H4 [H9 H10] /H7 [_ H11]] H12].
    apply /H12 /Extensionality => ζ.
    rewrite ? H4 ? H7; intuition eauto.
Qed.

Definition is_function f A B :=
  (f ⊂ A × B) ∧ (∀ a, a ∈ A → exists ! b, b ∈ B ∧ (a,b) ∈ f).

Theorem unique_set_element : ∀ {X} (x : elts X), exists ! y, y ∈ X ∧ y = x.
Proof.
  move=> X [x H].
  exists x.
  repeat split; auto => x' [H0 H1] //.
Qed.

Record function : Type :=
  mkFunc { domain : set;
           range : set;
           graph : set;
           func_hyp : is_function graph domain range }.
Arguments mkFunc {domain} {range} {graph} func_hyp.

Definition outsider B := {x in B | x ∉ x}.

Theorem outsider_not_in : ∀ B, outsider B ∉ B.
Proof.
  move=> B H.
  absurd (outsider B ∈ outsider B); try apply Specify_classification, conj;
    auto; move=> /[dup] /Specify_classification => [[_ H0] H1] //.
Qed.

Definition eval : function → set → set.
Proof.
  move=> f x.
  elim (excluded_middle_informative (x ∈ domain f)) => [ | H].
  - move: (func_hyp f) => [] _ /[apply] /constructive_indefinite_description =>
    [[y] [[H H0] H1]].
    exact y.
  - exact (outsider (range f)).
Defined.

Coercion eval : function >-> Funclass.

Theorem function_maps_domain_to_range :
  ∀ f x, x ∈ domain f → f x ∈ range f.
Proof.
  rewrite /eval /sumbool_rect => f x H.
  case excluded_middle_informative => [{}H | ] //.
  destruct func_hyp.
  elim constructive_indefinite_description => y [[H0 H1] H2] //.
Qed.

Theorem function_construction : ∀ A B p,
    (∀ a, a ∈ A → p a ∈ B) →
    (∃ f, (domain f = A ∧ range f = B ∧ ∀ a, a ∈ A → f a = p a)).
Proof.
  move=> A B p H.
  have: ∀ a, a ∈ A → (a, p a) ∈ A × B.
  { move=> a H0.
    eapply Product_classification, ex_intro; eauto. }
  have H0: is_function {z in A × B | proj2 A B z = p (proj1 A B z)} A B.
  { (split => x; try now rewrite ? Specify_classification).
    exists (p x).
    (repeat split; try congruence; eauto) =>
    [| y [H1]]; rewrite Specify_classification ? proj1_eval ? proj2_eval
                        ? Product_classification; intuition; exists x; eauto. }
  exists (mkFunc H0); repeat split; auto => a H1.
  rewrite /eval /sumbool_rect.
  case excluded_middle_informative => /= {}H1 //.
  destruct H0.
  elim constructive_indefinite_description => y [[H2 /Specify_classification]].
  rewrite proj2_eval // proj1_eval // => [[]] //.
Qed.

Theorem functionify_construction : ∀ {A B} (p : elts A → elts B),
  ∃ f, domain f = A ∧ range f = B ∧ ∀ a : elts A, f a = p a.
Proof.
  move=> A B p.
  have H: ∀ a : elts A, (a, p a) ∈ A × B.
  { move=> a.
    rewrite Product_classification.
    eauto using elts_in_set. }
  have H0: is_function {z in A × B | ∃ a : elts A, z = (a, p a)} A B.
  { (split => a; try rewrite 1 ? Specify_classification => [[H0 H1]] //) => H0.
    exists (p (mkSet H0)).
    ((repeat split; eauto using elts_in_set) =>
     [| y]; rewrite Specify_classification ? Product_classification)
    => [| [H1 [H2 [c /Ordered_pair_iff [H3 H4]]]]].
    - split; eauto using elts_in_set.
      exists (mkSet H0 : elts A) => //.
    - move: H3 H4 H0 H1 => -> -> H0 H1.
      apply /f_equal /f_equal /set_proj_injective => //. }
  exists (mkFunc H0); repeat split; auto => a.
  rewrite /eval /sumbool_rect.
  case excluded_middle_informative => /= [H1 | []]; eauto using elts_in_set.
  destruct H0.
  elim constructive_indefinite_description => y [[H2 /Specify_classification]]
  => [[]] _ [a0] /Ordered_pair_iff [] /set_proj_injective -> //.
Qed.

Theorem function_maps_domain_to_graph :
  ∀ f x y, x ∈ domain f → y ∈ range f → (x,y) ∈ graph f ↔ f x = y.
Proof.
  rewrite /eval /sumbool_rect => f x y H H0.
  case excluded_middle_informative => // {}H.
  destruct func_hyp.
  elim constructive_indefinite_description => z [[H1 H2] H3].
  split; eauto; congruence.
Qed.

Theorem graph_elements_are_pairs : ∀ f z, z ∈ graph f → z ∈ domain f × range f.
Proof.
  move=> [_ _] _ [H] _ /H //.
Qed.

Section Function_evaluation.

  Variable f : function.
  Context {A B : set}.

  Definition lambdaify : elts (domain f) → elts (range f).
  Proof.
    move=> [x H].
    have H0: f x ∈ range f.
      by auto using function_maps_domain_to_range.
      exact (mkSet H0).
  Defined.

  Definition functionify : (elts A → elts B) → function.
  Proof.
    move: (@functionify_construction) =>
    /[swap] p /(_ _ _ p) /constructive_indefinite_description => [[g H]].
    exact g.
  Defined.

  Theorem functionify_domain : ∀ g, domain (functionify g) = A.
  Proof.
    rewrite /functionify => g.
    elim constructive_indefinite_description => g' [-> [H H0]] //.
  Qed.

  Theorem functionify_range : ∀ g, range (functionify g) = B.
  Proof.
    rewrite /functionify => g.
    elim constructive_indefinite_description => g' [H [-> H0]] //.
  Qed.

  Theorem functionify_graph : ∀ g, graph (functionify g) ⊂ A × B.
  Proof.
    move=> g z /graph_elements_are_pairs.
    rewrite functionify_domain functionify_range //.
  Qed.

  Theorem functionify_action :
    ∀ (a : elts A) g, (functionify g) a = g a.
  Proof.
    rewrite /functionify => a g.
    elim constructive_indefinite_description => g' [H [H0 ->]] //.
  Qed.

  Theorem functionify_is_function :
    ∀ g, is_function (graph (functionify g)) A B.
  Proof.
    move=> g.
    repeat split; auto using functionify_graph => a H.
    exists (g (mkSet H)).
    (repeat split) => [ | | x' [H0 H1]]; eauto using elts_in_set.
    - apply function_maps_domain_to_graph;
        rewrite ? functionify_domain // ? functionify_range;
        eauto using elts_in_set; rewrite -functionify_action //.
    - rewrite -functionify_action.
      apply function_maps_domain_to_graph in H1;
      rewrite ? functionify_domain // ? functionify_range //.
  Qed.

  Theorem functionify_injective : ∀ g h, functionify g = functionify h → g = h.
  Proof.
    move=> g h H.
    extensionality x.
    apply set_proj_injective.
    rewrite -? functionify_action H //.
  Qed.

End Function_evaluation.

Definition power X Y := {f in P (Y × X) | is_function f Y X}.

Infix "^" := power : set_scope.

Definition inclusion A B := {x in A × B | ∃ a, a ∈ A ∧ x = (a,a)}.

Theorem Inclusion_is_function : ∀ A B, A ⊂ B → is_function (inclusion A B) A B.
Proof.
  split => [x /Specify_classification [H0 H1] | a H0] //.
  exists a.
  (repeat split; eauto) =>
  [| x' [H1 /Specify_classification [H2 [z [H3 /Ordered_pair_iff H4]]]]].
  - rewrite Specify_classification Product_classification.
    split; eauto 6.
  - intuition congruence.
Qed.

Definition injective f := ∀ x y, (lambdaify f) x = (lambdaify f) y → x = y.

Definition surjective f := ∀ y, ∃ x, (lambdaify f) x = y.

Definition bijective f := injective f ∧ surjective f.

Section Choice.

  (* Axiom of choice is a theorem since we assume indefinite description. *)
  Variable X : set.
  Hypothesis H : ∅ ∉ X.

  Definition choice_function : set → set.
  Proof.
    move=> x.
    elim (excluded_middle_informative (x ∈ X)) => H0.
    - (have: x ≠ ∅ by congruence) =>
      /Nonempty_classification /constructive_indefinite_description => [[y H1]].
      exact y.
    - exact (outsider X).
  Defined.

  Lemma choice_function_classification : ∀ x, x ∈ X → choice_function x ∈ x.
  Proof.
    rewrite /choice_function => x H0.
    elim excluded_middle_informative => {}H0 /= //.
    rewrite /ssr_have.
    elim constructive_indefinite_description => //.
  Qed.

  Theorem Choice : ∃ f, domain f = X ∧ range f = ⋃ X  ∧ ∀ x, x ∈ X → f x ∈ x.
  Proof.
    move: (function_construction X (⋃ X) choice_function) => H0.
    elim H0 => [f [H1 [H2 H3]] | x H1]; rewrite ? Union_classification;
                 eauto using choice_function_classification.
    exists f.
    (repeat split; auto) => x H4.
    rewrite H3; auto using choice_function_classification.
  Qed.

End Choice.

Theorem function_empty_domain : ∀ f, graph f = ∅ ↔ domain f = ∅.
Proof.
  (split => H; apply NNPP; contradict H; move: (func_hyp f) H => [H H0]
   => /Nonempty_classification => [[x]]; rewrite Nonempty_classification)
  => [/H0 [y [[_ H1] _]] | /H /Product_classification [a [b [H1 _]]]]; eauto.
Qed.

Theorem Injective_classification : ∀ f, injective f ↔ ∀ x y,
        x ∈ domain f → y ∈ domain f → f x = f y → x = y.
Proof.
  split => [H x y H0 H1 H2 | H [x X] [y Y] H0];
             [ rewrite (reify H0) (reify H1) | inversion H0 ];
             auto using f_equal, set_proj_injective.
Qed.

Theorem Surjective_classification : ∀ f, surjective f ↔ ∀ y,
        y ∈ range f → ∃ x, x ∈ domain f ∧ f x = y.
Proof.
  split => [H y H0 | H [y Y]].
  - elim (H (mkSet H0 : elts (range f))) => [[x X] H1].
    inversion H1; eauto.
  - elim (H _ Y) => [x [H0]].
    exists (mkSet H0 : elts (domain f)).
    exact: set_proj_injective.
Qed.

Section inverse_functions.

  Variable f : function.
  Hypothesis H : graph f ≠ ∅.

  Notation A := (domain f).
  Notation B := (range f).

  Definition partial_left_inverse : set → set.
  Proof.
    move: H => /[swap] b /function_empty_domain /Nonempty_classification
                /constructive_indefinite_description [x H0].
    elim (excluded_middle_informative (∃ a, a ∈ A ∧ f a = b)) =>
    [/constructive_indefinite_description [a H1] | H1]; eauto.
  Defined.

  Theorem left_inverse_iff_injective :
    injective f ↔ ∃ g, domain g = range f ∧ range g = domain f ∧
                       ∀ x, x ∈ domain f → g (f x) = x.
  Proof.
    split => [/Injective_classification H0 | [g [H0 [H1 H2]]]].
    - elim (function_construction B A partial_left_inverse) =>
      [g [H1 [H2 H3]] | a H1].
      + exists g.
        (repeat split; auto) => x /[dup] H4 /function_maps_domain_to_range /H3.
        rewrite /partial_left_inverse.
        elim excluded_middle_informative => [H5 | H5].
        * (repeat elim constructive_indefinite_description => ? /= //)
          => [[H6]] /H0 -> //.
        * contradict H5; eauto.
      + rewrite /partial_left_inverse; elim excluded_middle_informative =>
        x; repeat elim constructive_indefinite_description => /= //; tauto.
    - apply Injective_classification => x y /H2 /[swap] /H2 {2}<- {2}<- -> //.
  Qed.

End inverse_functions.

Theorem right_inverse_iff_surjective :
  ∀ f, surjective f ↔ ∃ g, domain g = range f ∧ range g = domain f ∧
                           ∀ y, y ∈ range f → f (g y) = y.
Proof.
  split => [H | [g [H [H0 H1]]]].
  - exists
      (functionify
         (λ y, let (x, _) := constructive_indefinite_description (H y) in x)).
    rewrite functionify_domain functionify_range.
    (repeat split; auto) => y H0.
    rewrite (reify H0) functionify_action.
    elim constructive_indefinite_description => [[x X] <-] //.
  - rewrite /surjective => [[y /[dup] /H1 H2 /[dup]]].
    move: H H0 => {1}<- /[swap] /function_maps_domain_to_range /[swap] -> H Y.
    exists (mkSet H).
    eauto using set_proj_injective.
Qed.

Definition image (f : function) := {y in range f | ∃ x, x ∈ domain f ∧ f x = y}.

Definition push_forward (f : function) S :=
  {y in range f | ∃ x, x ∈ S ∩ domain f ∧ f x = y}.

Theorem image_subset_range : ∀ f, image f ⊂ range f.
Proof.
  move=> f x /Specify_classification [H H0] //.
Qed.

Theorem push_forward_image: ∀ f S, push_forward f S ⊂ image f.
Proof.
  move=> f S x /Specify_classification
           [H [z [/Pairwise_intersection_classification [H0 H1] H2]]].
  eapply Specify_classification, conj, ex_intro; repeat split; eauto.
Qed.

Theorem push_forward_domain : ∀ f, push_forward f (domain f) = image f.
Proof.
  move=> f.
  apply Subset_equality; auto using push_forward_image => x.
  rewrite ? Specify_classification Intersection_idempotent //.
Qed.

Theorem function_maps_domain_to_image :
  ∀ f x, x ∈ domain f → f x ∈ image f.
Proof.
  move=> f x H.
  apply Specify_classification.
  eauto using function_maps_domain_to_range.
Qed.

Theorem surjective_image : ∀ f, surjective f → range f = image f.
Proof.
  move=> f /Surjective_classification H.
  apply Extensionality => z.
  split => [H0 | /Specify_classification [H0 H1]] //.
  apply Specify_classification, conj; auto.
Qed.

Definition empty_function : function.
Proof.
  (have: ∀ a : set, a ∈ ∅ → a ∈ ∅ by auto) =>
  /function_construction /constructive_indefinite_description => [[f H]].
  exact f.
Defined.

Definition inverse : function → function.
Proof.
  move=> f.
  elim (excluded_middle_informative (bijective f)) =>
  [[H /right_inverse_iff_surjective /constructive_indefinite_description
      [g [H0 [H1 H2]]]] | H].
  - exact g.
  - exact empty_function.
Defined.

Theorem left_inverse :
  ∀ f, bijective f → ∀ x, x ∈ domain f → inverse f (f x) = x.
Proof.
  rewrite /inverse => f H x H0.
  elim excluded_middle_informative => /= // =>
  [[/Injective_classification H1 H2]].
  elim constructive_indefinite_description => [g [H3 [H4 H5]]].
  move: function_maps_domain_to_range (H0) (H0) H4 H1 =>
  /[apply] H1 /[swap] <- H4 H6.
  apply /H6; auto.
  move: function_maps_domain_to_range H3 H1 => /(_ g) /[swap] -> /[apply] //.
Qed.

Theorem inverse_domain : ∀ f, bijective f → domain (inverse f) = range f.
Proof.
  rewrite /inverse => f H.
  elim excluded_middle_informative => /= // => [[H1 H2]].
  elim constructive_indefinite_description => [g [H3 [H4 H5]]] //.
Qed.

Theorem right_inverse :
  ∀ f, bijective f → ∀ x, x ∈ domain (inverse f) → f (inverse f x) = x.
Proof.
  rewrite {2}/inverse => f H x H0.
  elim excluded_middle_informative => /= // => [[H1 H2]].
  elim constructive_indefinite_description => [g [H3 [H4 H5]]].
  move: inverse_domain H0 H5 -> => // /[swap] /[apply] //.
Qed.

Theorem inverse_range : ∀ f, bijective f → range (inverse f) = domain f.
Proof.
  rewrite /inverse => f H.
  elim excluded_middle_informative => /= // => [[H1 H2]].
  elim constructive_indefinite_description => [g [H3 [H4 H5]]] //.
Qed.

Theorem inverse_shift_right :
  ∀ f, bijective f → ∀ x y,
      x ∈ range f → y ∈ domain f → inverse f x = y ↔ x = f y.
Proof.
  split => H2.
  - rewrite -H2 right_inverse ? inverse_domain //.
  - rewrite H2 left_inverse //.
Qed.

Theorem inverse_bijective : ∀ f, bijective f → bijective (inverse f).
Proof.
  move=> f /[dup] H [H0 H1].
  (split; rewrite ? Injective_classification ? Surjective_classification) =>
  [x y H2 H3 H4 | y H2].
  - move: H H2 => /[dup] H /[swap] /right_inverse /[apply] <-.
    move: H4 H3 H -> => /right_inverse /[apply] //.
  - exists (f y).
    move: inverse_range inverse_domain H2 function_maps_domain_to_range -> =>
    // /[swap] /[dup] H2 /[swap] -> // /[swap] /[apply] H3.
    rewrite left_inverse; repeat split; auto.
Qed.

Definition composition : function → function → function.
Proof.
  move=> f g.
  elim (excluded_middle_informative (domain f = range g)) => [H | H].
  - have: ∀ x, x ∈ domain g → (λ x, f (g x)) x ∈ range f by
        move: H => /[swap] x /[swap] /function_maps_domain_to_range /[swap]
                   <- /function_maps_domain_to_range //.
    move /function_construction /constructive_indefinite_description => [h H0].
    exact h.
  - exact empty_function.
Defined.

Infix "∘" := composition : set_scope.

Theorem Composition_classification :
  ∀ f g, domain f = range g →
         domain (f ∘ g) = domain g ∧ range (f ∘ g) = range f ∧
         ∀ x, x ∈ domain g → (f ∘ g) x = f (g x).
Proof.
  rewrite /composition => f g H.
  elim excluded_middle_informative => // => {}H.
  rewrite /ssr_have /=.
  elim constructive_indefinite_description => //.
Qed.

Theorem composition_injective : ∀ f g,
    domain f = range g → injective f → injective g → injective (f ∘ g).
Proof.
  move=> f g /[dup] H /Composition_classification [H0 [H1 H2]]
           /Injective_classification H3 /Injective_classification H4
           [x X] [y Y] H5.
  inversion H5.
  apply /set_proj_injective /H4 =>
  /=; try apply H3; rewrite ? H -? H2;
    try apply /function_maps_domain_to_range; congruence.
Qed.

Theorem composition_surjective : ∀ f g,
    domain f = range g → surjective f → surjective g → surjective (f ∘ g).
Proof.
  move=> f g /[dup] H /Composition_classification [H0 [H1 H2]]
           /Surjective_classification H3 /Surjective_classification H4.
  rewrite Surjective_classification => y H5.
  move: H1 H H5 -> => /[swap] /H3 [z] /[swap] -> [/H4] [x].
  move: H0 H2 <- => /[swap] [[H <-]] <-; eauto.
Qed.

Theorem Graph_classification :
  ∀ f z, z ∈ graph f ↔ ∃ a, a ∈ domain f ∧ z = (a, f a).
Proof.
  split => [H | [a [H ->]]].
  - move: H (func_hyp f) => /[dup] /[swap] H /[swap] /[dup] H0 [H1 H2] /H1
                             /Product_classification [a [b [H3 [H4 H5]]]].
    eapply ex_intro, conj; eauto; subst.
    move: (H2) (H3) => /[apply] => [[y]] [[H5 H6] H7].
    have ->: b = y by apply eq_sym, H7.
      by have ->: y = f a by apply H7; rewrite ? function_maps_domain_to_graph;
        eauto using function_maps_domain_to_range.
  - rewrite ? function_maps_domain_to_graph;
      eauto using function_maps_domain_to_range.
Qed.

Theorem function_graph_uniqueness : ∀ f x a b, x ∈ domain f →
    (x, a) ∈ graph f → (x, b) ∈ graph f → a = b.
Proof.
  move: func_hyp
  => /[swap] f /(_ f) [H H0] x a b H1 /Graph_classification
      [c [H2 /Ordered_pair_iff [-> ->]]] /Graph_classification
      [d [H5 /Ordered_pair_iff [-> ->]]] //.
Qed.

Section Restrictions.

  Variable f : function.
  Variable X Y : set.

  Hypothesis image_Y : image f ⊂ Y.

  Definition restriction_set :=
    {x in graph f | proj1 (domain f) (range f) x ∈ X}.

  Lemma restriction_is_function :
    is_function restriction_set (X ∩ domain f) (range f).
  Proof.
    split => [z /Specify_classification
                [/[dup] /graph_elements_are_pairs
                  /Product_classification [a [b [H [H0 H1]]]] H2] |
              z /Pairwise_intersection_classification [H H0]].
    - rewrite Product_intersection_distr_l Pairwise_intersection_classification
              H1 proj1_eval ? Product_classification; repeat split; eauto.
    - exists (f z).
      (repeat split; auto using function_maps_domain_to_range) =>
      [| y [H1 /Specify_classification [H2 H3]]].
      + apply Specify_classification, conj;
          [ apply /function_maps_domain_to_graph | rewrite proj1_eval ];
          auto using function_maps_domain_to_range.
      + apply function_maps_domain_to_graph; auto.
  Qed.

  Definition restriction := mkFunc restriction_is_function.

  Theorem restriction_domain : domain restriction = (X ∩ domain f).
  Proof.
    auto.
  Qed.

  Theorem restriction_range : range restriction = range f.
  Proof.
    auto.
  Qed.

  Theorem restriction_graph : graph restriction = restriction_set.
  Proof.
    auto.
  Qed.

  Theorem restriction_subset : graph restriction ⊂ graph f.
  Proof.
    rewrite restriction_graph => z /Specify_classification [H H0] //.
  Qed.

  Theorem restriction_action : ∀ x, x ∈ X ∩ domain f → f x = restriction x.
  Proof.
    (rewrite /restriction => x /Pairwise_intersection_classification) => [[*]].
    apply /function_maps_domain_to_graph; simpl; auto;
      [ rewrite <-restriction_range; apply function_maps_domain_to_range |
        apply /restriction_subset /Graph_classification; exists x ];
      rewrite restriction_domain Pairwise_intersection_classification //.
  Qed.

  Theorem restriction_Y_is_function : is_function (graph f) (domain f) Y.
  Proof.
    split => [z /Graph_classification [a [H ->]] | z H].
    - eapply Product_classification, ex_intro, ex_intro.
      eauto using function_maps_domain_to_image.
    - exists (f z); (repeat split) =>
      [ | | y [H0 /Graph_classification [a [H1 /Ordered_pair_iff [-> ->]]]]] //.
      + eauto using function_maps_domain_to_image.
      + apply /Graph_classification; eauto.
  Qed.

  Definition restriction_Y := mkFunc restriction_Y_is_function.

  Theorem restriction_Y_domain : domain restriction_Y = domain f.
  Proof.
    auto.
  Qed.

  Theorem restriction_Y_range : range restriction_Y = Y.
  Proof.
    auto.
  Qed.

  Theorem restriction_Y_graph : graph restriction_Y = graph f.
  Proof.
    auto.
  Qed.

  Theorem restriction_Y_action : ∀ a, a ∈ domain f → restriction_Y a = f a.
  Proof.
    move=> a H.
    apply function_maps_domain_to_graph; auto;
      rewrite ? restriction_Y_range ? restriction_Y_graph;
      [ | apply function_maps_domain_to_graph ];
      auto using function_maps_domain_to_range, function_maps_domain_to_image.
  Qed.

End Restrictions.

Arguments restriction_Y {f Y}.
Arguments restriction_Y_domain {f Y}.
Arguments restriction_Y_range {f Y}.
Arguments restriction_Y_action {f Y}.

Section Quotient_maps.

  Context {X : set}.
  Variable R : set.

  Definition quotient_map : elts X → elts (X / R).
  Proof.
    move=> [x H].
    have H0: {z in X | (x, z) ∈ R} ∈ X / R.
    { apply quotient_classification, conj =>
      [y /Specify_classification [H0 H1] | ] //.
      exists x.
      repeat split; auto; rewrite -> Specify_classification in *; intuition. }
    exact (mkSet H0).
  Defined.

End Quotient_maps.

Theorem quotient_lift : ∀ {X R : set} (y : elts (X / R)),
  ∃ x : elts X, quotient_map R x = y.
Proof.
  rewrite /quotient => X R [y /[dup] /quotient_classification [H [x [H0 H1]]]]
                         /[dup] /replacement_classification [γ H2] H3.
  exists (mkSet H0 : elts X).
  apply /set_proj_injective /Extensionality => /= z.
  split => [/Specify_classification /H1 H4 | H4] //.
  apply /Specify_classification /H1 => //.
Qed.

Theorem quotient_equiv : ∀ X R (x y : elts X),
    is_equivalence X R → quotient_map R x = quotient_map R y ↔ (x, y) ∈ R.
Proof.
  move=> X R [x A] [y B] [H [H0 H1]].
  split => [H2 /= | H2].
  - (have: {z in X | (x, z) ∈ R} = {z in X | (y, z) ∈ R} by now inversion H2)
    => /Subset_equality_iff => [[H3 /(_ y)]].
    rewrite ? Specify_classification.
    move: H => /(_ y); tauto.
  - apply /set_proj_injective /Extensionality => /= => z.
    rewrite ? Specify_classification; intuition;
      [ apply (H1 y x) | eapply H1 ]; eauto.
Qed.

Theorem quotient_image :
  ∀ X R (x : elts X), {z in X | (x,z) ∈ R} = quotient_map R x.
Proof.
  move=> X R [x H] //.
Qed.

Theorem no_quines : ∀ x, ¬ x ∈ x.
Proof.
  move: Regularity => /[swap] x /(_ {x,x}) H H0.
  elim H => [y [/Singleton_classification -> H2] | ].
  - eapply H2, ex_intro, conj; eauto.
    rewrite Singleton_classification //.
  - eapply ex_intro, Singleton_classification => //.
Qed.

Theorem no_loops : ∀ x y, ¬ (x ∈ y ∧ y ∈ x).
Proof.
  move: Regularity => /[swap] x /[swap] y /(_ {x,y}) H [H0 H1].
  elim H => [z [/Pairing_classification H2 H3] {H} | ].
  - contradict H3.
    wlog: x y H0 H1 H2 / z = x => [ x0 | -> ].
    + elim H2; [ | rewrite Pairing_comm ]; auto.
    + exists y.
      rewrite Pairing_classification; tauto.
  - exists x.
    rewrite Pairing_classification; tauto.
Qed.

Lemma disjoint_succ : ∀ s, s ∩ {s,s} = ∅.
Proof.
  move=> s; apply Extensionality => z; split =>
  [/Pairwise_intersection_classification
    [/[dup] H /[swap] /Singleton_classification -> /no_quines]
  | /Empty_set_classification] //.
Qed.

Theorem disjoint_union_complement : ∀ E F, E ∪ F = E ∪ (F \ E).
Proof.
  move=> E F.
  apply Extensionality => z.
  rewrite ? Pairwise_union_classification.
  split => [[H | H] | [H | /Complement_classification]]; try tauto.
  (elim (classic (z ∈ E)); try tauto) => H0.
  apply /or_intror /Complement_classification => //.
Qed.

Lemma in_succ : ∀ s, s ∈ succ s.
Proof.
  rewrite /succ => s.
  now apply /Pairwise_union_classification /or_intror /Singleton_classification.
Qed.

Lemma subset_succ : ∀ s, s ⊂ succ s.
Proof.
  rewrite /succ => s x H.
  apply /Pairwise_union_classification /or_introl => //.
Qed.

Theorem complement_disjoint_union : ∀ E F, E ∩ F = ∅ → (E ∪ F) \ F = E.
Proof.
  move=> E F H.
  apply Extensionality => z.
  split => [/Complement_classification
             [/Pairwise_union_classification [H0 | H0] H1] | H0]; try tauto.
  apply Complement_classification, conj => [ | H1].
  - apply Pairwise_union_classification; tauto.
  - contradiction (Empty_set_classification z).
    rewrite -H Pairwise_intersection_classification //.
Qed.

Theorem disjoint_intersection_complement : ∀ E F, E ∩ (F \ E) = ∅.
Proof.
  move=> E F.
  apply Extensionality => z.
  rewrite Pairwise_intersection_classification Complement_classification.
  split => [[H [H0 H1]] | /Empty_set_classification] //.
Qed.

Theorem complement_union_intersection : ∀ E F, (F \ E) ∪ (E ∩ F) = F.
Proof.
  move=> E F.
  apply Extensionality => z.
  rewrite Pairwise_union_classification Complement_classification
          Pairwise_intersection_classification.
  split => [[[H H0] | [H H0]] | H] //.
  elim (classic (z ∈ E)); tauto.
Qed.

Theorem complement_disjoint_intersection : ∀ E F, (F \ E) ∩ (E ∩ F) = ∅.
Proof.
  move=> E F.
  apply Extensionality => z.
  rewrite ? Pairwise_intersection_classification Complement_classification.
  split => [[[H H0] [H1 H2]] | /Empty_set_classification] //.
Qed.

Theorem complement_subset : ∀ E F, F \ E ⊂ F.
Proof.
  move=> E F x /Complement_classification [H] //.
Qed.

Theorem Intersection_left : ∀ E F, E ∩ F ⊂ E.
Proof.
  move=> E F x /Pairwise_intersection_classification [H H0] //.
Qed.

Theorem Intersection_right : ∀ E F, E ∩ F ⊂ F.
Proof.
  move=> E F x /Pairwise_intersection_classification [H H0] //.
Qed.

Theorem power_0_l : ∀ m, m ≠ ∅ → ∅^m = ∅.
Proof.
  move=> m /[dup] H /Nonempty_classification [x H0].
  apply Extensionality => z; split =>
  [/Specify_classification [H1 [H2 /(_ x H0) [y [[/Empty_set_classification]]]]]
  | /Empty_set_classification] //.
Qed.

Theorem power_0_r : ∀ m, m^∅ = succ ∅.
Proof.
  move=> m; apply Extensionality => z.
  (split => [/Specify_classification |
             /Pairwise_union_classification [/Empty_set_classification | ]]
              //; rewrite ? Specify_classification /is_function ? /succ
              ? Pairwise_union_classification Singleton_classification
              Empty_product_left) =>
  [[H [/Subset_equality ->]] | ->]; repeat split;
    auto using Empty_set_in_powerset, Empty_set_is_subset
  => a /Empty_set_classification //.
Qed.

Definition inverse_image_of_element f y := {x in domain f | f x = y}.

Theorem Inverse_image_classification : ∀ f a b,
    a ∈ domain f → b ∈ range f → a ∈ inverse_image_of_element f b ↔ f a = b.
Proof.
  split; rewrite Specify_classification; tauto.
Qed.

Theorem Inverse_image_classification_domain : ∀ f a b,
    b ∈ range f → a ∈ inverse_image_of_element f b → a ∈ domain f.
Proof.
  rewrite /inverse_image_of_element => f a b H /Specify_classification [] //.
Qed.

Theorem Inverse_image_classification_left : ∀ f a b,
    b ∈ range f → a ∈ inverse_image_of_element f b → f a = b.
Proof.
  rewrite /inverse_image_of_element => f a b H /Specify_classification [] //.
Qed.

Theorem Inverse_image_subset : ∀ f b,
    b ∈ range f → inverse_image_of_element f b ⊂ domain f.
Proof.
  rewrite /inverse_image_of_element => f a b H /Specify_classification [] //.
Qed.

Theorem function_graph_equality : ∀ A B g1 g2,
    is_function g1 A B → is_function g2 A B → g1 ⊂ g2 → g1 = g2.
Proof.
  move=> A B g1 g2 /[dup] H /[swap] /[dup] H0 /[swap].
  rewrite /is_function -{4}[g1]/(graph (mkFunc H)) -{4}[g2]/(graph (mkFunc H0))
  => [[H1 H2] [H3 H4]] H5.
  apply Subset_equality_iff, conj; auto =>
  [z /Graph_classification [z1 [H6 ->]]].
  eapply Graph_classification, ex_intro, conj, f_equal,
  function_graph_uniqueness; eauto =>
  /=; [ | apply /H5 ];
    rewrite -1? [g1]/(graph (mkFunc H))
    -1? [g2]/(graph (mkFunc H0)) function_maps_domain_to_graph
      /= -1 ?[B]/(range (mkFunc H)) -1 ?[B]/(range (mkFunc H0)); auto;
      apply /function_maps_domain_to_range => //.
Qed.

Theorem singleton_products : ∀ x y, {x,x} × {y,y} = {(x,y), (x,y)}.
Proof.
  move=> x y.
  apply Extensionality => z.
  rewrite Singleton_classification Product_classification.
  split => [[a [b [/Singleton_classification ->
                   [/Singleton_classification -> ->]]]] | H] //.
  exists x, y.
  rewrite ? Singleton_classification //.
Qed.

Theorem singleton_functions :
  ∀ f x y, domain f = {x,x} → range f = {y,y} → graph f = {(x,y), (x,y)}.
Proof.
  move: func_hyp => /[swap] f /(_ f) /[dup] H [H0 H1] x y H2 H3.
  apply (function_graph_equality {x,x} {y,y}); try congruence.
  - split => [| a /Singleton_classification ->]; rewrite ? singleton_products.
    + apply Set_is_subset.
    + exists y.
      repeat split; rewrite ? Singleton_classification //
      => x' [/Singleton_classification -> H5] //.
  - move: H2 H3 singleton_products H0 => -> -> -> //.
Qed.

Theorem domain_uniqueness : ∀ f A1 A2 B,
    is_function f A1 B → is_function f A2 B → A1 = A2.
Proof.
  move=> f A1 A2 B [H H0] [H1 H2].
  apply Extensionality => z.
  wlog: f A1 A2 B H H0 H1 H2 / z ∈ A1.
  - split => H3; [ apply (x f A1 A2 B) | apply (x f A2 A1 B) ]; auto.
  - (split => H4; try tauto) => {H4}.
    move: H0 H3 =>
    /[apply] [[y [[_ /H1 /Specify_classification
                     [_ [a [b [_ [_ /Ordered_pair_iff [-> ->]]]]]]]]]] //.
Qed.

Theorem function_record_injective : ∀ f g,
    range f = range g → graph f = graph g → f = g.
Proof.
  move=> [df rf gf hf] [dg rg gg hg] /= H H0; subst.
  (have: df = dg by eauto using domain_uniqueness) => H; subst.
  suff -> : hf = hg; auto using proof_irrelevance.
Qed.

Lemma func_ext_lemma : ∀ f g,
    range f = range g → (∀ x, x ∈ domain f → f x = g x)
    → graph f ⊂ graph g.
Proof.
  move=> f g H H0 z /Graph_classification [a [/[dup] H1 /H0 /[dup] H2 -> ->]].
  apply Graph_classification.
  exists a.
  split; auto.
  apply NNPP => H3.
  move: (func_hyp g) H2 => H2.
  rewrite {2}/eval /sumbool_rect.
  case excluded_middle_informative => // {}H3 H4.
  contradiction (outsider_not_in (range g)).
  move: H H4 function_maps_domain_to_range <- => <- /(_ _ _ H1) //.
Qed.

Theorem func_ext : ∀ f g, domain f = domain g → range f = range g
                          → (∀ x, x ∈ domain f → f x = g x) → f = g.
Proof.
  move=> f g /[swap] H /[swap] /[dup] H0 /[swap] -> H1.
  apply function_record_injective, Subset_equality_iff, conj;
    auto using func_ext_lemma, eq_sym.
Qed.

Theorem function_inv_inv : ∀ f, bijective f → inverse (inverse f) = f.
Proof.
  move=> f /[dup] H /inverse_bijective /[dup] H0
           [/Injective_classification H1 H2].
  apply func_ext; rewrite ? inverse_domain ? inverse_range ? inverse_domain;
    auto using inverse_bijective => x H3.
  apply /H1; rewrite -? inverse_range ? left_inverse ? right_inverse; auto.
  * apply function_maps_domain_to_range.
    rewrite inverse_domain ? inverse_range; auto.
  * rewrite inverse_range ? inverse_domain; auto.
    apply function_maps_domain_to_range => //.
  * rewrite inverse_domain ? inverse_range; auto.
Qed.

Lemma Euler_Phi_lemma :
  ∀ A B C D, A = B → A ∩ C = ∅ → B ∩ D = ∅ → A ∪ C = B ∪ D → C = D.
Proof.
  move=> A B C D ->.
  rewrite ? (Intersection_comm B) ? (Union_comm B) =>
  /complement_disjoint_union {2}<- /complement_disjoint_union {2}<- -> //.
Qed.

Definition swap_product (S T : set) : elts (S × T) → elts (T × S).
Proof.
  move=> [z /Product_classification /constructive_indefinite_description
            [x /constructive_indefinite_description [y [H [H0 H1]]]]].
  have H2: (y, x) ∈ T × S by apply Product_classification; eauto.
  exact (mkSet H2).
Defined.

Definition swap_function S T := functionify (swap_product S T).

Theorem swap_domain : ∀ S T, domain (swap_function S T) = S × T.
Proof.
  move=> S T.
  apply functionify_domain.
Qed.

Theorem swap_range : ∀ S T, range (swap_function S T) = T × S.
Proof.
  move=> S T.
  apply functionify_range.
Qed.

Theorem swap_action : ∀ S T x y,
    x ∈ S → y ∈ T → swap_function S T (x, y) = (y, x).
Proof.
  move=> S T x y H H0.
  have H1: (x, y) ∈ S × T by apply Product_classification; eauto.
  rewrite /swap_function /swap_product (reify H1) functionify_action.
  elim constructive_indefinite_description => a [b [H2 [H3 H4]]].
  elim constructive_indefinite_description =>
  c [H5 [H6 /Ordered_pair_iff [-> ->]]] => /= //.
Qed.

Theorem swap_bijective : ∀ S T, bijective (swap_function S T).
Proof.
  (split; rewrite ? Injective_classification ? Surjective_classification
                  ? swap_domain ? swap_range) =>
  [z1 z2 /Product_classification [x [y [H [H0 ->]]]]
      /Product_classification [x' [y' [H1 [H2 ->]]]] |
   z /Product_classification [x [y [H [H0 ->]]]]].
  - rewrite ? swap_action; auto => /Ordered_pair_iff [-> ->] //.
  - exists (y, x).
    rewrite Product_classification swap_action; intuition eauto.
Qed.
