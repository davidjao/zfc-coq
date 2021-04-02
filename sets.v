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

Section Set_to_type.
  Variable S : set.
  Definition elts := {x : set | x ∈ S}.
  Definition elt_to_set (x : elts) := proj1_sig x.
  Coercion elt_to_set : elts >-> set.
End Set_to_type.
Arguments elt_to_set {S}.

Theorem set_proj_injective :
  ∀ X (n m : elts X), (n : set) = (m : set) → n = m.
Proof.
  move=> S [n N] [m M] /= H.
  move: H N M -> => N M.
  apply /f_equal /proof_irrelevance.
Qed.

Theorem elts_in_set : ∀ {S} (x : elts S), elt_to_set x ∈ S.
Proof.
  move=> S [x X] /= //.
Qed.

Theorem reify : ∀ {x} {S} (H : x ∈ S), x = (exist H : elts S).
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
  - exact (p (exist H)).
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
  - exists (f (exist H)).
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
  rewrite /intersection /specify.
  repeat (destruct constructive_indefinite_description => /=).
  apply /Extensionality => z.
  rewrite i Empty_union.
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
  intros A B C.
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

Lemma Ordered_pair_iff_left : ∀ a b c d, (a,b) = (c,d) → a = c.
Proof.
  move=> a b c d.
  rewrite /ordered_pair => H.
  have: {a,a} ∈ {{c,c}, {c,d}}.
  { move: H <-; apply /Pairing_classification /or_introl => //. }
  move => /Pairing_classification =>
  [[H0 | H0]]; symmetry; apply /Singleton_classification;
    rewrite H0; apply /Pairing_classification; auto.
Qed.

Theorem Ordered_pair_iff : ∀ a b c d, (a, b) = (c, d) ↔ (a = c ∧ b = d).
Proof.
  move=> a b c d.
  rewrite /ordered_pair.
  split => [/[dup] /Ordered_pair_iff_left -> H | [-> ->]] //.
  have: {c,b} ∈ {{c,c}, {c,d}}.
  { move: H <-; apply /Pairing_classification /or_intror => //. }
  move => /Pairing_classification =>
  [[/Subset_equality_iff [/(_ b) H0 _] |
    /Subset_equality_iff [/(_ b) H0 /(_ d) H1]]].
  - have: {c,d} ∈ {{c,c}, {c,b}}.
    { move: H ->; apply /Pairing_classification /or_intror => //. }
    move => /Pairing_classification =>
    [[/Subset_equality_iff [/(_ d) H1 _] | /Subset_equality_iff [/(_ d) H1 _]]];
      rewrite -> ? Pairing_classification in *; intuition congruence.
  - rewrite -> ? Pairing_classification in *; intuition congruence.
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
    exact (exist H0).
  Defined.

  Definition π2 : elts (A × B) → elts B.
  Proof.
    move=> z.
    move: (elts_in_set z) => /Product_classification
    => /constructive_indefinite_description [a] =>
    /constructive_indefinite_description [b] [H0 [H1 H2]].
    exact (exist H1).
  Defined.

  Theorem π1_action :
    ∀ a b (Ha : a ∈ A) (Hb : b ∈ B)
      (H : (exist Ha : elts A, exist Hb : elts B) ∈ A × B),
      π1 (exist H) = exist Ha.
  Proof.
    rewrite /π1 => a b Ha Hb H.
    elim constructive_indefinite_description => x [z [p [p0 p1]]].
    elim constructive_indefinite_description => y [q [q0 q1]].
    move: p1 q1 q => /Ordered_pair_iff /[swap] /Ordered_pair_iff [<- _] _ q.
    apply /f_equal /proof_irrelevance.
  Qed.

  Theorem π2_action :
    ∀ a b (Ha : a ∈ A) (Hb : b ∈ B)
      (H : (exist Ha : elts A, exist Hb : elts B) ∈ A × B),
      π2 (exist H) = exist Hb.
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

Theorem Product_intersection_distr_l :
  ∀ A B X, (A ∩ B) × X = (A × X) ∩ (B × X).
Proof.
  move=> A B X.
  rewrite -Product_intersection Intersection_idempotent //.
Qed.

Theorem Product_complement : ∀ A B X, (A \ B) × X = (A × X) \ (B × X).
Proof.
  intros A B X.
  apply Extensionality.
  split; intros H;
    repeat rewrite -> Complement_classification, Product_classification in *.
  - destruct H as [a [b [H [H0 H1]]]].
    rewrite -> Complement_classification in *.
    destruct H as [H H2].
    split; try now exists a, b.
    contradict H2.
    rewrite -> Product_classification in *.
    destruct H2 as [x [y [H2 [H3 H4]]]].
    subst.
    rewrite -> Ordered_pair_iff in *.
    intuition; congruence.
  - destruct H as [[a [b [H [H0 H1]]]] H2].
    exists a, b.
    rewrite -> Complement_classification in *.
    repeat split; auto.
    contradict H2.
    rewrite Product_classification.
    now exists a, b.
Qed.

Theorem Empty_product_left : ∀ S, ∅ × S = ∅.
Proof.
  intros.
  apply Extensionality.
  split; intros H.
  - apply Product_classification in H as [a [b [H [H0 H1]]]].
    contradiction (Empty_set_classification a).
  - contradiction (Empty_set_classification z).
Qed.

Theorem Empty_product_right : ∀ S, S × ∅ = ∅.
Proof.
  intros.
  apply Extensionality.
  split; intros H.
  - apply Product_classification in H as [a [b [H [H0 H1]]]].
    contradiction (Empty_set_classification b).
  - contradiction (Empty_set_classification z).
Qed.

Definition quotient X R := {{y in X | (x,y) ∈ R} | x in X}.

Infix "/" := quotient : set_scope.

Theorem quotient_classification : ∀ X R s,
    s ∈ X/R ↔ s ⊂ X ∧ ∃ x, x ∈ X ∧ (∀ y, y ∈ s ↔ y ∈ X ∧ (x,y) ∈ R).
Proof.
  intros X R s.
  split; intros H; repeat split;
    unfold quotient in *;
    repeat destruct constructive_indefinite_description;
    rewrite -> replacement_classification in *; destruct H as [σ H]; subst.
  - intros x H.
    now apply Specify_classification in H.
  - exists σ.
    split; auto using elts_in_set.
    split; intros H.
    + now apply Specify_classification in H.
    + now apply Specify_classification.
  - destruct H as [x [H H0]].
    exists (exist H : elts X).
    apply Extensionality.
    split; intros H1.
    + apply Specify_classification; firstorder.
    + apply Specify_classification in H1; firstorder.
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
  intros X R [H [H0 H1]].
  repeat split.
  - apply Extensionality.
    split; intros H2.
    + apply Union_classification in H2 as [S [H2 H3]].
      apply quotient_classification in H2 as [H2 [x [H4 H5]]].
      now apply H2.
    + apply Union_classification.
      exists {y in X | (z,y) ∈ R}.
      split; try rewrite -> quotient_classification in *; try split;
        [ intros y H3 | exists z; intuition | ];
        rewrite -> Specify_classification in *; intuition.
  - intros c H2.
    apply quotient_classification in H2 as [H2 [x [H3 H4]]].
    rewrite Nonempty_classification.
    exists x.
    apply H4; auto.
  - intros c1 c2 H2 H3 H4.
    apply quotient_classification in H2 as [H2 [x [H5 H6]]].
    apply quotient_classification in H3 as [H3 [y [H7 H8]]].
    apply NNPP.
    contradict H4.
    apply Nonempty_classification in H4 as [z H4].
    apply Pairwise_intersection_classification in H4 as [H4 H9].
    apply Extensionality.
    split; intros H10; apply H6 in H4 as [H4 H12]; apply H8 in H9 as [H9 H13];
      [ apply H6 in H10 as [H10 H14] | apply H8 in H10 as [H10 H14] ];
      [ apply H8 | apply H6 ]; eauto.
Qed.

Definition is_function f A B :=
  (f ⊂ A × B) ∧ (∀ a, a ∈ A → exists ! b, b ∈ B ∧ (a,b) ∈ f).

Theorem unique_set_element : ∀ {X} (x : elts X), exists ! y, y ∈ X ∧ y = x.
Proof.
  intros X [x H].
  exists x.
  repeat split; auto.
  now intros x' [H0 H1].
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
  intros B H.
  absurd (outsider B ∈ outsider B); try apply Specify_classification;
    try split; auto; intros H0; now apply Specify_classification in H0 as H1.
Qed.

Definition eval_rel : set → set → set → set → set.
Proof.
  intros f A B x.
  destruct (excluded_middle_informative (x ∈ A)).
  - destruct (excluded_middle_informative (is_function f A B)).
    + destruct i0, (constructive_indefinite_description (H0 x i)) as [y].
      exact y.
    + exact (outsider B).
  - exact (outsider B).
Defined.

Definition eval f x := eval_rel (graph f) (domain f) (range f) x.

Coercion eval : function >-> Funclass.

Theorem Function_classification : ∀ {f A B a},
    a ∈ A → is_function f A B →
    unique (λ b : set, b ∈ B ∧ (a, b) ∈ f) (eval_rel f A B a).
Proof.
  intros f A B a H H0.
  unfold eval_rel.
  destruct (excluded_middle_informative (a ∈ A)),
  (excluded_middle_informative (is_function f A B)); try tauto.
  destruct i0.
  repeat destruct constructive_indefinite_description; repeat split; tauto.
Qed.

Theorem function_maps_domain_to_range :
  ∀ f x, x ∈ domain f → f x ∈ range f.
Proof.
  intros f x H.
  pose proof func_hyp f as H0.
  eapply Function_classification in H as [[H H1] H2]; eauto.
Qed.

Theorem function_construction : ∀ A B p,
    (∀ a, a ∈ A → p a ∈ B) →
    (∃ f, (domain f = A ∧ range f = B ∧ ∀ a, a ∈ A → f a = p a)).
Proof.
  intros A B p H.
  assert (∀ a, a ∈ A → (a, p a) ∈ A × B) as H0.
  { intros a H0.
    rewrite Product_classification.
    exists a, (p a); intuition; congruence. }
  assert (is_function {z in A × B | proj2 A B z = p (proj1 A B z)} A B) as H1.
  { split; intros x H1; try now rewrite -> Specify_classification in *.
    exists (p x).
    repeat split; try congruence; try intros x' [H4 H5]; auto;
      rewrite -> Specify_classification, proj1_eval, proj2_eval in *;
      intuition. }
  exists (mkFunc H1).
  repeat split; auto.
  intros a H2.
  destruct (Function_classification H2 H1) as [[H3 H4] H5].
  destruct (H5 (p a)); split; simpl; intuition.
  rewrite -> Specify_classification, proj1_eval, proj2_eval; auto.
Qed.

Theorem functionify_construction : ∀ {A B} (p : elts A → elts B),
  ∃ f, domain f = A ∧ range f = B ∧ ∀ a : elts A, f a = p a.
Proof.
  intros A B p.
  assert (∀ a : elts A, (a, p a) ∈ A × B) as H.
  { intros a.
    rewrite Product_classification.
    eauto using elts_in_set. }
  assert (is_function {z in A × B | ∃ a : elts A, z = (a, p a)} A B) as H0.
  { split; intros a H0; try now rewrite -> Specify_classification in *.
    exists (p (exist H0)).
    repeat split; eauto using elts_in_set.
    - rewrite -> Specify_classification in *.
      split.
      + apply Product_classification.
        eauto using elts_in_set.
      + now (exists (exist H0 : elts A)).
    - intros x' H1.
      destruct H1 as [H1 H2].
      apply Specify_classification in H2 as [H2 [[a' H3] H4]].
      simpl in *.
      apply Ordered_pair_iff in H4 as [H4 H5].
      subst.
      repeat apply f_equal.
      apply proof_irrelevance. }
  exists (mkFunc H0).
  repeat split; auto.
  intros a.
  destruct (Function_classification (elts_in_set a) H0)
    as [[H1 H2] H3], (H3 (p a)); try apply H3; split; auto using elts_in_set.
  rewrite Specify_classification.
  split; try now (exists a).
  rewrite Product_classification.
  eauto using elts_in_set.
Qed.

Theorem function_maps_domain_to_graph :
  ∀ f x y, x ∈ domain f → y ∈ range f → (x,y) ∈ graph f ↔ f x = y.
Proof.
  intros f x y H H0.
  split; intros H1; unfold eval, eval_rel in *;
    repeat destruct excluded_middle_informative; intuition;
      try contradiction (func_hyp f);
      try destruct i0, constructive_indefinite_description;
      destruct a as [[H2 H3] H4]; auto; congruence.
Qed.

Theorem graph_elements_are_pairs : ∀ f z, z ∈ graph f → z ∈ domain f × range f.
Proof.
  intros f z H.
  destruct f.
  unfold graph in H.
  simpl.
  destruct func_hyp0.
  now apply H0.
Qed.

Section Function_evaluation.

  Variable f : function.
  Context {A B : set}.

  Definition lambdaify : elts (domain f) → elts (range f).
  Proof.
    intros [x H].
    assert (f x ∈ range f)
      by auto using function_maps_domain_to_range.
    exact (exist H0).
  Defined.

  Definition functionify : (elts A → elts B) → function.
  Proof.
    intros p.
    destruct (constructive_indefinite_description
                (functionify_construction p)) as [g].
    exact g.
  Defined.

  Theorem functionify_domain : ∀ g, domain (functionify g) = A.
  Proof.
    intros g.
    unfold functionify.
    destruct constructive_indefinite_description.
    tauto.
  Qed.

  Theorem functionify_range : ∀ g, range (functionify g) = B.
  Proof.
    intros g.
    unfold functionify.
    destruct constructive_indefinite_description.
    tauto.
  Qed.

  Theorem functionify_graph : ∀ g, graph (functionify g) ⊂ A × B.
  Proof.
    intros g z H.
    apply graph_elements_are_pairs in H.
    now rewrite -> functionify_domain, functionify_range in H.
  Qed.

  Theorem functionify_action :
    ∀ (a : elts A) g, (functionify g) a = g a.
  Proof.
    intros a g.
    unfold functionify.
    destruct constructive_indefinite_description as [g'], a0 as [H0 [H1 H2]].
    apply H2.
  Qed.

End Function_evaluation.

Definition power X Y := {f in P (Y × X) | is_function f Y X}.

Infix "^" := power : set_scope.

Definition inclusion A B := {x in A × B | ∃ a, a ∈ A ∧ x = (a,a)}.

Theorem Inclusion_is_function : ∀ A B, A ⊂ B → is_function (inclusion A B) A B.
Proof.
  intros A B H.
  split.
  - intros x H0.
    now apply Specify_classification in H0.
  - intros a H0.
    exists a.
    repeat split; try now apply H.
    + apply Specify_classification.
      split; try now (exists a).
      rewrite Product_classification.
      exists a, a.
      intuition.
    + intros x' [H1 H2].
      apply Specify_classification in H2.
      destruct H2 as [H2 [z [H3 H4]]].
      rewrite -> Ordered_pair_iff in H4.
      intuition; congruence.
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
    intros x.
    destruct (excluded_middle_informative (x ∈ X)).
    - assert (x ≠ ∅) as H0 by congruence.
      apply Nonempty_classification in H0.
      destruct (constructive_indefinite_description H0) as [y].
      exact y.
    - exact X.
  Defined.

  Lemma choice_function_classification : ∀ x, x ∈ X → choice_function x ∈ x.
  Proof.
    intros x H0.
    unfold choice_function.
    destruct excluded_middle_informative;
      try destruct constructive_indefinite_description; intuition.
  Qed.

  Theorem Choice : ∃ f, domain f = X ∧ range f = ⋃ X  ∧ ∀ x, x ∈ X → f x ∈ x.
  Proof.
    destruct (function_construction X (⋃ X) choice_function)
      as [f [H0 [H1 H2]]].
    { intros a H0.
      rewrite Union_classification.
      eauto using choice_function_classification. }
    exists f.
    repeat split; auto.
    intros x H3.
    rewrite H2; auto using choice_function_classification.
  Qed.

End Choice.

Theorem function_empty_domain : ∀ f, graph f = ∅ ↔ domain f = ∅.
Proof.
  intros f.
  split; intros H; apply NNPP; contradict H.
  - rewrite -> Nonempty_classification in *.
    destruct H as [x H].
    destruct (func_hyp f) as [H0 H1].
    apply H1 in H as [y [H2 H3]].
    exists (x, y); tauto.
  - apply Nonempty_classification in H as [x H].
    destruct (func_hyp f) as [H0 H1].
    apply H0, Product_classification in H as [a [b H]].
    rewrite Nonempty_classification.
    exists a; tauto.
Qed.

Section inverse_functions.

  Variable f : function.
  Hypothesis H : graph f ≠ ∅.

  Notation A := (domain f).
  Notation B := (range f).

  Definition partial_left_inverse : set → set.
  Proof.
    intros b.
    rewrite -> function_empty_domain in H.
    apply Nonempty_classification in H.
    destruct (constructive_indefinite_description H) as [x Hx].
    destruct (excluded_middle_informative (∃ a, a ∈ A ∧ f a = b)) as [e | n].
    - destruct (constructive_indefinite_description e) as [a e0].
      exact a.
    - exact x.
  Defined.

  Theorem left_inverse_iff_injective :
    injective f ↔ ∃ g, domain g = range f ∧ range g = domain f ∧
                       ∀ x, x ∈ domain f → g (f x) = x.
  Proof.
    split; intros H0.
    - destruct (function_construction B A partial_left_inverse) as [g Hg].
      { intros a H1.
        unfold partial_left_inverse.
        repeat destruct excluded_middle_informative;
          repeat destruct constructive_indefinite_description; intuition. }
      exists g; intuition.
      pose proof H2 as H5.
      apply function_maps_domain_to_range, H4 in H5.
      unfold partial_left_inverse in H5.
      repeat destruct excluded_middle_informative;
        repeat destruct constructive_indefinite_description.
      + destruct a as [H6 H7].
        rewrite H5.
        assert ((exist H6) = (exist H2)) by now apply H0, set_proj_injective.
        now inversion H8.
      + contradiction n.
        now (exists x).
    - destruct H0 as [g [H0 [H1 H2]]].
      intros x1 x2 H3.
      unfold lambdaify in H3.
      destruct x1, x2.
      replace x with x0; try apply set_proj_injective; simpl;
        inversion H3 as [H4]; now rewrite <-(H2 _ i), <-(H2 _ i0), H4.
  Qed.

  Theorem right_inverse_iff_surjective_nonempty :
    surjective f ↔ ∃ g, domain g = range f ∧ range g = domain f ∧
                        ∀ y, y ∈ range f → f (g y) = y.
  Proof.
    split; intros H0.
    - destruct (function_construction B A partial_left_inverse) as [g Hg].
      { intros a H1.
        unfold partial_left_inverse.
        repeat destruct excluded_middle_informative;
          repeat destruct constructive_indefinite_description; intuition. }
      exists g; intuition.
      pose proof H2 as H5.
      apply H4 in H5.
      destruct (H0 (exist H2)) as [[x H6] H7].
      simpl in *.
      unfold partial_left_inverse in H5.
      repeat destruct excluded_middle_informative;
        repeat destruct constructive_indefinite_description; subst; try tauto.
      contradiction n.
      exists x; split; auto.
      now inversion H7.
    - destruct H0 as [g [H0 [H1 H2]]].
      intros [b H3].
      assert (g b ∈ A).
      { rewrite <-H1.
        apply function_maps_domain_to_range.
        congruence. }
      exists (exist H4 : elts A).
      simpl.
      now apply set_proj_injective, H2.
  Qed.

End inverse_functions.

Theorem right_inverse_iff_surjective :
  ∀ f, surjective f ↔ ∃ g, domain g = range f ∧ range g = domain f ∧
                           ∀ y, y ∈ range f → f (g y) = y.
Proof.
  intros f.
  destruct (classic (graph f ≠ ∅)) as [H | H];
    eauto using right_inverse_iff_surjective_nonempty.
  apply NNPP in H.
  split; intros H0; apply function_empty_domain in H.
  - assert (range f = ∅).
    { apply NNPP.
      intros H1.
      apply Nonempty_classification in H1 as [y H1].
      destruct (H0 (exist H1)) as [[x H2] H3].
      contradiction (Empty_set_classification x).
      congruence. }
    destruct (function_construction (range f) (domain f) (λ x, x)) as [g Hg].
    { intros a H2.
      contradiction (Empty_set_classification a).
      congruence. }
    exists g; split; intuition.
    contradiction (Empty_set_classification y).
    congruence.
  - destruct H0 as [g [H0 [H1 H2]]].
    intros [y H3].
    exfalso.
    contradiction (Empty_set_classification (g y)).
    rewrite <-H, <-H1.
    apply function_maps_domain_to_range.
    congruence.
Qed.

Theorem Injective_classification : ∀ f, injective f ↔ ∀ x y,
        x ∈ domain f → y ∈ domain f → f x = f y → x = y.
Proof.
  split; intros H.
  - intros x y H0 H1 H2.
    replace x with ((exist H0 : elts (domain f)) : set) by auto.
    replace y with ((exist H1 : elts (domain f)) : set) by auto.
    auto using f_equal, set_proj_injective.
  - intros [x X] [y Y] H0.
    inversion H0.
    auto using set_proj_injective.
Qed.

Theorem Surjective_classification : ∀ f, surjective f ↔ ∀ y,
        y ∈ range f → ∃ x, x ∈ domain f ∧ f x = y.
Proof.
  split; intros H.
  - intros y H0.
    destruct (H (exist H0 : elts (range f))) as [[x X] H1].
    exists x.
    now inversion H1.
  - intros [y Y].
    pose proof (H _ Y) as [x [H0 H1]].
    exists (exist H0 : elts (domain f)).
    now apply set_proj_injective.
Qed.

Definition image (f : function) := {y in range f | ∃ x, x ∈ domain f ∧ f x = y}.

Definition push_forward (f : function) S :=
  {y in range f | ∃ x, x ∈ S ∩ domain f ∧ f x = y}.

Theorem image_subset_range : ∀ f, image f ⊂ range f.
Proof.
  intros f x H.
  now apply Specify_classification in H as [H H0].
Qed.

Theorem push_forward_image: ∀ f S, push_forward f S ⊂ image f.
Proof.
  intros f S x H.
  apply Specify_classification in H as [H [z [H0 H1]]].
  apply Specify_classification.
  split; auto.
  exists z.
  apply Pairwise_intersection_classification in H0 as [H0 H2].
  split; auto.
Qed.

Theorem push_forward_domain : ∀ f, push_forward f (domain f) = image f.
Proof.
  intros f.
  apply Subset_equality; auto using push_forward_image.
  intros x H.
  apply Specify_classification in H.
  apply Specify_classification.
  now rewrite Intersection_idempotent.
Qed.

Theorem function_maps_domain_to_image :
  ∀ f x, x ∈ domain f → f x ∈ image f.
Proof.
  intros f x H.
  apply Specify_classification.
  eauto using function_maps_domain_to_range.
Qed.

Theorem surjective_image : ∀ f, surjective f → range f = image f.
Proof.
  intros f H.
  apply Extensionality.
  split; intros H0.
  - apply Specify_classification.
    rewrite -> Surjective_classification in H.
    split; auto.
  - now apply Specify_classification in H0.
Qed.

Definition empty_function : function.
Proof.
  assert (∀ a : set, a ∈ ∅ → (λ x : set, x) a ∈ ∅) as H by auto.
  apply function_construction in H.
  destruct (constructive_indefinite_description H) as [f i].
  exact f.
Defined.

Definition inverse : function → function.
Proof.
  intros f.
  destruct (excluded_middle_informative (bijective f)).
  - destruct b as [H H0].
    apply right_inverse_iff_surjective in H0.
    destruct (constructive_indefinite_description H0) as [g [H1 [H2 H3]]].
    exact g.
  - exact empty_function.
Defined.

Theorem left_inverse :
  ∀ f, bijective f → ∀ x, x ∈ domain f → inverse f (f x) = x.
Proof.
  intros f H x H0.
  unfold inverse.
  destruct excluded_middle_informative; try tauto.
  destruct b, constructive_indefinite_description as [g].
  repeat destruct a.
  rewrite -> Injective_classification in i.
  apply i; auto.
  - rewrite <-e0.
    apply function_maps_domain_to_range.
    rewrite e.
    now apply function_maps_domain_to_range.
  - rewrite e1; auto.
    now apply function_maps_domain_to_range.
Qed.

Theorem right_inverse :
  ∀ f, bijective f → ∀ x, x ∈ domain (inverse f) → f (inverse f x) = x.
Proof.
  intros f H x H0.
  unfold inverse in *.
  destruct excluded_middle_informative; try tauto.
  destruct b, constructive_indefinite_description as [g].
  repeat destruct a.
  rewrite e1; auto.
  congruence.
Qed.

Theorem inverse_domain : ∀ f, bijective f → domain (inverse f) = range f.
Proof.
  intros f H.
  unfold inverse.
  destruct excluded_middle_informative; try tauto.
  destruct b, constructive_indefinite_description as [g].
  now repeat destruct a.
Qed.

Theorem inverse_range : ∀ f, bijective f → range (inverse f) = domain f.
Proof.
  intros f H.
  unfold inverse.
  destruct excluded_middle_informative; try tauto.
  destruct b, constructive_indefinite_description as [g].
  now repeat destruct a.
Qed.

Theorem inverse_shift_right :
  ∀ f, bijective f → ∀ x y,
      x ∈ range f → y ∈ domain f → inverse f x = y ↔ x = f y.
Proof.
  intros f H x y H0 H1.
  split; intros H2.
  - rewrite <-H2, right_inverse; auto.
    now rewrite inverse_domain.
  - rewrite -> H2, left_inverse; auto.
Qed.

Theorem inverse_bijective : ∀ f, bijective f → bijective (inverse f).
Proof.
  intros f H.
  pose proof H as [H0 H1].
  split.
  - rewrite -> Injective_classification in *.
    intros x y H2 H3 H4.
    rewrite <-(right_inverse f); auto.
    symmetry.
    rewrite <-(right_inverse f), H4; auto.
  - rewrite -> Surjective_classification in *.
    intros y H2.
    exists (f y).
    rewrite -> inverse_domain, left_inverse; repeat split; auto;
      try (now destruct H); try apply function_maps_domain_to_range;
        now rewrite <-inverse_range.
Qed.

Definition composition : function → function → function.
Proof.
  intros f g.
  destruct (excluded_middle_informative (domain f = range g)).
  - assert (∀ x, x ∈ domain g → (λ x, f (g x)) x ∈ range f) as H.
    { intros x H.
      apply function_maps_domain_to_range in H.
      rewrite <-e in H.
      now apply function_maps_domain_to_range in H. }
    apply function_construction in H.
    destruct (constructive_indefinite_description H) as [h i].
    exact h.
  - exact empty_function.
Defined.

Infix "∘" := composition : set_scope.

Theorem Composition_classification :
  ∀ f g, domain f = range g →
         domain (f ∘ g) = domain g ∧ range (f ∘ g) = range f ∧
         ∀ x, x ∈ domain g → (f ∘ g) x = f (g x).
Proof.
  intros f g H.
  unfold composition.
  repeat destruct excluded_middle_informative;
    repeat destruct constructive_indefinite_description; intuition.
Qed.

Theorem composition_injective : ∀ f g,
    domain f = range g → injective f → injective g → injective (f ∘ g).
Proof.
  intros f g H H0 H1 [x X] [y Y] H2.
  destruct (Composition_classification f g) as [H3 [H4 H5]]; try congruence.
  apply set_proj_injective.
  simpl in *.
  inversion H2.
  rewrite -> Injective_classification in H1, H0.
  apply H1; try congruence.
  apply H0; try (rewrite H; apply function_maps_domain_to_range;
                 now rewrite <-H3).
  rewrite <-? H5; congruence.
Qed.

Theorem composition_surjective : ∀ f g,
    domain f = range g → surjective f → surjective g → surjective (f ∘ g).
Proof.
  intros f g H H0 H1 [y Y].
  destruct (Composition_classification f g) as [H2 [H3 H4]]; try congruence.
  rewrite -> Surjective_classification in H0, H1.
  destruct (H0 y) as [z [H5 H6]]; try now rewrite <-H3.
  rewrite H in H5.
  destruct (H1 z) as [x [H7 H8]]; auto.
  rewrite <-H2 in H7.
  exists (exist H7 : elts (domain (f ∘ g))).
  apply set_proj_injective.
  simpl.
  rewrite H4; congruence.
Qed.

Theorem Graph_classification :
  ∀ f z, z ∈ graph f ↔ ∃ a, a ∈ domain f ∧ z = (a, f a).
Proof.
  split; intros H.
  - pose proof (func_hyp f) as [H0 H1].
    apply H0 in H as H2.
    apply Product_classification in H2 as [a [b [H2 [H3 H4]]]].
    exists a.
    split; auto; subst.
    apply H1 in H2 as H4.
    destruct H4 as [z [[H4 H5] H6]].
    eapply Function_classification in H2 as [[H2 H7] H8];
      eauto using (func_hyp f).
    rewrite <-(H6 b), <-(H6 (f a)); auto.
  - destruct H as [a [H H0]].
    subst.
    eapply Function_classification in H as [[H H1] H2];
      eauto using (func_hyp f).
Qed.

Theorem function_graph_uniqueness : ∀ f x a b, x ∈ domain f →
    (x, a) ∈ graph f → (x, b) ∈ graph f → a = b.
Proof.
  intros f x a b H H0 H1.
  pose proof (func_hyp f) as [H2 H3].
  apply H2 in H0 as H6.
  apply Product_classification in H6 as [x' [a' [H6 [H7 H8]]]].
  apply Ordered_pair_iff in H8 as [H8 H9].
  subst.
  apply H2 in H1 as H4.
  apply Product_classification in H4 as [x [a [H4 [H5 H8]]]].
  apply Ordered_pair_iff in H8 as [H8 H9].
  subst.
  apply H3 in H4 as [y [[H4 H8] H9]].
  rewrite <-(H9 a), <-(H9 a'); auto.
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
    split; intros z H.
    - apply Specify_classification in H as [H H0].
      rewrite -> Product_intersection_distr_l,
      Pairwise_intersection_classification.
      apply graph_elements_are_pairs in H as H1.
      split; auto.
      apply Product_classification in H1 as [a [b [H1 [H2 H3]]]]; subst.
      rewrite -> Product_classification, proj1_eval in *; eauto.
    - exists (f z).
      apply Pairwise_intersection_classification in H as [H H0].
      repeat split.
      + auto using function_maps_domain_to_range.
      + apply Specify_classification.
        split.
        * apply function_maps_domain_to_graph;
            auto using function_maps_domain_to_range.
        * rewrite proj1_eval; auto using function_maps_domain_to_range.
      + intros y [H1 H2].
        apply function_maps_domain_to_graph; auto.
        now apply Specify_classification in H2.
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
    rewrite restriction_graph.
    intros z H.
    now apply Specify_classification in H.
  Qed.

  Theorem restriction_action : ∀ x, x ∈ X ∩ domain f → f x = restriction x.
  Proof.
    intros x H.
    apply Pairwise_intersection_classification in H as [H H0].
    unfold restriction.
    apply function_maps_domain_to_graph; simpl; auto.
    - rewrite <-restriction_range.
      apply function_maps_domain_to_range.
      rewrite restriction_domain.
      now apply Pairwise_intersection_classification.
    - apply restriction_subset, Graph_classification.
      exists x.
      now rewrite -> restriction_domain, Pairwise_intersection_classification.
  Qed.

  Theorem restriction_Y_is_function : is_function (graph f) (domain f) Y.
  Proof.
    split; intros z H.
    - apply Graph_classification in H as [a [H H0]]; subst.
      apply Product_classification.
      exists a, (f a).
      eauto using function_maps_domain_to_image.
    - exists (f z).
      repeat split.
      + eauto using function_maps_domain_to_image.
      + apply Graph_classification; eauto.
      + intros x' [H0 H1].
        apply Graph_classification in H1 as [a [H1 H2]].
        apply Ordered_pair_iff in H2 as [H2 H3]; now subst.
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
    intros a H.
    apply function_maps_domain_to_graph; auto.
    - rewrite restriction_Y_range.
      auto using function_maps_domain_to_image.
    - rewrite restriction_Y_graph.
      apply function_maps_domain_to_graph;
        auto using function_maps_domain_to_range.
  Qed.

End Restrictions.

Arguments restriction_Y {f Y}.
Arguments restriction_Y_domain {f Y}.
Arguments restriction_Y_range {f Y}.
Arguments restriction_Y_action {f Y}.

Section Quotient_maps.

  Context {X : set}.
  Variable R : set.

  Definition quotient_map : elts X → elts (X/R).
  Proof.
    intros [x H].
    assert ({z in X | (x,z) ∈ R} ∈ X/R).
    { apply quotient_classification.
      split.
      - intros y H0.
        now rewrite -> Specify_classification in *.
      - exists x.
        repeat split; auto; rewrite -> Specify_classification in *; intuition. }
    exact (exist H0).
  Defined.

End Quotient_maps.

Theorem quotient_lift : ∀ {X R : set} (y : elts (X/R)),
  ∃ x : elts X, quotient_map R x = y.
Proof.
  intros X R y.
  unfold quotient in *.
  destruct y as [y H].
  pose proof H as H0.
  apply quotient_classification in H0 as [H0 [x [H1 H2]]].
  exists (exist H1 : elts X).
  apply set_proj_injective.
  simpl in *.
  apply replacement_classification in H as [γ H]; subst.
  apply Extensionality; split; intros H3.
  - now apply Specify_classification, H2 in H3.
  - now apply Specify_classification, H2.
Qed.

Theorem quotient_equiv : ∀ X R (x y : elts X),
    is_equivalence X R → quotient_map R x = quotient_map R y ↔ (x, y) ∈ R.
Proof.
  intros X R [x A] [y B] [H [H0 H1]].
  split; intros H2.
  - assert ({z in X | (x, z) ∈ R} = {z in X | (y, z) ∈ R}) as H3 by
          now inversion H2.
    simpl.
    apply Subset_equality_iff in H3 as [H4 H5].
    pose proof (H5 y) as H6.
    rewrite -> ? Specify_classification in H6.
    apply H6.
    auto.
  - apply set_proj_injective.
    simpl in *.
    apply Extensionality.
    split; intros H3; rewrite -> Specify_classification in *; split; try tauto;
      [ apply (H1 y x) | eapply H1 ]; eauto; intuition.
Qed.

Theorem quotient_image :
  ∀ X R (x : elts X), {z in X | (x,z) ∈ R} = quotient_map R x.
Proof.
  now intros X R [x H].
Qed.

Theorem no_quines : ∀ x, ¬ x ∈ x.
Proof.
  intros x H.
  destruct (Regularity {x,x}) as [y [H0 H1]].
  - exists x.
    now apply Singleton_classification.
  - contradict H1.
    exists x.
    split.
    + apply Singleton_classification in H0.
      now subst.
    + now apply Singleton_classification.
Qed.

Theorem no_loops : ∀ x y, ¬ (x ∈ y ∧ y ∈ x).
Proof.
  intros x y [H H0].
  destruct (Regularity {x,y}) as [z [H1 H2]].
  - exists x.
    apply Pairing_classification; auto.
  - contradict H2.
    apply Pairing_classification in H1.
    wlog: x y H H0 H1 / z = x.
    + intros x0.
      destruct H1; [ | rewrite Pairing_comm ]; auto.
    + exists y.
      subst.
      rewrite Pairing_classification.
      tauto.
Qed.

Lemma disjoint_succ : ∀ s, s ∩ {s,s} = ∅.
Proof.
  intros s.
  apply Extensionality.
  split; intros H.
  - apply Pairwise_intersection_classification in H as [H H0].
    apply Singleton_classification in H0.
    subst.
    contradiction (no_quines s).
  - contradiction (Empty_set_classification z).
Qed.

Theorem disjoint_union_complement : ∀ E F, E ∪ F = E ∪ (F \ E).
Proof.
  intros E F.
  apply Extensionality.
  split; intros H; apply Pairwise_union_classification;
    apply Pairwise_union_classification in H as [H | H]; try tauto.
  - destruct (classic (z ∈ E)); try tauto.
    right.
    now apply Complement_classification.
  - apply Complement_classification in H as [H H0].
    tauto.
Qed.

Lemma in_succ : ∀ s, s ∈ succ s.
Proof.
  intros s.
  unfold succ.
  rewrite -> Pairwise_union_classification, Singleton_classification.
  now right.
Qed.

Lemma subset_succ : ∀ s, s ⊂ succ s.
Proof.
  intros s x H.
  unfold succ.
  rewrite Pairwise_union_classification.
  now left.
Qed.

Theorem complement_disjoint_union : ∀ E F, E ∩ F = ∅ → (E ∪ F) \ F = E.
Proof.
  intros E F H.
  apply Extensionality.
  split; intros H0.
  - apply Complement_classification in H0 as [H0 H1].
    apply Pairwise_union_classification in H0 as [H0 | H0]; tauto.
  - apply Complement_classification.
    split.
    + apply Pairwise_union_classification; tauto.
    + intros H1.
      contradiction (Empty_set_classification z).
      rewrite <-H.
      now apply Pairwise_intersection_classification.
Qed.

Theorem disjoint_intersection_complement : ∀ E F, E ∩ (F \ E) = ∅.
Proof.
  intros E F.
  apply Extensionality.
  split; intros H; rewrite -> Pairwise_intersection_classification in *.
  - rewrite -> Complement_classification in *.
    tauto.
  - contradiction (Empty_set_classification z).
Qed.

Theorem complement_union_intersection : ∀ E F, (F \ E) ∪ (E ∩ F) = F.
Proof.
  intros E F.
  apply Extensionality.
  split; intros H;
    rewrite -> Pairwise_union_classification, Complement_classification,
    Pairwise_intersection_classification in *.
  - tauto.
  - destruct (classic (z ∈ E)); tauto.
Qed.

Theorem complement_disjoint_intersection : ∀ E F, (F \ E) ∩ (E ∩ F) = ∅.
Proof.
  intros E F.
  apply Extensionality.
  split; intros H.
  - rewrite -> ? Pairwise_intersection_classification,
    Complement_classification in *.
    tauto.
  - contradiction (Empty_set_classification z).
Qed.

Theorem complement_subset : ∀ E F, F \ E ⊂ F.
Proof.
  intros E F x H.
  now apply Complement_classification in H as [H].
Qed.

Theorem Intersection_left : ∀ E F, E ∩ F ⊂ E.
Proof.
  intros E F x H.
  rewrite -> Pairwise_intersection_classification in H.
  tauto.
Qed.

Theorem Intersection_right : ∀ E F, E ∩ F ⊂ F.
Proof.
  intros E F x H.
  rewrite -> Pairwise_intersection_classification in H.
  tauto.
Qed.

Theorem power_0_l : ∀ m, m ≠ ∅ → ∅^m = ∅.
Proof.
  intros m H.
  apply Extensionality.
  split; intros H0.
  - apply Specify_classification in H0 as [H0 [H1 H2]].
    pose proof H as H3.
    apply Nonempty_classification in H3 as [x H3].
    apply H2 in H3 as [y [[H3 H4] _]].
    contradiction (Empty_set_classification y).
  - contradiction (Empty_set_classification z).
Qed.

Theorem power_0_r : ∀ m, m^∅ = succ ∅.
Proof.
  intros m.
  apply Extensionality.
  split; intros H.
  - apply Specify_classification in H as [H [H0 H1]].
    rewrite Empty_product_left in H.
    apply Powerset_classification in H.
    assert (z = ∅).
    { apply Extensionality.
      split; intros H2; auto.
      contradiction (Empty_set_classification z0). }
    subst.
    apply Pairwise_union_classification.
    rewrite Singleton_classification.
    tauto.
  - apply Pairwise_union_classification in H as [H | H].
    + contradiction (Empty_set_classification z).
    + rewrite -> Singleton_classification in H.
      subst.
      apply Specify_classification.
      repeat split.
      * apply Empty_set_in_powerset.
      * apply Empty_set_is_subset.
      * intros a H.
        contradiction (Empty_set_classification a).
Qed.

Definition inverse_image_of_element f y := {x in domain f | f x = y}.

Theorem Inverse_image_classification : ∀ f a b,
    a ∈ domain f → b ∈ range f → a ∈ inverse_image_of_element f b ↔ f a = b.
Proof.
  intros f a b H H0.
  split; intros H1; unfold inverse_image_of_element in *;
    rewrite -> Specify_classification in *; tauto.
Qed.

Theorem Inverse_image_classification_domain : ∀ f a b,
    b ∈ range f → a ∈ inverse_image_of_element f b → a ∈ domain f.
Proof.
  intros f a b H H0.
  unfold inverse_image_of_element in *.
  apply Specify_classification in H0; tauto.
Qed.

Theorem Inverse_image_classification_left : ∀ f a b,
    b ∈ range f → a ∈ inverse_image_of_element f b → f a = b.
Proof.
  intros f a b H H0.
  unfold inverse_image_of_element in *.
  apply Specify_classification in H0; tauto.
Qed.

Theorem Inverse_image_subset : ∀ f b,
    b ∈ range f → inverse_image_of_element f b ⊂ domain f.
Proof.
  intros f b H a H0.
  unfold inverse_image_of_element in H0.
  apply Specify_classification in H0; tauto.
Qed.

Theorem function_graph_equality : ∀ A B g1 g2,
    is_function g1 A B → is_function g2 A B → g1 ⊂ g2 → g1 = g2.
Proof.
  intros A B g1 g2 H H0 H1.
  apply Subset_equality_iff.
  split; auto.
  intros z H2.
  set (f1 := mkFunc H).
  set (f2 := mkFunc H0).
  unfold is_function in *.
  replace g2 with (graph f2) in H2 by auto.
  apply Graph_classification in H2 as [z1 [H2 H3]].
  subst.
  replace g1 with (graph f1) by auto.
  apply Graph_classification.
  exists z1.
  simpl in *.
  split; auto.
  assert ((z1, f1 z1) ∈ g2) as H3.
  { apply H1.
    replace g1 with (graph f1) by auto.
    apply Graph_classification.
    exists z1.
    now simpl. }
  assert ((z1, f2 z1) ∈ g2) as H4.
  { replace g2 with (graph f2) by auto.
    apply Graph_classification.
    exists z1.
    now simpl. }
  pose proof H0 as H5.
  apply H5 in H2 as H6.
  destruct H6 as [z1' [[H6 H7] H8]].
  rewrite <-? (H8 (f1 z1)), <-? (H8 (f2 z1)); split; auto;
    [ replace B with (range f2) by auto | replace B with (range f1) by auto ];
    apply function_maps_domain_to_range; now simpl.
Qed.

Theorem singleton_products : ∀ x y, {x,x} × {y,y} = {(x,y), (x,y)}.
Proof.
  intros x y.
  apply Extensionality.
  split; intros H.
  - apply Product_classification in H as [a [b [H H0]]].
    rewrite -> Singleton_classification in *.
    intuition; congruence.
  - apply Product_classification.
    exists x, y.
    now rewrite -> ? Singleton_classification in *.
Qed.

Theorem singleton_functions :
  ∀ f x y, domain f = {x,x} → range f = {y,y} → graph f = {(x,y), (x,y)}.
Proof.
  intros f x y H H0.
  apply (function_graph_equality {x,x} {y,y}).
  - pose proof (func_hyp f).
    congruence.
  - split.
    + rewrite singleton_products.
      apply Set_is_subset.
    + intros a H2.
      exists y.
      split.
      * rewrite -> ? Singleton_classification in *.
        now subst.
      * intros x' H4.
        rewrite -> ? Singleton_classification, Ordered_pair_iff in *.
        intuition; congruence.
  - pose proof func_hyp f as [H1].
    now rewrite -> H, H0, singleton_products in *.
Qed.

Theorem domain_uniqueness : ∀ f A1 A2 B,
    is_function f A1 B → is_function f A2 B → A1 = A2.
Proof.
  intros f A1 A2 B [H H0] [H1 H2].
  apply Extensionality.
  intros z.
  wlog: f A1 A2 B H H0 H1 H2 / z ∈ A1.
  - split; intros H3; [ apply (x f A1 A2 B) | apply (x f A2 A1 B) ]; auto.
  - split; intros H4; try tauto; clear H4.
    apply H0 in H3 as [y [[H3 H4] H5]].
    apply H1 in H4.
    apply Specify_classification in H4 as [H4 [a [b [H6 [H7 H8]]]]].
    apply Ordered_pair_iff in H8 as [H8 H9].
    now subst.
Qed.

Theorem function_record_injective : ∀ f g,
    range f = range g → graph f = graph g → f = g.
Proof.
  intros f g H H0.
  destruct f, g.
  simpl in *.
  subst.
  assert (domain0 = domain1) by eauto using domain_uniqueness.
  subst.
  now replace func_hyp0 with func_hyp1 by apply proof_irrelevance.
Qed.

Lemma func_ext_lemma : ∀ f g,
    range f = range g → (∀ x, x ∈ domain f → f x = g x)
    → graph f ⊂ graph g.
Proof.
  intros f g H H0 z H1.
  apply Graph_classification in H1 as [a [H1 H2]].
  apply Graph_classification.
  exists a.
  rewrite <-H0; repeat split; try congruence.
  apply NNPP.
  intros H3.
  apply H0 in H1 as H4.
  unfold eval in H4 at 2.
  unfold eval_rel in H4.
  destruct excluded_middle_informative; try tauto.
  contradiction (outsider_not_in (range g)).
  rewrite <-H4, <-H.
  now apply function_maps_domain_to_range.
Qed.

Theorem func_ext : ∀ f g, domain f = domain g → range f = range g
                          → (∀ x, x ∈ domain f → f x = g x) → f = g.
Proof.
  intros f g H H0 H1.
  apply function_record_injective; try congruence.
  apply Subset_equality_iff.
  pose proof H1 as H2.
  rewrite H in H2.
  split; apply func_ext_lemma; auto using eq_sym.
Qed.

Theorem function_inv_inv : ∀ f, bijective f → inverse (inverse f) = f.
Proof.
  intros f H.
  apply func_ext.
  - rewrite -> inverse_domain, inverse_range; auto using inverse_bijective.
  - rewrite -> inverse_range, inverse_domain; auto using inverse_bijective.
  - intros x H0.
    rewrite -> inverse_domain, inverse_range in H0;
      assert (bijective (inverse f)) as H1; auto using inverse_bijective.
    pose proof H1 as [H2 H3].
    rewrite -> Injective_classification in H2.
    apply H2.
      * rewrite <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite -> inverse_domain, inverse_range; auto.
      * rewrite inverse_domain; auto.
        now apply function_maps_domain_to_range.
      * rewrite -> left_inverse, right_inverse; auto.
        rewrite -> inverse_domain, inverse_range; auto.
Qed.

Lemma Euler_Phi_lemma :
  ∀ A B C D, A = B → A ∩ C = ∅ → B ∩ D = ∅ → A ∪ C = B ∪ D → C = D.
Proof.
  intros A B C D H H0 H1 H2.
  rewrite -> Intersection_comm, Union_comm, (Union_comm B D) in *.
  apply complement_disjoint_union in H0, H1.
  now rewrite <-H0, <-H1, H2, H.
Qed.

Definition swap_product (S T : set) : elts (S × T) → elts (T × S).
Proof.
  intros z.
  pose proof (elts_in_set z).
  apply Product_classification in H.
  destruct (constructive_indefinite_description H) as [x H0].
  destruct (constructive_indefinite_description H0) as [y [H1 [H2 H3]]].
  assert ((y, x) ∈ T × S) as H4.
  { apply Product_classification; eauto. }
  exact (exist H4).
Defined.

Definition swap_function S T := functionify (swap_product S T).

Theorem swap_domain : ∀ S T, domain (swap_function S T) = S × T.
Proof.
  intros S T.
  apply functionify_domain.
Qed.

Theorem swap_range : ∀ S T, range (swap_function S T) = T × S.
Proof.
  intros S T.
  apply functionify_range.
Qed.

Theorem swap_action : ∀ S T x y,
    x ∈ S → y ∈ T → swap_function S T (x, y) = (y, x).
Proof.
  intros S T x y H H0.
  assert ((x, y) ∈ S × T) as H1.
  { apply Product_classification; eauto. }
  unfold swap_function, swap_product.
  rewrite -> (reify H1), functionify_action.
  repeat destruct constructive_indefinite_description.
  repeat destruct a.
  destruct Product_classification.
  simpl in *.
  apply Ordered_pair_iff in e0 as [H2 H3].
  congruence.
Qed.

Theorem swap_bijective : ∀ S T, bijective (swap_function S T).
Proof.
  split.
  - apply Injective_classification.
    intros z1 z2 H H0 H1.
    rewrite -> swap_domain in *.
    apply Product_classification in H as
        [x [y [H [H2 H3]]]], H0 as [x' [y' [H4 [H5 H6]]]].
    subst.
    rewrite ? swap_action in H1; auto.
    apply Ordered_pair_iff in H1; intuition; congruence.
  - apply Surjective_classification.
    intros z H.
    rewrite -> swap_domain, swap_range in *.
    apply Product_classification in H as [x [y [H [H0 H1]]]].
    subst.
    exists (y, x).
    rewrite -> Product_classification, swap_action; try split; eauto.
Qed.
