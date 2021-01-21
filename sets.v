Require Export logic_axioms Basics.

(* Beginning of axioms. *)

Parameter set : Type.
Parameter IN: set → set → Prop.
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

Definition elts (S : set) := {x : set | x ∈ S}.

Theorem Empty_Set : ∃ w, ∀ x, x ∉ w.
Proof.
  destruct Infinity as [x [[w [H H0]] H1]].
  eauto.
Qed.

Definition empty_set : set.
Proof.
  destruct (constructive_indefinite_description _ Empty_Set) as [w].
  exact w.
Defined.

Notation "∅" := empty_set : set_scope.

Theorem Empty_set_classification : ∀ w, w ∉ ∅.
Proof.
  unfold empty_set.
  now destruct constructive_indefinite_description.
Qed.

Theorem Nonempty_classification : ∀ y, y ≠ ∅ ↔ ∃ x, x ∈ y.
Proof.
  split; intros H.
  - apply NNPP.
    contradict H.
    apply Extensionality.
    split; intros.
    + contradict H.
      now (exists z).
    + now apply Empty_set_classification in H0.
  - intros H0.
    destruct H as [x H].
    contradiction (Empty_set_classification x).
    congruence.
Qed.

(* The axiom of specification is a theorem in ZFC under classical logic. *)
Theorem Specification : ∀ z p, ∃ y, ∀ x, (x ∈ y ↔ (x ∈ z ∧ (p x))).
Proof.
  intros z p.
  destruct (classic (∃ x, x ∈ z ∧ p x)) as [[e [H H0]] | H].
  - destruct (Replacement z (λ x y, p x ∧ x = y ∨ ¬ p x ∧ e = y)).
    + intros x H1.
      destruct (classic (p x)); [ exists x | exists e ];
        split; auto; intros x' H3; tauto.
    + exists x.
      split; intros H2.
      * apply H1 in H2 as [w [H2 [[H3 H4] | [H3 H4]]]]; now subst.
      * destruct H2 as [H2 H3].
        apply H1.
        eauto.
  - exists ∅.
    split; intros H0.
    + contradiction (Empty_set_classification x).
    + exfalso; eauto.
Qed.

Definition specify : set → (set → Prop) → set.
Proof.
  intros A p.
  destruct (constructive_indefinite_description _ (Specification A p)) as [S].
  exact S.
Defined.

Notation "{ x 'in' A | P }" := (specify A (λ x, P)) : set_scope.

Definition subset a b := ∀ x, x ∈ a → x ∈ b.
Infix "⊂" := subset (at level 70) : set_scope.

Definition P : set → set.
Proof.
  intros x.
  destruct (constructive_indefinite_description _ (Powerset x)) as [y].
  exact {s in y | s ⊂ x}.
Defined.

Theorem Empty_set_is_subset : ∀ X, ∅ ⊂ X.
Proof.
  intros X z H.
  now apply Empty_set_classification in H.
Qed.

Theorem Set_is_subset : ∀ X, X ⊂ X.
Proof.
  firstorder.
Qed.

Theorem Powerset_classification : ∀ X x, x ∈ P X ↔ x ⊂ X.
Proof.
  intros X.
  unfold P, specify.
  repeat destruct constructive_indefinite_description.
  split; [ | intros H ]; apply i0; split; auto.
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
  intros x H.
  contradiction (Empty_set_classification x).
  rewrite H.
  now apply Set_in_powerset.
Qed.

Lemma Subset_of_subsets_of_emptyset : ∀ a, a ∈ P (P ∅) → a = ∅ ∨ a = P ∅.
Proof.
  intros a H.
  destruct (classic (a = ∅)); try tauto.
  right.
  apply Extensionality.
  - split; intros H1.
    + apply Powerset_classification in H.
      now apply H in H1.
    + apply Powerset_classification in H1.
      replace z with ∅ in *.
      * apply Powerset_classification in H.
        apply Nonempty_classification in H0 as [x H0].
        apply H in H0 as H2.
        apply Powerset_classification in H2.
        replace x with ∅ in *; auto.
        apply Extensionality.
        split; intros H3; auto.
        contradiction (Empty_set_classification z0).
      * apply Extensionality.
        split; intros H2; auto.
        contradiction (Empty_set_classification z0).
Qed.

(* The axiom of pairing is a theorem in ZFC under classical logic. *)
Theorem Pairing : ∀ x y, ∃ z, ((x ∈ z) ∧ (y ∈ z)).
Proof.
  intros x y.
  destruct (Replacement (P (P ∅)) (λ a b, ∅ = a ∧ x = b ∨ P ∅ = a ∧ y = b))
    as [z H].
  - intros a H.
    apply Subset_of_subsets_of_emptyset in H as [H | H];
      [ exists x | exists y ]; split; auto; intros x' [[H0 H1] | [H0 H1]];
        auto; contradiction (Powerset_nonempty ∅); congruence.
  - exists z; split; apply H; [ exists ∅ | exists (P ∅) ];
      split; eauto using Empty_set_in_powerset, Set_in_powerset.
Qed.

Definition pair : set → set → set.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (Pairing x y)) as [z].
  exact {t in z | t = x ∨ t = y}.
Defined.

Notation " { x , y } " := (pair x y) : set_scope.
Notation " { x } " := (pair x x) : set_scope.

Definition union : set → set.
Proof.
  intros F.
  destruct (constructive_indefinite_description _ (Union F)) as [A].
  exact {x in A | ∃ y, (x ∈ y ∧ y ∈ F)}.
Defined.

Notation "⋃ x" := (union x) (at level 60) : set_scope.

Definition pairwise_union A B := (⋃ {A, B}).

Infix "∪" := pairwise_union (at level 60) : set_scope.

Definition succ w := w ∪ {w, w}.

Definition Inductive X := ∀ y, y ∈ X → succ y ∈ X.

Lemma neq_sym : ∀ a b : set, a ≠ b ↔ b ≠ a.
Proof.
  split; intros H; now contradict H.
Qed.

Theorem Specify_classification : ∀ A P x, x ∈ {x in A | P x} ↔ x ∈ A ∧ P x.
Proof.
  intros A P x.
  unfold specify in *.
  repeat destruct constructive_indefinite_description.
  split; intros H; now apply i.
Qed.

Theorem Specify_subset : ∀ A P, {x in A | P x} ⊂ A.
Proof.
  intros A P x H.
  apply Specify_classification in H.
  tauto.
Qed.

Lemma Pairing_classification : ∀ x y z, z ∈ {x,y} ↔ (z = x ∨ z = y).
Proof.
  intros x y z.
  unfold pair, specify.
  repeat destruct constructive_indefinite_description.
  split; intros H.
  - apply i in H as [H [H0 | H0]]; auto.
  - destruct H as [H | H]; apply i; intuition; congruence.
Qed.

Lemma Singleton_classification : ∀ x y, y ∈ {x,x} ↔ y = x.
Proof.
  intros x y.
  split; intros H; auto; rewrite Pairing_classification in *; tauto.
Qed.

Definition proper_subset a b := a ⊂ b ∧ a ≠ b.
Infix "⊊" := proper_subset (at level 70) : set_scope.

Lemma not_proper_subset_inhab : ∀ x y, ¬ x ⊊ y → x ≠ y → ∃ z, z ∈ x ∧ z ∉ y.
Proof.
  intros x y H H0.
  apply NNPP.
  contradict H.
  split; try now contradict H0.
  intros z H1.
  apply NNPP.
  contradict H.
  now (exists z).
Qed.

Theorem Subset_transitive : ∀ X Y Z, X ⊂ Y → Y ⊂ Z → X ⊂ Z.
Proof.
  intros X Y Z H H0 x H1.
  eauto.
Qed.

Theorem Subset_equality : ∀ A B, A ⊂ B → B ⊂ A → A = B.
Proof.
  intros A B H H0.
  apply Extensionality; intuition.
Qed.

Theorem Subset_equality_iff : ∀ A B, (A ⊂ B ∧ B ⊂ A) ↔ A = B.
Proof.
  intros A B.
  split; intros H; subst; firstorder using Subset_equality, Set_is_subset.
Qed.

Theorem subset_subsetneq_trans : ∀ A B C, A ⊂ B → B ⊊ C → A ⊊ C.
Proof.
  intros A B C H [H0 H1].
  split.
  - intros a H2.
    auto.
  - intros H2.
    subst.
    contradict H1.
    now apply Subset_equality_iff.
Qed.

Theorem subsetneq_subset_trans : ∀ A B C, A ⊊ B → B ⊂ C → A ⊊ C.
Proof.
  intros A B C [H H0] H1.
  split.
  - intros a H2.
    auto.
  - intros H2.
    subst.
    contradict H0.
    now apply Subset_equality_iff.
Qed.

Lemma proper_subset_inhab : ∀ x y, x ⊊ y → ∃ z, z ∈ y ∧ z ∉ x.
Proof.
  intros x y [H H0].
  apply NNPP.
  contradict H0.
  apply Subset_equality_iff.
  split; auto.
  intros z H1.
  apply NNPP.
  contradict H0.
  eauto.
Qed.

Theorem Union_classification : ∀ x C, x ∈ ⋃ C ↔ ∃ X, X ∈ C ∧ x ∈ X.
Proof.
  intros x C.
  unfold union, specify in *.
  repeat destruct constructive_indefinite_description.
  split; intros H; [ apply i0 in H as [H [y H0]]
                   | destruct H as [y H]; apply i0 ]; firstorder.
Qed.

Theorem Empty_union : ⋃ ∅ = ∅.
Proof.
  apply Extensionality.
  split; intros H; rewrite Union_classification in *;
    repeat destruct H; now apply Empty_set_classification in H.
Qed.

Lemma Pairwise_union_classification :
  ∀ A B x, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B.
Proof.
  intros A B x.
  unfold pairwise_union.
  split; intros H; rewrite Union_classification in *; repeat destruct H;
    try rewrite Pairing_classification in *; try destruct H; subst; auto;
  [ exists A | exists B ]; split; try rewrite Pairing_classification; tauto.
Qed.

Theorem Singleton_union : ∀ A, ⋃ {A, A} = A.
Proof.
  intros A.
  apply Extensionality.
  split; intros H; [ apply Pairwise_union_classification in H |
                     apply Pairwise_union_classification ]; tauto.
Qed.

Theorem Union_comm : ∀ A B, A ∪ B = B ∪ A.
Proof.
  intros A B.
  apply Extensionality.
  split; intros H; rewrite Pairwise_union_classification in *; tauto.
Qed.

Theorem Union_assoc : ∀ A B C, A ∪ (B ∪ C) = (A ∪ B) ∪ C.
Proof.
  intros A B C.
  apply Extensionality.
  split; intros H; repeat rewrite Pairwise_union_classification in *; tauto.
Qed.

Theorem Union_empty : ∀ A, A ∪ ∅ = A.
Proof.
  intros A.
  apply Extensionality.
  split; intros H; rewrite Pairwise_union_classification in *;
    intuition; now apply Empty_set_classification in H0.
Qed.

Theorem Union_idempotent : ∀ A, A ∪ A = A.
Proof.
  intros A.
  apply Extensionality.
  split; intros H; repeat rewrite Pairwise_union_classification in *; tauto.
Qed.

Theorem Union_subset : ∀ A B, A ⊂ B ↔ A ∪ B = B.
Proof.
  intros A B.
  rewrite <-Subset_equality_iff.
  split; intros H; repeat split; intros x H0;
    try rewrite Pairwise_union_classification in *;
    firstorder; firstorder using Pairwise_union_classification.
Qed.

Definition intersection X := {y in ⋃ X | ∀ x, x ∈ X → y ∈ x}.

Notation "⋂ x" := (intersection x) (at level 60) : set_scope.

Definition pairwise_intersection A B := (⋂ {A, B}).

Infix "∩" := pairwise_intersection (at level 60) : set_scope.

Theorem Intersection_classification : ∀ C,
    C ≠ ∅ → ∀ x, x ∈ ⋂ C ↔ ∀ X, X ∈ C → x ∈ X.
Proof.
  intros C H x.
  apply Nonempty_classification in H as [z H].
  unfold intersection, union, specify in *.
  repeat destruct constructive_indefinite_description.
  split; intros H0.
  - intros X H1.
    apply i in H0 as [H0 H2].
    eauto.
  - apply i.
    split; intuition.
    apply i1; firstorder.
Qed.

Theorem Pairwise_intersection_classification :
  ∀ A B x, x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B.
Proof.
  intros A B x.
  split; intros H; unfold pairwise_intersection in *;
    rewrite Intersection_classification in *;
    try (apply Nonempty_classification; exists A;
         apply Pairing_classification; tauto).
  - split; apply H; apply Pairing_classification; tauto.
  - intros X H0.
    apply Pairing_classification in H0 as [H0 | H0]; subst; tauto.
Qed.

Theorem Empty_intersection : (⋂ ∅ = ∅).
Proof.
  unfold intersection, specify.
  repeat destruct constructive_indefinite_description.
  apply Extensionality.
  split; intros H; try apply i in H as [H H0]; rewrite Empty_union in *;
    now apply Empty_set_classification in H.
Qed.

Theorem Intersection_empty : ∀ A, A ∩ ∅ = ∅.
Proof.
  intros A.
  apply Extensionality.
  split; intros H; rewrite Pairwise_intersection_classification in *;
    intuition; now apply Empty_set_classification in H.
Qed.

Theorem Intersection_comm : ∀ A B, A ∩ B = B ∩ A.
Proof.
  intros A B.
  apply Extensionality.
  split; intros H; rewrite Pairwise_intersection_classification in *; tauto.
Qed.

Theorem Intersection_assoc : ∀ A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof.
  intros A B C.
  apply Extensionality.
  split; intros H; repeat rewrite Pairwise_intersection_classification in *;
    tauto.
Qed.

Theorem Intersection_idempotent : ∀ A, A ∩ A = A.
Proof.
  intros A.
  apply Extensionality.
  split; intros H; repeat rewrite Pairwise_intersection_classification in *;
    tauto.
Qed.

Theorem Intersection_subset : ∀ A B, A ⊂ B ↔ A ∩ B = A.
Proof.
  intros A B.
  rewrite <-Subset_equality_iff.
  split; intros H; repeat split; intros x H0;
    try rewrite Pairwise_intersection_classification in *; eauto; try tauto.
  destruct H as [H H1].
  apply H1 in H0.
  rewrite Pairwise_intersection_classification in H0.
  tauto.
Qed.

Theorem Intersection_union : ∀ A B C, A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C).
Proof.
  intros A B C.
  apply Extensionality.
  split; intros H;
    repeat rewrite Pairwise_union_classification,
    Pairwise_intersection_classification in *; tauto.
Qed.

Theorem Union_intersection : ∀ A B C, A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C).
Proof.
  intros A B C.
  apply Extensionality.
  split; intros H;
    repeat rewrite Pairwise_intersection_classification,
    Pairwise_union_classification in *; tauto.
Qed.

Theorem Halmos_4_1 : ∀ A B C, (A ∩ B) ∪ C = A ∩ (B ∪ C) ↔ C ⊂ A.
Proof.
  intros A B C.
  split; intros H.
  - apply Subset_equality_iff in H as [H H0].
    intros x H1.
    pose proof (H x).
    repeat rewrite Pairwise_intersection_classification,
    Pairwise_union_classification in *.
    tauto.
  - apply Extensionality.
    intros z; split; intros H0;
      repeat rewrite Pairwise_union_classification,
      Pairwise_intersection_classification,
      Pairwise_union_classification in *; pose proof (H z); tauto.
Qed.

Definition complement A B := {x in A | x ∉ B}.

Infix "\" := complement (at level 45) : set_scope.

Theorem Complement_classification : ∀ A B x, x ∈ A \ B ↔ x ∈ A ∧ x ∉ B.
Proof.
  intros A B x.
  unfold complement, specify.
  repeat destruct constructive_indefinite_description.
  auto.
Qed.

Theorem Complement_subset : ∀ A B, A ⊂ B ↔ A \ B = ∅.
Proof.
  intros A B.
  split; intros H.
  - apply Extensionality; split; intros;
      rewrite Complement_classification in *;
      firstorder using Empty_set_classification.
  - apply Subset_equality_iff in H as [H H0].
    intros x H1.
    apply NNPP.
    intros H2.
    eapply Empty_set_classification.
    apply H.
    rewrite Complement_classification in *.
    eauto.
Qed.

Theorem Complement_intersection : ∀ A B, A \ (A \ B) = A ∩ B.
Proof.
  intros A B.
  apply Extensionality.
  split; intros H; rewrite Pairwise_intersection_classification in *;
    repeat rewrite Complement_classification in *;
    pose proof (classic (z ∈ B)); tauto.
Qed.

Theorem Intersection_complement : ∀ A B C, A ∩ (B \ C) = (A ∩ B) \ (A ∩ C).
Proof.
  intros A B C.
  apply Extensionality.
  split; intros H; repeat rewrite Complement_classification,
                   Pairwise_intersection_classification in *; tauto.
Qed.

Definition ordered_pair x y := {{x,x},{x,y}}.

Notation " ( x , y ) " := (ordered_pair x y) : set_scope.

Lemma Ordered_pair_iff_left : ∀ a b c d, (a,b) = (c,d) → a = c.
Proof.
  intros a b c d H.
  unfold ordered_pair in *.
  assert ({a,a} ∈ {{c,c}, {c,d}}) as H0
      by (rewrite <-H; apply Pairing_classification; auto).
  apply Pairing_classification in H0 as [H0 | H0]; symmetry;
    apply Singleton_classification; rewrite H0;
      apply Pairing_classification; auto.
Qed.

Theorem Ordered_pair_iff : ∀ a b c d, (a, b) = (c, d) ↔ (a = c ∧ b = d).
Proof.
  intros a b c d.
  unfold ordered_pair in *.
  split; intros H; intuition; try congruence;
    eauto using Ordered_pair_iff_left.
  assert ({a,b} ∈ {{c,c}, {c,d}}) as H0
      by (rewrite <-H; apply Pairing_classification; auto).
  apply Pairing_classification in H0 as [H0 | H0].
  - replace d with c.
    + apply Singleton_classification.
      rewrite <-H0; apply Pairing_classification; auto.
    + assert ({c,d} ∈ {{a,a},{a,b}}) as H2
        by (rewrite H; apply Pairing_classification; auto).
      apply Pairing_classification in H2 as [H2 | H2];
        replace c with a in *; symmetry; [ | | | symmetry ];
          apply Singleton_classification; rewrite <-H0, <-H2 in *;
            [ | | | rewrite H2 in * ]; apply Pairing_classification; auto.
  - assert (d ∈ {a,b}) as H1
        by (rewrite H0; apply Pairing_classification; auto).
    apply Pairing_classification in H1 as [H1 | H1]; subst; auto.
    apply Ordered_pair_iff_left in H.
    apply Singleton_classification.
    subst; rewrite <-H0; apply Pairing_classification; auto.
Qed.

Definition product A B :=
  {x in P (P (A ∪ B)) | ∃ a b, a ∈ A ∧ b ∈ B ∧ x = (a,b)}.

Infix "×" := product (at level 60) : set_scope.

Theorem Product_classification : ∀ A B x,
    x ∈ A × B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ x = (a,b).
Proof.
  intros A B x.
  unfold product.
  split; intros H.
  - apply Specify_classification in H as [H [a [b [H0 [H1 H2]]]]].
    now exists a, b.
  - destruct H as [a [b [H0 [H1 H2]]]].
    subst.
    apply Specify_classification.
    split; eauto.
    apply Powerset_classification.
    intros y H3.
    apply Powerset_classification.
    intros z H4.
    apply Pairwise_union_classification.
    apply Pairing_classification in H3 as [H3 | H3]; subst;
      apply Pairing_classification in H4 as [H4 | H4]; subst; tauto.
Qed.

Definition proj1 : set → set → set → set.
Proof.
  intros A B x.
  destruct (excluded_middle_informative (x ∈ A × B)).
  - rewrite Product_classification in i.
    destruct (constructive_indefinite_description _ i) as [a].
    destruct (constructive_indefinite_description _ e) as [b].
    exact a.
  - exact ∅.
Defined.

Definition proj2 : set → set → set → set.
Proof.
  intros A B x.
  destruct (excluded_middle_informative (x ∈ A × B)).
  - rewrite Product_classification in i.
    destruct (constructive_indefinite_description _ i) as [a].
    destruct (constructive_indefinite_description _ e) as [b].
    exact b.
  - exact ∅.
Defined.

Theorem proj1_eval : ∀ A B a b, a ∈ A → b ∈ B → proj1 A B (a,b) = a.
Proof.
  intros A B a b H H0.
  unfold proj1.
  assert ((a,b) ∈ A × B) by (rewrite Product_classification; eauto).
  repeat destruct excluded_middle_informative; intuition.
  repeat destruct constructive_indefinite_description.
  destruct a0 as [H2 [H3 H4]].
  now apply Ordered_pair_iff in H4 as [H4 H5].
Qed.

Theorem proj2_eval : ∀ A B a b, a ∈ A → b ∈ B → proj2 A B (a,b) = b.
Proof.
  intros A B a b H H0.
  unfold proj2.
  assert ((a,b) ∈ A × B) by (rewrite Product_classification; eauto).
  repeat destruct excluded_middle_informative; intuition.
  repeat destruct constructive_indefinite_description.
  destruct a0 as [H2 [H3 H4]].
  now apply Ordered_pair_iff in H4 as [H4 H5].
Qed.

Theorem Product_union_distr_l : ∀ A B X, (A ∪ B) × X = (A × X) ∪ (B × X).
Proof.
  intros A B X.
  apply Extensionality.
  split; intros H; rewrite Pairwise_union_classification in *;
    repeat rewrite Product_classification in *; repeat destruct H;
      try (rewrite Pairwise_union_classification in *;
           destruct H; [ left | right ]; exists x, x0; tauto);
      exists x, x0; rewrite Pairwise_union_classification in *; tauto.
Qed.

Theorem Product_intersection :
  ∀ A B X Y, (A ∩ B) × (X ∩ Y) = (A × X) ∩ (B × Y).
Proof.
  intros A B X Y.
  apply Extensionality.
  split; intros H;
    rewrite Product_classification, Pairwise_intersection_classification in *;
    repeat rewrite Product_classification in *; repeat destruct H;
      repeat destruct H0; intuition; subst; try rewrite Ordered_pair_iff in *;
      exists x, x0; repeat rewrite Pairwise_intersection_classification in *;
      intuition; congruence.
Qed.

Theorem Product_complement : ∀ A B X, (A \ B) × X = (A × X) \ (B × X).
Proof.
  intros A B X.
  apply Extensionality.
  split; intros H;
    repeat rewrite Complement_classification, Product_classification in *.
  - destruct H as [a [b [H [H0 H1]]]].
    rewrite Complement_classification in *.
    destruct H as [H H2].
    split; try now exists a, b.
    contradict H2.
    rewrite Product_classification in *.
    destruct H2 as [x [y [H2 [H3 H4]]]].
    subst.
    rewrite Ordered_pair_iff in *.
    intuition; congruence.
  - destruct H as [[a [b [H [H0 H1]]]] H2].
    exists a, b.
    rewrite Complement_classification in *.
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

Definition quotient X R := {s in P X | ∃ x, x ∈ X ∧ s = {y in X | (x,y) ∈ R}}.

Infix "/" := quotient : set_scope.

Theorem quotient_classification : ∀ X R s,
    s ∈ X/R ↔ s ⊂ X ∧ ∃ x, x ∈ X ∧ (∀ y, y ∈ s ↔ y ∈ X ∧ (x,y) ∈ R).
Proof.
  intros X R s.
  split; intros H; repeat split;
    unfold quotient in *;
    repeat destruct constructive_indefinite_description;
    try apply i in H as [H [y [H0 H1]]];
    rewrite Specify_classification in *.
  - now apply Powerset_classification.
  - destruct H as [H [y [H0 H1]]].
    exists y.
    split; auto.
    split; intros H2; subst; now rewrite Specify_classification in *.
  - destruct H as [H [y [H0 H1]]].
    rewrite Powerset_classification in *.
    split; auto.
    exists y.
    split; auto.
    apply Extensionality.
    split; intros H2; rewrite Specify_classification in *; firstorder.
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
      split; try rewrite quotient_classification in *; try split;
        [ intros y H3 | exists z; intuition | ];
        rewrite Specify_classification in *; intuition.
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

Theorem unique_set_element :
  ∀ X (x : elts X), exists ! y, y ∈ X ∧ proj1_sig x = y.
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

Theorem set_proj_injective :
  ∀ X (n m : elts X), proj1_sig n = proj1_sig m → n = m.
Proof.
  intros S n m H.
  destruct n, m; simpl in *.
  subst.
  now replace i with i0 by apply proof_irrelevance.
Qed.

Theorem function_record_injective : ∀ f g,
    domain f = domain g → range f = range g → graph f = graph g →
    f = g.
Proof.
  intros f g H H0 H1.
  destruct f, g.
  simpl in *.
  subst.
  now replace func_hyp0 with func_hyp1 by apply proof_irrelevance.
Qed.

Definition eval_rel : set → set → set → set → set.
Proof.
  intros f A B x.
  destruct (excluded_middle_informative (x ∈ A)).
  - destruct (excluded_middle_informative (is_function f A B)).
    + destruct i0.
      destruct (constructive_indefinite_description _ (H0 x i)) as [y].
      exact y.
    + exact B.
  - exact B.
Defined.

Definition eval f x := eval_rel (graph f) (domain f) (range f) x.

Coercion eval : function >-> Funclass.

Theorem Function_classification : ∀ f A B a,
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
  { split; intros x H1; try now rewrite Specify_classification in *.
    exists (p x).
    repeat split; try congruence; try intros x' [H4 H5]; auto;
      rewrite Specify_classification, proj1_eval, proj2_eval in *;
      intuition. }
  exists (mkFunc A B {z in A × B | proj2 A B z = p (proj1 A B z)} H1).
  repeat split; auto.
  intros a H2.
  pose proof Function_classification _ _ _ _ H2 H1 as [[H3 H4] H5].
  destruct (H5 (p a)); split; simpl; intuition.
  rewrite Specify_classification, proj1_eval, proj2_eval; auto.
Qed.

Theorem functionify_construction : ∀ A B (p : elts A → elts B),
  ∃ f, domain f = A ∧ range f = B ∧
       ∀ a : elts A, f (proj1_sig a) = proj1_sig (p a).
Proof.
  intros A B p.
  assert (∀ a : elts A, (proj1_sig a, proj1_sig (p a)) ∈ A × B) as H.
  { intros.
    rewrite Product_classification.
    exists (proj1_sig a), (proj1_sig (p a)).
    repeat split; apply proj2_sig. }
  assert (is_function {z in A × B | ∃ a : elts A,
                         z = (proj1_sig a, proj1_sig (p a))} A B) as H0.
  { split; intros a H0; try now rewrite Specify_classification in *.
    exists (proj1_sig (p (exist _ _ H0))).
    repeat split; intros; try apply proj2_sig.
    - rewrite Specify_classification in *.
      split.
      + apply Product_classification.
        exists a, (proj1_sig (p (exist _ _ H0))).
        repeat split; auto; try apply proj2_sig.
      + exists (exist _ _ H0 : elts A).
        now simpl.
    - destruct H1 as [H1 H2].
      apply Specify_classification in H2 as [H2 [[a' H3] H4]].
      simpl in *.
      apply Ordered_pair_iff in H4 as [H4 H5].
      subst.
      repeat apply f_equal.
      apply proof_irrelevance. }
  exists (mkFunc A B {z in A × B | ∃ a : elts A,
                        z = (proj1_sig a, proj1_sig (p a))} H0).
  repeat split; auto.
  intros a.
  pose proof Function_classification _ _ _ _ (proj2_sig a) H0 as [[H1 H2] H3].
  destruct (H3 (proj1_sig (p a))); split; simpl; intuition; try apply proj2_sig.
  rewrite Specify_classification.
  split; try now (exists a).
  rewrite Product_classification.
  exists (proj1_sig a), (proj1_sig (p a)); repeat split; try apply proj2_sig.
Qed.

Section Function_evaluation.

  Variable f : function.
  Variable A B : set.

  Definition lambdaify : elts (domain f) → elts (range f).
  Proof.
    intros [x H].
    assert (f x ∈ range f)
      by auto using function_maps_domain_to_range.
    exact (exist _ _ H0).
  Defined.

  Definition functionify : (elts A → elts B) → function.
  Proof.
    intros p.
    destruct (constructive_indefinite_description
                _ (functionify_construction _ _ p)) as [g].
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

End Function_evaluation.

Notation "f [ x ] " :=
  ((lambdaify f) x) (at level 60, format "f [ x ]") : set_scope.

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
      rewrite Ordered_pair_iff in H4.
      intuition; congruence.
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

Definition injective f := ∀ x1 x2, f[x1] = f[x2] → x1 = x2.

Definition surjective f := ∀ y, ∃ x, f[x] = y.

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
      destruct (constructive_indefinite_description _ H0) as [y].
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
    destruct (function_construction X (⋃ X) choice_function) as [f [H0 [H1 H2]]].
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
  - rewrite Nonempty_classification in *.
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
    rewrite function_empty_domain in H.
    apply Nonempty_classification in H.
    destruct (constructive_indefinite_description _ H) as [x Hx].
    destruct (excluded_middle_informative (∃ a, a ∈ A ∧ f a = b)) as [e | n].
    - destruct (constructive_indefinite_description _ e) as [a e0].
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
        assert ((exist _ _ H6) = (exist _ _ H2)) by
            now apply H0, set_proj_injective.
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
      destruct (H0 (exist _ _ H2)) as [[x H6] H7].
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
      exists (exist _ _ H4 : elts A).
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
      destruct (H0 (exist _ _ H1)) as [[x H2] H3].
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
    replace x with (proj1_sig (exist (λ x, x ∈ domain f) _ H0)) by auto.
    replace y with (proj1_sig (exist (λ x, x ∈ domain f) _ H1)) by auto.
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
    destruct (H (exist (λ x, x ∈ range f) _ H0)) as [[x X] H1].
    exists x.
    now inversion H1.
  - intros [y Y].
    pose proof (H _ Y) as [x [H0 H1]].
    exists (exist (λ x, x ∈ domain f) _ H0).
    simpl.
    now apply set_proj_injective.
Qed.

Definition image (f : function) := {y in range f | ∃ x, x ∈ domain f ∧ f x = y}.

Theorem image_subset_range : ∀ f, image f ⊂ range f.
Proof.
  intros f x H.
  now apply Specify_classification in H as [H H0].
Qed.

Definition empty_function : function.
Proof.
  assert (∀ a : set, a ∈ ∅ → (λ x : set, x) a ∈ ∅) as H by auto.
  apply function_construction in H.
  destruct (constructive_indefinite_description _ H) as [f i].
  exact f.
Defined.

Definition inverse : function → function.
Proof.
  intros f.
  destruct (excluded_middle_informative (bijective f)).
  - destruct b as [H H0].
    apply right_inverse_iff_surjective in H0.
    destruct (constructive_indefinite_description _ H0) as [g [H1 [H2 H3]]].
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
  rewrite Injective_classification in i.
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
  - rewrite H2, left_inverse; auto.
Qed.

Theorem inverse_bijective : ∀ f, bijective f → bijective (inverse f).
Proof.
  intros f H.
  pose proof H as [H0 H1].
  split.
  - rewrite Injective_classification in *.
    intros x y H2 H3 H4.
    rewrite <-(right_inverse f); auto.
    symmetry.
    rewrite <-(right_inverse f), H4; auto.
  - rewrite Surjective_classification in *.
    intros y H2.
    exists (f y).
    rewrite inverse_domain, left_inverse; repeat split; auto;
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
    destruct (constructive_indefinite_description _ H) as [h i].
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
  rewrite Injective_classification in H1, H0.
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
  rewrite Surjective_classification in H0, H1.
  destruct (H0 y) as [z [H5 H6]]; try now rewrite <-H3.
  rewrite H in H5.
  destruct (H1 z) as [x [H7 H8]]; auto.
  rewrite <-H2 in H7.
  exists (exist (λ x, x ∈ domain (f ∘ g)) _ H7).
  simpl.
  apply set_proj_injective.
  simpl.
  rewrite H4; congruence.
Qed.

Lemma func_ext_lemma : ∀ f g,
    domain f = domain g → range f = range g → (∀ x, x ∈ domain f → f x = g x)
    → graph f ⊂ graph g.
Proof.
  intros f g H H0 H1 z H2.
  pose proof func_hyp f as H3.
  pose proof func_hyp g as H4.
  pose proof func_hyp f as [H5 H6].
  apply H5 in H2 as H7.
  apply Product_classification in H7 as [a [b [H7 [H8 H9]]]].
  pose proof (H1 a) as H10.
  unfold eval in H10.
  destruct H, H0.
  subst.
  pose proof Function_classification _ _ _ _ H7 H3 as [[H H0] H9].
  pose proof H9 _ (conj H8 H2) as H11.
  subst.
  pose proof Function_classification _ _ _ _ H7 H4 as [[H11 H12] H13].
  now rewrite H10.
Qed.

Theorem func_ext : ∀ f g, domain f = domain g → range f = range g
                          → (∀ x, x ∈ domain f → f x = g x) → f = g.
Proof.
  intros f g H H0 H1.
  assert (graph f = graph g).
  { apply Subset_equality_iff.
    pose proof H1 as H2.
    rewrite H in H2.
    split; apply func_ext_lemma; auto using eq_sym. }
  destruct f, g.
  simpl in *.
  subst.
  assert (func_hyp0 = func_hyp1) by apply proof_irrelevance.
  now subst.
Qed.

Theorem function_inv_inv : ∀ f, bijective f → inverse (inverse f) = f.
Proof.
  intros f H.
  apply func_ext.
  - rewrite inverse_domain, inverse_range; auto using inverse_bijective.
  - rewrite inverse_range, inverse_domain; auto using inverse_bijective.
  - intros x H0.
    rewrite inverse_domain, inverse_range in H0; auto using inverse_bijective.
    assert (bijective (inverse f)) as H1 by auto using inverse_bijective.
    pose proof H1 as [H2 H3].
    rewrite Injective_classification in H2.
    apply H2.
      * rewrite <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite inverse_domain, inverse_range; auto.
      * rewrite inverse_domain; auto.
        now apply function_maps_domain_to_range.
      * rewrite left_inverse, right_inverse; auto.
        rewrite inverse_domain, inverse_range; auto.
Qed.

Section Quotient_maps.

  Variable X R : set.

  Definition quotient_map : elts X → elts (X/R).
  Proof.
    intros [x H].
    assert ({z in X | (x,z) ∈ R} ∈ X/R).
    { apply quotient_classification.
      split.
      - intros y H0.
        now rewrite Specify_classification in *.
      - exists x.
        repeat split; auto; rewrite Specify_classification in *; intuition. }
    exact (exist _ _ H0).
  Defined.

End Quotient_maps.

Theorem quotient_lift : ∀ (X R : set) (y : elts (X/R)),
  ∃ x : elts X, quotient_map X R x = y.
Proof.
  intros X R y.
  unfold quotient in *.
  destruct y as [y H].
  pose proof H as H0.
  apply quotient_classification in H0 as [H0 [x [H1 H2]]].
  exists (exist (λ x, x ∈ X) _ H1).
  apply set_proj_injective.
  simpl in *.
  apply Specify_classification in H as [H3 H4].
  apply Extensionality; split; intros H5.
  - now apply Specify_classification, H2 in H5.
  - now apply Specify_classification, H2.
Qed.

Theorem quotient_equiv : ∀ X R x y,
    is_equivalence X R →
    quotient_map X R x = quotient_map X R y ↔ (proj1_sig x, proj1_sig y) ∈ R.
Proof.
  intros X R [x A] [y B] [H [H0 H1]].
  split; intros H2.
  - assert ({z in X | (x, z) ∈ R} = {z in X | (y, z) ∈ R}) as H3 by
          now inversion H2.
    simpl.
    apply Subset_equality_iff in H3 as [H4 H5].
    pose proof (H5 y) as H6.
    rewrite ? Specify_classification in H6.
    apply H6.
    auto.
  - apply set_proj_injective.
    simpl in *.
    apply Extensionality.
    split; intros H3; rewrite Specify_classification in *; split; try tauto.
    + apply (H1 y x z); intuition.
    + apply (H1 x y z); intuition.
Qed.

Theorem quotient_image : ∀ X R x,
    proj1_sig (quotient_map X R x) = {z in X | ((proj1_sig x),z) ∈ R}.
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
    apply Pairing_classification in H1 as [H1 | H1].
    + exists y.
      subst.
      split; auto.
      apply Pairing_classification; auto.
    + exists x.
      subst.
      split; auto.
      apply Pairing_classification; auto.
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
  split; intros H; rewrite Pairwise_intersection_classification in *.
  - rewrite Complement_classification in *.
    tauto.
  - contradiction (Empty_set_classification z).
Qed.

Theorem complement_union_intersection : ∀ E F, (F \ E) ∪ (E ∩ F) = F.
Proof.
  intros E F.
  apply Extensionality.
  split; intros H;
    rewrite Pairwise_union_classification, Complement_classification,
    Pairwise_intersection_classification in *.
  - tauto.
  - destruct (classic (z ∈ E)); tauto.
Qed.

Theorem complement_disjoint_intersection : ∀ E F, (F \ E) ∩ (E ∩ F) = ∅.
Proof.
  intros E F.
  apply Extensionality.
  split; intros H.
  - rewrite ? Pairwise_intersection_classification,
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
  rewrite Pairwise_intersection_classification in H.
  tauto.
Qed.

Theorem Intersection_right : ∀ E F, E ∩ F ⊂ F.
Proof.
  intros E F x H.
  rewrite Pairwise_intersection_classification in H.
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
    + rewrite Singleton_classification in H.
      subst.
      apply Specify_classification.
      repeat split.
      * apply Empty_set_in_powerset.
      * apply Empty_set_is_subset.
      * intros a H.
        contradiction (Empty_set_classification a).
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
    pose proof
         Function_classification (graph f) (domain f) (range f) _ H2 (func_hyp f)
      as [[H5 H6] H7].
    apply H1 in H2 as [z [[H4 H8] H9]].
    assert (z = b) by now apply H9.
    assert (z = (f a)) by now apply H9.
    congruence.
  - destruct H as [a [H H0]].
    subst.
    pose proof
         Function_classification (graph f) (domain f) (range f) _ H (func_hyp f)
      as [[H0 H1] H2].
    exact H1.
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
  assert (y = a) by now apply H9.
  assert (y = a') by now apply H9.
  congruence.
Qed.

Definition inverse_image_of_element f y := {x in domain f | f x = y}.

Theorem Inverse_image_classification : ∀ f a b,
    a ∈ domain f → b ∈ range f → a ∈ inverse_image_of_element f b ↔ f a = b.
Proof.
  intros f a b H H0.
  split; intros H1; unfold inverse_image_of_element in *;
    rewrite Specify_classification in *; tauto.
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
  set (f1 := mkFunc A B g1 H).
  set (f2 := mkFunc A B g2 H0).
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
    rewrite Singleton_classification in *.
    intuition; congruence.
  - apply Product_classification.
    exists x, y.
    now rewrite ? Singleton_classification in *.
Qed.

Theorem singleton_functions :
  ∀ f x y, domain f = {x,x} → range f = {y,y} → graph f = {(x,y),(x,y)}.
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
      * rewrite ? Singleton_classification in *.
        now subst.
      * intros x' H4.
        rewrite ? Singleton_classification, Ordered_pair_iff in *.
        intuition; congruence.
  - pose proof func_hyp f as [H1].
    now rewrite H, H0, singleton_products in *.
Qed.
