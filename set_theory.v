Require Export logic_axioms.

Parameter set : Type.
Parameter IN: set → set → Prop.
Delimit Scope set_scope with set.
Open Scope set_scope.
Bind Scope set_scope with set.

Infix "∈" := IN (at level 75) : set_scope.
Notation "a ∉ b" := (¬ a ∈ b) (at level 75) : set_scope.

Axiom Nontriviality : ∃ w : set, True.
Axiom Extensionality : ∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y.
Axiom Regularity :
  ∀ x, ((∃ a, a ∈ x) → ∃ y, (y ∈ x ∧ ¬ ∃ z, (z ∈ y ∧ z ∈ x))).
Axiom Specification : ∀ z p, ∃ y, ∀ x, (x ∈ y ↔ (x ∈ z ∧ (p x))).
Axiom Replacement : ∀ A R,
      (∀ x, x ∈ A → exists ! y, (R x y)) →
      ∃ B, ∀ x, (x ∈ A → ∃ y, (y ∈ B ∧ (R x y))).

Definition specify : set → (set → Prop) → set.
Proof.
  intros A p.
  destruct (constructive_indefinite_description _ (Specification A p)) as [S].
  exact S.
Defined.

Notation "{ x 'in' A | P }" := (specify A (λ x, P)) : set_scope.

Theorem Specify_classification : ∀ A P x, x ∈ (specify A P) ↔ x ∈ A ∧ P x.
Proof.
  intros A P x.
  unfold specify in *.
  repeat destruct constructive_indefinite_description.
  split; intros H; now apply i.
Qed.

Definition empty_set : set.
Proof.
  destruct (constructive_indefinite_description _ Nontriviality) as [w].
  exact {x in w | False}.
Defined.

Notation "∅" := empty_set : set_scope.

Theorem Empty_set_classification : ∀ w, w ∉ ∅.
Proof.
  unfold empty_set, specify.
  repeat destruct constructive_indefinite_description.
  firstorder.
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

Axiom Pairing : ∀ x y, ∃ z, ((x ∈ z) ∧ (y ∈ z)).

Definition pair : set → set → set.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (Pairing x y)) as [z].
  exact {t in z | t = x ∨ t = y}.
Defined.

Notation " { x , y } " := (pair x y) : set_scope.
Notation " { x } " := (pair x x) : set_scope.

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

Axiom Union : ∀ F, ∃ A, ∀ x y, (x ∈ y ∧ y ∈ F) → x ∈ A.

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

Axiom Infinity : ∃ X, (∅ ∈ X ∧ Inductive X).

Definition subset a b := ∀ x, x ∈ a → x ∈ b.

Infix "⊂" := subset (at level 70) : set_scope.

Axiom Powerset : ∀ x, ∃ y, ∀ z, z ⊂ x → z ∈ y.

Definition P : set → set.
Proof.
  intros x.
  destruct (constructive_indefinite_description _ (Powerset x)) as [y].
  exact {s in y | s ⊂ x}.
Defined.

Theorem Subset_transitive : ∀ X Y Z, X ⊂ Y → Y ⊂ Z → X ⊂ Z.
Proof.
  intros X Y Z H H0 x H1.
  eauto.
Qed.

Theorem Empty_set_is_subset : ∀ X, ∅ ⊂ X.
Proof.
  intros X z H.
  now apply Empty_set_classification in H.
Qed.

Theorem Set_is_subset : ∀ X, X ⊂ X.
Proof.
  firstorder.
Qed.

Theorem Subset_equality : ∀ A B, A ⊂ B → B ⊂ A → A = B.
Proof.
  intros A B H H0.
  apply Extensionality; intuition.
Qed.

Theorem Subset_equality_iff : ∀ A B, (A ⊂ B ∧ B ⊂ A) ↔ A = B.
Proof.
  intros A B.
  split; intros H.
  - apply Subset_equality; tauto.
  - rewrite H.
    split; apply Set_is_subset.
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

Theorem Union_classification : ∀ x C, x ∈ ⋃ C ↔ ∃ X, X ∈ C ∧ x ∈ X.
Proof.
  intros x C.
  unfold union, specify in *.
  repeat destruct constructive_indefinite_description.
  split; intros H;
    [ apply i0 in H as [H [y H0]] | destruct H as [y H]; apply i0 ];
    firstorder.
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

Definition intersection : set → set.
Proof.
  intros X.
  exact {y in ⋃ X | ∀ x, x ∈ X → y ∈ x}.
Defined.

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

Definition complement : set → set → set.
Proof.
  intros A B.
  exact {x in A | x ∉ B}.
Defined.

Infix "\" := complement (at level 60) : set_scope.

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

Definition product : set → set → set.
Proof.
  intros A B.
  destruct (constructive_indefinite_description
              _ (Specification (P (P (A ∪ B)))
                               (λ x, ∃ a b, a ∈ A ∧ b ∈ B ∧ x = (a,b))))
    as [x].
  exact x.
Defined.

Infix "×" := product (at level 60) : set_scope.

Theorem Product_classification : ∀ A B x,
    x ∈ A × B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ x = (a,b).
Proof.
  intros A B x.
  unfold product.
  destruct constructive_indefinite_description.
  split; intros H.
  - apply i in H as [H [a [b [H0 [H1 H2]]]]].
    now exists a, b.
  - destruct H as [a [b [H0 [H1 H2]]]].
    subst.
    apply i.
    split; try now exists a, b.
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

(* Coqification of sets *)
Record elts (S : set) : Type := mkSet { ambient_set := S;
                                        value : set;
                                        in_set : value ∈ S }.

Theorem unique_set_element : ∀ X x, exists ! y, y ∈ X ∧ value X x = y.
Proof.
  intros X [_ x H].
  exists x.
  repeat split; auto.
  now intros x' [H0 H1].
Qed.

Record function : Type :=
  mkFunc { domain : set;
           range : set;
           graph : set;
           func_hyp : is_function graph domain range }.

Theorem set_proj_injective : ∀ X n m, (value X n) = (value X m) → n = m.
Proof.
  intros S n m H.
  destruct n, m; simpl in *.
  subst.
  assert (in_set0 = in_set1) by apply proof_irrelevance.
  now subst.
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
       ∀ a : elts A, f (value A a) = (value B (p a)).
Proof.
  intros A B p.
  assert (∀ a : elts A, ((value A a), (value B (p a))) ∈ A × B) as H.
  { intros.
    rewrite Product_classification.
    exists (value A a), (value B (p a)).
    repeat split; auto using in_set. }
  assert (is_function {z in A × B | ∃ a : elts A,
                         z = ((value A a), (value B (p a)))} A B) as H0.
  { split; intros a H0; try now rewrite Specify_classification in *.
    exists (value B (p (mkSet A a H0))).
    repeat split; intros; auto using in_set.
    - rewrite Specify_classification in *.
      split.
      + apply Product_classification.
        exists a, (value B (p {| value := a; in_set := H0 |})).
        auto using in_set.
      + exists (mkSet A a H0).
        now simpl.
    - destruct H1 as [H1 H2].
      apply Specify_classification in H2 as [H2 [[a' H3] H4]].
      simpl in *.
      apply Ordered_pair_iff in H4 as [H4 H5].
      subst.
      repeat apply f_equal.
      apply proof_irrelevance. }
  exists (mkFunc A B {z in A × B | ∃ a : elts A,
                        z = ((value A a), (value B (p a)))} H0).
  repeat split; auto.
  intros a.
  pose proof Function_classification _ _ _ _ (in_set A a) H0 as [[H1 H2] H3].
  destruct (H3 (value B (p a))); split; simpl; intuition; try apply in_set.
  rewrite Specify_classification.
  split; try now (exists a).
  rewrite Product_classification.
  exists (value A a), (value B (p a)); auto using in_set.
Qed.

Section Function_evaluation.

  Variable f : function.
  Variable A B : set.

  Definition lambdaify : elts (domain f) → elts (range f).
  Proof.
    intros [_ x H].
    assert (f x ∈ range f)
      by auto using function_maps_domain_to_range.
    exact (mkSet (range f) (f x) H0).
  Defined.

  Definition functionify : (elts A → elts B) → function.
  Proof.
    intros p.
    destruct (constructive_indefinite_description
                _ (functionify_construction _ _ p)) as [g].
    exact g.
  Defined.

End Function_evaluation.

Notation "f [ x ] " :=
  ((lambdaify f) x) (at level 60, format "f [ x ]") : set_scope.

Definition power X Y := {f in P (X × Y) | is_function f X Y}.

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

Definition injective f := ∀ x1 x2, f[x1] = f[x2] → x1 = x2.

Definition surjective f := ∀ y, ∃ x, f[x] = y.

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
        assert ((mkSet A x1 H6) = (mkSet A x H2)) by
            now apply H0, set_proj_injective.
        congruence.
      + contradiction n.
        now (exists x).
    - destruct H0 as [g [H0 [H1 H2]]].
      intros x1 x2 H3.
      unfold lambdaify in H3.
      destruct x1, x2.
      assert (value0 = value1).
      { rewrite <-H2; rewrite <-H2 at 1; try rewrite <-H1; try congruence.
        apply function_maps_domain_to_range.
        rewrite H0.
        now apply function_maps_domain_to_range. }
      subst.
      now apply set_proj_injective.
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
      destruct (H0 (mkSet B y H2)) as [[_ x H6] H7].
      simpl in *.
      unfold partial_left_inverse in H5.
      repeat destruct excluded_middle_informative;
        repeat destruct constructive_indefinite_description; subst; try tauto.
      contradiction n.
      exists x; split; auto.
      congruence.
    - destruct H0 as [g [H0 [H1 H2]]].
      intros [_ b H3].
      assert (g b ∈ A).
      { rewrite <-H1.
        apply function_maps_domain_to_range.
        congruence. }
      exists (mkSet A (g b) H4).
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
      destruct (H0 (mkSet (range f) y H1)) as [[_ x H2] H3].
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
    intros [_ y H3].
    exfalso.
    contradiction (Empty_set_classification (g y)).
    rewrite <-H, <-H1.
    apply function_maps_domain_to_range.
    congruence.
Qed.

Definition empty_function : function.
Proof.
  assert (∀ a : set, a ∈ ∅ → (λ x : set, x) a ∈ ∅).
  { intros a H.
    contradiction (Empty_set_classification a). }
  apply function_construction in H.
  destruct (constructive_indefinite_description _ H) as [f i].
  exact f.
Defined.

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

Infix "∘" := composition (at level 60) : set_scope.

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

Section Quotient_maps.

  Variable X R : set.

  Definition quotient_map : elts X → elts (X/R).
  Proof.
    intros [_ x H].
    assert ({z in X | (x,z) ∈ R} ∈ X/R).
    { apply quotient_classification.
      split.
      - intros y H0.
        now rewrite Specify_classification in *.
      - exists x.
        repeat split; auto; rewrite Specify_classification in *; intuition. }
    exact (mkSet (X/R) {z in X | (x,z) ∈ R} H0).
  Defined.

End Quotient_maps.

Theorem quotient_lift : ∀ (X R : set) (y : elts (X/R)),
  ∃ x : elts X, quotient_map X R x = y.
Proof.
  intros X R y.
  unfold quotient in *.
  pose proof in_set (X/R) y as H.
  apply quotient_classification in H as [H [x [H0 H1]]].
  exists (mkSet X x H0).
  destruct y as [y Y].
  apply set_proj_injective.
  simpl in *.
  apply Extensionality; split; intros H2.
  - now apply Specify_classification, H1 in H2.
  - now apply Specify_classification, H1.
Qed.

Theorem quotient_wf : ∀ X R x y,
    is_equivalence X R →
    quotient_map X R x = quotient_map X R y ↔ ((value X x), (value X y)) ∈ R.
Proof.
  intros X R [_ x A] [_ y B] [H [H0 H1]].
  split; intros H2.
  - assert ({z in X | (x, z) ∈ R} = {z in X | (y, z) ∈ R}) as H3 by
          (unfold quotient_map in H2; congruence).
    simpl.
    apply Subset_equality_iff in H3 as [H4 H5].
    pose proof (H5 y) as H6.
    rewrite ? Specify_classification in H6.
    apply H6.
    auto.
  - apply set_proj_injective.
    simpl in *.
    apply Extensionality.
    split; intros H3; rewrite Specify_classification in *.
    + split; try tauto.
      apply (H1 y x z); intuition.
    + split; try tauto.
      apply (H1 x y z); intuition.
Qed.

Theorem quotient_image : ∀ X R x,
    value (X / R) (quotient_map X R x) = {z in X | ((value X x),z) ∈ R}.
Proof.
  now intros X R [_ x H].
Qed.

Record relation : Type := mkrel
                           { R1 : set;
                             R2 : set;
                             R : set;
                             rel_cond : R ⊂ R1 × R2 }.

Goal ∀ R : relation, R.(R1) = ∅.
Admitted.

Theorem Product_left_empty : ∀ A, ∅ × A = ∅.
Proof.
  intros A.
  apply Extensionality; split; intros H;
    try apply Product_classification in H as [a [b [H H0]]];
    now apply Empty_set_classification in H.
Qed.

(*Check (mkrel ∅ ∅ ∅ (Empty_set_is_subset _)).(rel_cond).*)
