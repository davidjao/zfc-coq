Require Export peano_axioms.
Set Warnings "-notation-overridden".

Definition integer_relation :=
  {z in (ω × ω) × (ω × ω) | ∃ a b c d : N,
     z = ((value ω a, value ω b), (value ω c, value ω d)) ∧
     a + d = b + c}.

Theorem integer_equivalence : is_equivalence (ω × ω) integer_relation.
Proof.
  repeat split; unfold integer_relation in *.
  - intros a H.
    apply Specify_classification.
    split.
    + apply Product_classification; eauto.
    + apply Product_classification in H as [x [y [H [H0 H1]]]].
      exists (mkSet ω x H), (mkSet ω y H0), (mkSet ω x H), (mkSet ω y H0).
      split; simpl; try congruence; ring.
  - intros x y H H0 H1.
    rewrite Specify_classification in *.
    destruct H1 as [H1 [a [b [c [d [H2 H3]]]]]].
    split.
    + apply Product_classification; eauto.
    + exists c, d, a, b.
      split; try now ring_simplify [H3].
      now rewrite Ordered_pair_iff in *.
  - intros x y z H H0 H1 H2 H3.
    rewrite Specify_classification in *.
    destruct H2 as [H2 [a [b [c [d [H4 H5]]]]]],
                   H3 as [H3 [e [f [g [h [H6 H7]]]]]].
    split.
    + apply Product_classification; eauto.
    + exists a, b, g, h.
      split; rewrite Ordered_pair_iff in *; intuition.
      subst.
      rewrite Ordered_pair_iff in *; intuition.
      apply set_proj_injective in H6.
      apply set_proj_injective in H8.
      subst.
      apply (cancellation_add e).
      ring_simplify [H5 H7].
      rewrite H7, add_comm, add_assoc, H5.
      ring.
Qed.

Definition Z := elts ((ω × ω) / integer_relation).

Delimit Scope Z_scope with Z.
Open Scope Z_scope.
Bind Scope Z_scope with Z.

Definition embed : N → N → Z.
Proof.
  intros [_ a A] [_ b B].
  assert ((a, b) ∈ ω × ω).
  { apply Product_classification.
    exists a, b.
    auto. }
  exact (quotient_map (ω × ω) integer_relation (mkSet (ω × ω) (a,b) H)).
Defined.

Infix "-" := embed : N_scope.

Theorem embed_surj : ∀ z, ∃ a b, a - b = z.
Proof.
  intros z.
  destruct (quotient_lift _ _ z) as [y H].
  destruct (unique_set_element _ y) as [x [[H0 H1] H2]].
  apply Product_classification in H0 as [a [b [H3 [H4 H5]]]].
  exists (mkSet _ _ H3), (mkSet _ _ H4).
  apply set_proj_injective.
  simpl in *.
  rewrite <-H, <-H5, <-H1.
  auto using quotient_image. (* alternative direct proof: now destruct y. *)
Qed.

Theorem Zequiv : ∀ a b c d, a - b = c - d ↔ a+d = b+c.
Proof.
  intros [_ a A] [_ b B] [_ c C] [_ d D].
  split; intros H; unfold embed in *.
  - apply quotient_wf in H; auto using integer_equivalence.
    simpl in *.
    apply Specify_classification in H as [H [a0 [b0 [c0 [d0 [H0 H1]]]]]].
    rewrite ? Ordered_pair_iff in *; intuition; subst.
    replace {| in_set := A |} with a0; replace {| in_set := B |} with b0;
    replace {| in_set := C |} with c0; replace {| in_set := D |} with d0;
    auto; now apply set_proj_injective.
  - apply quotient_wf; auto using integer_equivalence.
    simpl.
    apply Specify_classification; split.
    + apply Product_classification.
      exists (a,b), (c,d).
      repeat split; auto; apply Product_classification; eauto.
    + now exists {| in_set := A |}, {| in_set := B |},
    {| in_set := C |}, {| in_set := D |}.
Qed.

Definition INZ a := a - 0.

Coercion INZ : N >-> Z.

Definition add : Z → Z → Z.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (embed_surj x)) as [a H].
  destruct (constructive_indefinite_description _ H) as [b H0].
  destruct (constructive_indefinite_description _ (embed_surj y)) as [c H1].
  destruct (constructive_indefinite_description _ H1) as [d H2].
  exact ((a+c) - (b+d)).
Defined.

Definition mul : Z → Z → Z.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (embed_surj x)) as [m H].
  destruct (constructive_indefinite_description _ H) as [n H0].
  destruct (constructive_indefinite_description _ (embed_surj y)) as [p H1].
  destruct (constructive_indefinite_description _ H1) as [q H2].
  exact ((m*p+n*q) - (n*p+m*q)).
Defined.

Definition neg : Z → Z.
Proof.
  intros x.
  destruct (constructive_indefinite_description _ (embed_surj x)) as [a H].
  destruct (constructive_indefinite_description _ H) as [b H0].
  exact (b - a).
Defined.

Definition zero := 0 - 0.
Definition one := 1 - 0.

Notation "0" := zero : Z_scope.
Notation "1" := one : Z_scope.
Infix "+" := add : Z_scope.
Infix "*" := mul : Z_scope.
Notation "- a" := (neg a) : Z_scope.

Theorem INZ_add : ∀ a b : N, a+b = (a+b)%N.
Proof.
  intros a b.
  unfold add, INZ.
  repeat destruct constructive_indefinite_description.
  rewrite Zequiv in *.
  ring [e0 e2].
Qed.

Theorem INZ_mul : ∀ a b : N, a*b = (a*b)%N.
Proof.
  intros a b.
  unfold mul, INZ.
  repeat destruct constructive_indefinite_description.
  rewrite Zequiv in *.
  ring [e0 e2].
Qed.

Theorem INZ_inj : ∀ a b : N, INZ a = INZ b ↔ a = b.
Proof.
  intros a b.
  split; intros H; try now subst.
  apply Zequiv in H.
  ring [H].
Qed.

Theorem add_Z_wf : ∀ a b c d, (a - b) + (c - d) = (a+c) - (b+d).
Proof.
  intros a b c d.
  unfold add.
  repeat destruct constructive_indefinite_description.
  rewrite Zequiv in *.
  ring_simplify [e0 e2].
  rewrite e2, <-add_assoc, e0.
  ring.
Qed.

Theorem A1 : ∀ a b, a + b = b + a.
Proof.
  intros a b.
  unfold add.
  repeat destruct constructive_indefinite_description.
  rewrite Zequiv.
  ring.
Qed.

Theorem A2 : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  intros a b c.
  unfold add.
  repeat destruct constructive_indefinite_description.
  rewrite Zequiv in *.
  apply (cancellation_add x2).
  ring_simplify [e6]; ring_simplify in e6; rewrite <-e6;
    ring_simplify [e8]; ring_simplify in e8; rewrite e8; ring.
Qed.

Theorem A3 : ∀ a, 0 + a = a.
Proof.
  intros a.
  unfold add.
  repeat destruct constructive_indefinite_description.
  unfold zero, INZ in *.
  subst.
  rewrite Zequiv in *.
  ring [e0].
Qed.

Theorem neg_Z_wf : ∀ a b, - (a - b) = b - a.
Proof.
  intros a b.
  unfold neg.
  repeat destruct constructive_indefinite_description.
  now rewrite Zequiv in *.
Qed.

Theorem A4 : ∀ a, a + -a = 0.
Proof.
  intros a.
  unfold add, neg.
  repeat destruct constructive_indefinite_description.
  unfold zero, INZ.
  rewrite Zequiv in *.
  now ring_simplify [e2].
Qed.

Theorem M1 : ∀ a b, a * b = b * a.
Proof.
  intros a b.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  rewrite Zequiv.
  ring.
Qed.

Theorem mul_Z_wf : ∀ a b c d,
    (a - b) * (c - d) = (a*c+b*d) - (b*c+a*d).
Proof.
  intros a b c d.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  rewrite Zequiv in *.
  apply (cancellation_add (b*x1)).
  rewrite ? add_assoc, <-mul_distr_r, (add_comm _ (b*d)), ? add_assoc,
  <-mul_distr_l, (add_comm b), (add_comm d), e0, e2, (add_comm x0),
  <-? add_assoc, (add_comm (x*x2)), ? add_assoc, (add_comm _ (a*d)),
  (add_comm _ (x*x2)), mul_distr_l, mul_distr_r, ? add_assoc, <-mul_distr_l,
  <-mul_distr_r, (add_comm d), e0, e2.
  ring.
Qed.

Theorem M2 : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  intros a b c.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  rewrite <-? mul_Z_wf, e6, e8, ? mul_Z_wf, Zequiv.
  ring.
Qed.

Theorem M3 : ∀ a, 1 * a = a.
Proof.
  intros [_ a H].
  unfold mul in *.
  repeat destruct constructive_indefinite_description.
  unfold one, INZ in *.
  destruct e2.
  rewrite Zequiv in *.
  ring [e0].
Qed.

Theorem D1 : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  intros a b c.
  unfold mul, add.
  repeat destruct constructive_indefinite_description.
  rewrite <-mul_Z_wf, <-add_Z_wf, e4, e8, e10, add_Z_wf, mul_Z_wf, Zequiv.
  ring.
Qed.

Definition sub a b := (a + -b).
Infix "-" := sub : Z_scope.

Theorem A3_r : ∀ a, a + 0 = a.
Proof.
  intros a.
  now rewrite A1, A3.
Qed.

Theorem M3_r : ∀ a, a * 1 = a.
Proof.
  intros a.
  now rewrite M1, M3.
Qed.

Theorem D1_l : ∀ a b c, a * (b + c) = a * b + a * c.
Proof.
  intros a b c.
  now rewrite ? (M1 a), D1.
Qed.

Theorem sub_neg : (∀ x y : Z, x - y = x + - y).
Proof.
  auto.
Qed.

Add Ring integer_ring :
  (mk_rt 0 1 add mul sub neg eq A3 A1 A2 M3 M1 M2 D1 sub_neg A4).

Definition lt : Z → Z → Prop.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (embed_surj x)) as [a H].
  destruct (constructive_indefinite_description _ H) as [b H0].
  destruct (constructive_indefinite_description _ (embed_surj y)) as [c H1].
  destruct (constructive_indefinite_description _ H1) as [d H2].
  exact (a+d < b+c).
Defined.

Infix "<" := lt : Z_scope.
Notation "a > b" := (b < a) (only parsing) : Z_scope.
Notation "x < y < z" := (x < y ∧ y < z) : Z_scope.

Definition le a b := a < b ∨ a = b.
Infix "≤" := le : Z_scope.
Notation "a ≥ b" := (b ≤ a) (only parsing) : Z_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level): Z_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level): Z_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level): Z_scope.

Theorem T : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ (a > b)) ∨
                   (¬ (a < b) ∧ a = b ∧ ¬ (a > b)) ∨
                   (¬ (a < b) ∧ a ≠ b ∧ a > b).
Proof.
  intros a b.
  unfold lt.
  repeat destruct constructive_indefinite_description.
  subst.
  unfold not.
  rewrite Zequiv, ? (add_comm x1), ? (add_comm x2).
  eauto using trichotomy.
Qed.

Theorem lt_def : ∀ a b, a < b ↔ ∃ c : N, 0 ≠ c ∧ b = a + c.
Proof.
  intros a b.
  split; intros H; unfold lt, zero, INZ in *;
    repeat destruct constructive_indefinite_description; rewrite lt_def in *;
      destruct H as [z [H H0]]; exists z; split; subst;
        try rewrite add_Z_wf, Zequiv in *.
  - contradict H.
    rewrite Zequiv in *.
    now ring_simplify in H.
  - now ring_simplify [H0].
  - contradict H.
    now subst.
  - now ring_simplify in e2; ring_simplify [e2].
Qed.

Theorem lt_trans : ∀ a b c, a < b → b < c → a < c.
Proof.
  intros a b c H H0.
  rewrite lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  exists (x+y)%N.
  split.
  - intros H3.
    apply INZ_inj, eq_sym, cancellation_0_add in H3 as [H3 H4]; subst; auto.
  - subst.
    rewrite <-INZ_add.
    ring.
Qed.

Theorem O1 : ∀ a b c, b < c → a + b < a + c.
Proof.
  intros a b c H.
  rewrite lt_def in *.
  destruct H as [x [H H0]].
  exists x.
  split; auto.
  ring [H0].
Qed.

Theorem O2 : ∀ a b, 0 < a → 0 < b → 0 < a * b.
Proof.
  intros a b H H0.
  rewrite lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  exists (x*y)%N.
  split.
  - intros H3.
    unfold lt in *.
    repeat destruct constructive_indefinite_description.
    subst.
    apply INZ_inj, eq_sym, cancellation_0_mul in H3 as [H3 | H3]; subst; auto.
  - subst.
    ring_simplify.
    auto using INZ_mul.
Qed.

Theorem O3 : ∀ a b c, 0 < a → b < c → a * b < a * c.
Proof.
  intros a b c H H0.
  rewrite lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  ring_simplify in H2.
  subst.
  exists (x*y)%N.
  split.
  - intros H1.
    apply INZ_inj, eq_sym, cancellation_0_mul in H1 as [H1 | H1]; subst; auto.
  - ring_simplify.
    now rewrite INZ_mul.
Qed.

Theorem INZ_lt : ∀ a b : N, INZ a < INZ b ↔ (a < b)%N.
Proof.
  intros a b.
  split; intros H; rewrite lt_def, peano_axioms.lt_def in *;
    destruct H as [c [H H0]]; exists c; split.
  - contradict H.
    now subst.
  - now rewrite INZ_add, INZ_inj in H0.
  - contradict H.
    now apply INZ_inj in H.
  - subst.
    auto using INZ_add.
Qed.

Theorem lt_0_1 : ∀ a, 0 < a → ¬ a < 1.
Proof.
  intros a H H0.
  rewrite lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  contradiction (peano_axioms.lt_0_1 x).
  split; rewrite peano_axioms.lt_def.
  - exists x.
    split; try ring; subst.
    contradict H.
    now subst.
  - exists y.
    split.
    + contradict H0.
      now subst.
    + subst.
      ring_simplify in H2.
      now rewrite <-INZ_inj, <-INZ_add.
Qed.

Theorem lt_n_Sn : ∀ x n, x < S n → x < n ∨ x = n.
Proof.
  intros x n H.
  destruct (T x n); intuition; try tauto.
  rewrite lt_def in *.
  destruct H as [a [H H2]], H3 as [b [H3 H4]].
  subst.
  rewrite ? INZ_add, INZ_inj, <-add_1_r, <-add_assoc in H2.
  apply cancellation_add, eq_sym, cancellation_1_add in H2 as [H2 | H2];
    subst; [ contradiction H3 | contradiction H ]; auto.
Qed.

Theorem zero_lt_1 : 0 < 1.
Proof.
  rewrite lt_def.
  exists 1%N.
  split.
  - intros H.
    replace 0 with (INZ 0) in *; auto.
    now apply INZ_inj, PA4 in H.
  - now ring_simplify.
Qed.

Theorem strong_induction : ∀ P : Z → Prop,
    (∀ x : Z, (∀ y : Z, 0 < y < x → P y) → P x) → ∀ a : Z, P a.
Proof.
  intros P H x.
  destruct (T x 0) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]];
    try now (apply H; intros y [H3 H4]; contradict H2; eauto using lt_trans).
  apply lt_def in H2 as [c [H2 H3]].
  subst.
  rewrite A3 in *.
  apply (Induction (λ x : N, P x ∧ ∀ y : N, 0 < y ∧ y < x → P y))%N.
  - split; [ apply H | ]; intros y [H3 H4]; contradiction (lt_irrefl 0);
      [ eapply INZ_lt, lt_trans | eapply peano_axioms.lt_trans ]; eauto.
  - intros n [H3 H4].
    split.
    + apply H.
      intros y [H5 H6].
      apply lt_n_Sn in H6 as [H6 | H6]; try congruence.
      apply H.
      intros z [H8 H9].
      pose proof H8 as H10.
      apply lt_def in H10 as [d [H10 H11]].
      rewrite H11, A3 in *.
      apply H4.
      split; apply INZ_lt; eauto using lt_trans.
    + intros y [H5 H6].
      apply INZ_lt, lt_n_Sn in H6 as [H6 | H6]; try congruence.
      rewrite INZ_lt in H6.
      auto.
Qed.
