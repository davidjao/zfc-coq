Set Warnings "-ambiguous-paths".
Require Export ordered_fields Field.

Definition Z0 := {z in Zset × Zset | (proj2 Zset Zset z) ≠ 0}.

Definition rational_relation :=
  {z in Z0 × Z0 | ∃ a b c d : Z, z = ((a, b), (c, d)) ∧ a * d = b * c}.

Theorem rational_equivalence : is_equivalence Z0 rational_relation.
Proof.
  repeat split; unfold rational_relation in *.
  - intros a H.
    apply Specify_classification.
    split; try apply Product_classification; eauto.
    apply Specify_classification in H as [H H0].
    apply Product_classification in H as [x [y [H1 [H2 H3]]]].
    subst; simpl.
    unfold proj2 in H0.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description.
    + destruct a as [H3 [H4 H5]].
      apply Ordered_pair_iff in H5 as [H5 H6].
      subst.
      exists (exist _ _ H1 : Z), (exist _ _ H2 : Z),
      (exist _ _ H3 : Z), (exist _ _ H4 : Z).
      simpl.
      split; auto.
      rewrite integers.M1.
      replace H1 with H3; replace H2 with H4; auto using proof_irrelevance.
    + contradiction n.
      apply Product_classification; eauto.
  - intros x y H H0 H1.
    rewrite Specify_classification in *.
    destruct H1 as [H1 [a [b [c [d [H2 H3]]]]]].
    split; try apply Product_classification; eauto.
    exists c, d, a ,b.
    repeat split; auto; try ring [H3].
    repeat rewrite Ordered_pair_iff in *.
    intuition.
  - intros x y z H H0 H1 H2 H3.
    rewrite Specify_classification in *.
    destruct H2 as [H2 [a [b [c [d [H4 H5]]]]]], H3
        as [H3 [a' [b' [c' [d' [H8 H9]]]]]].
    split; try apply Product_classification; eauto.
    exists a, b, c', d'.
    repeat split; auto; repeat rewrite Ordered_pair_iff in *; intuition;
      subst; rewrite Ordered_pair_iff in *; intuition.
    apply set_proj_injective in H6.
    apply set_proj_injective in H7.
    subst.
    apply (cancellation_mul_l (integral_domain ℤ_order) b'); simpl.
    + apply Specify_classification in H0 as [H0 H4].
      rewrite proj2_eval in H4; unfold IZS; auto using elts_in_set.
      contradict H4.
      now subst.
    + now ring_simplify [H5 H9].
Qed.

Definition Qset := Z0 / rational_relation.

Definition Q := elts Qset.

Definition IQS (a : Q) := elt_to_set _ a : set.
Coercion IQS : Q >-> set.

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.
Open Scope Q_scope.
Bind Scope Q_scope with Q.

Lemma embed_zero : (0,1) ∈ Z0.
Proof.
  apply Specify_classification.
  split.
  - apply Product_classification.
    exists 0, 1.
    unfold IZS; repeat split; auto using elts_in_set.
  - unfold proj2.
    destruct excluded_middle_informative.
    repeat destruct constructive_indefinite_description.
    + destruct a as [H [H0 H1]].
      apply Ordered_pair_iff in H1 as [H1 H2].
      subst.
      intros H1.
      contradiction zero_ne_1.
      now apply set_proj_injective.
    + contradiction n.
      apply Product_classification.
      exists 0, 1.
      unfold IZS; repeat split; auto using elts_in_set.
Qed.

Lemma embed_nonzero : ∀ a b : Z, b ≠ 0 → (a, b) ∈ Z0.
Proof.
  intros a b H.
  apply Specify_classification.
  split.
  + apply Product_classification; eauto using elts_in_set.
  + rewrite proj2_eval; eauto using elts_in_set.
    contradict H.
    now apply set_proj_injective.
Qed.

Definition embed : Z → Z → Q.
Proof.
  intros a b.
  destruct (excluded_middle_informative (b = 0)).
  - pose proof embed_zero as H.
    exact (quotient_map Z0 rational_relation (exist _ _ H)).
  - apply (embed_nonzero a) in n.
    exact (quotient_map Z0 rational_relation (exist _ _ n)).
Defined.

Infix "/" := embed : Q_scope.

Theorem Qlift : ∀ q, ∃ a b, b ≠ 0 ∧ a / b = q.
Proof.
  intros q.
  destruct (quotient_lift _ _ q) as [y H].
  destruct (unique_set_element _ y) as [x [[H0 H1] H2]].
  apply Specify_classification in H0 as [H0 H3].
  apply Product_classification in H0 as [a [b [H0 [H4 H5]]]].
  subst.
  exists (exist _ _ H0 : Z), (exist _ _ H4 : Z).
  set (a' := exist _ _ H0 : Z).
  set (b' := exist _ _ H4 : Z).
  assert (b' ≠ 0) as H5.
  { contradict H3.
    unfold proj2.
    destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description.
    - destruct a0 as [H5 [H6 H7]].
      apply Ordered_pair_iff in H7 as [H7 H8].
      subst.
      now rewrite <-H3.
    - contradict n.
      apply Product_classification; eauto. }
  split; auto.
  apply set_proj_injective.
  unfold Qset.
  rewrite <-quotient_image, <-H1.
  unfold embed; destruct excluded_middle_informative; simpl; intuition.
Qed.

Theorem Qequiv : ∀ a b c d, b ≠ 0 → d ≠ 0 → a / b = c / d ↔ a * d = b * c.
Proof.
  intros [a A] [b B] [c C] [d D] H H0.
  split; intros H1; unfold embed in *; destruct excluded_middle_informative;
    try (now contradiction); [symmetry in H1 | symmetry];
      destruct excluded_middle_informative; try (now contradiction);
        [apply quotient_equiv in H1 | apply quotient_equiv];
        auto using rational_equivalence; simpl in *.
  - apply Specify_classification in H1 as [H1 [c' [d' [a' [b' [H2 H3]]]]]].
    repeat rewrite Ordered_pair_iff in *.
    intuition.
    subst.
    destruct a', b', c', d'.
    simpl in *.
    replace A with i; replace B with i0; replace C with i1;
      replace D with i2; auto using proof_irrelevance.
    ring [H3].
  - apply Specify_classification.
    split.
    + apply Product_classification.
      exists (c, d), (a, b).
      assert (∀ e f (F : f ∈ Zset), e ∈ Zset → (exist _ _ F) ≠ 0 → (e, f) ∈ Z0);
        eauto.
      intros e f F E H2.
      apply Specify_classification.
      split; try apply Product_classification; eauto.
      unfold proj2.
      destruct excluded_middle_informative;
        try (contradict n1; apply Product_classification; eauto).
      repeat destruct constructive_indefinite_description.
      destruct a0 as [H3 [H4 H5]].
      apply Ordered_pair_iff in H5 as [H6 H7].
      contradict H2.
      subst.
      now apply set_proj_injective.
    + exists (exist _ _ C : Z), (exist _ _ D : Z),
      (exist _ _ A : Z), (exist _ _ B : Z).
      repeat split; auto.
      ring [H1].
Qed.

Definition IZQ a := a / 1.
Coercion IZQ : Z >-> Q.

Definition zero := 0 / 1.
Definition one := 1 / 1.
Notation "0" := zero : Q_scope.
Notation "1" := one : Q_scope.

Definition add : Q → Q → Q.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (Qlift x)) as [a e].
  destruct (constructive_indefinite_description _ e) as [b [e0 e1]].
  destruct (constructive_indefinite_description _ (Qlift y)) as [c e2].
  destruct (constructive_indefinite_description _ e2) as [d [e3 e4]].
  exact ((a * d + c * b) / (b * d)).
Defined.

Definition mul : Q → Q → Q.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (Qlift x)) as [a e].
  destruct (constructive_indefinite_description _ e) as [b [e0 e1]].
  destruct (constructive_indefinite_description _ (Qlift y)) as [c e2].
  destruct (constructive_indefinite_description _ e2) as [d [e3 e4]].
  exact ((a * c) / (b * d)).
Defined.

Definition neg : Q → Q.
Proof.
  intros x.
  destruct (constructive_indefinite_description _ (Qlift x)) as [a e].
  destruct (constructive_indefinite_description _ e) as [b [e0 e1]].
  exact (-a / b).
Defined.

Definition inv : Q → Q.
Proof.
  intros x.
  destruct (constructive_indefinite_description _ (Qlift x)) as [a e].
  destruct (constructive_indefinite_description _ e) as [b [e0 e1]].
  exact (b / a).
Defined.

Infix "+" := add : Q_scope.
Infix "*" := mul : Q_scope.
Notation "- a" := (neg a) : Q_scope.
Notation "a '^-1' " := (inv a) (at level 30, format "a '^-1'") : Q_scope.

Definition sub a b := a + -b.
Definition div a b := a * b^-1.

Infix "-" := sub : Q_scope.

Theorem add_wf : ∀ a b c d : Z,
    b ≠ 0%Z → d ≠ 0%Z → (a / b) + (c / d) = (a * d + c * b) / (b * d).
Proof.
  intros a b c d H H0.
  unfold add.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  rewrite Qequiv in *; auto; try ring [e1 e2];
    intros H1; apply (cancellation_0_mul ℤ_order) in H1; tauto.
Qed.

Theorem mul_wf : ∀ a b c d : Z,
    b ≠ 0%Z → d ≠ 0%Z → (a / b) * (c / d) = (a * c) / (b * d).
Proof.
  intros a b c d H H0.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  rewrite Qequiv in *; auto; try ring [e1 e2];
    intros H1; apply (cancellation_0_mul ℤ_order) in H1; tauto.
Qed.

Theorem neg_wf : ∀ a b : Z, b ≠ 0%Z → -(a / b) = (-a) / b.
Proof.
  intros a b H.
  unfold neg.
  repeat destruct constructive_indefinite_description.
  destruct a0.
  rewrite Qequiv in *; auto.
  ring [e0].
Qed.

Theorem inv_wf : ∀ a b : Z, a ≠ 0%Z → b ≠ 0%Z → (a / b)^-1 = b / a.
Proof.
  intros a b H H0.
  unfold inv.
  repeat destruct constructive_indefinite_description.
  destruct a0.
  rewrite Qequiv in e0; auto.
  rewrite Qequiv; auto.
  intros H1.
  subst.
  replace (0*b)%Z with (0%Z) in * by ring.
  symmetry in e0.
  apply (cancellation_0_mul ℤ_order) in e0.
  tauto.
Qed.

Theorem A3 : ∀ x, 0 + x = x.
Proof.
  intros [x H].
  unfold add in *.
  repeat destruct constructive_indefinite_description.
  destruct a, a0.
  rewrite <-add_wf, e1, <-e2; auto.
  unfold zero.
  rewrite add_wf, Qequiv; auto.
  - ring.
  - contradict n0.
    ring [n0].
  - apply zero_ne_1.
Qed.

Theorem A1 : ∀ a b, a + b = b + a.
Proof.
  intros [a A] [b B].
  unfold add in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  rewrite Qequiv in *; auto;
    try (intros Z; apply (cancellation_0_mul ℤ_order) in Z; tauto).
  ring.
Qed.

Theorem A2 : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  intros [a A] [b B] [c C].
  unfold add in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4.
  rewrite Qequiv in *; auto;
    try (intros Z; apply (cancellation_0_mul ℤ_order) in Z; tauto).
  apply (cancellation_mul_r (integral_domain ℤ_order) x3); auto; simpl.
  now ring_simplify [e7 e8].
Qed.

Theorem M3 : ∀ x, 1 * x = x.
Proof.
  intros [x H].
  unfold mul in *.
  repeat destruct constructive_indefinite_description.
  destruct a, a0.
  rewrite <-mul_wf, e1, <-e2; auto.
  unfold one.
  rewrite mul_wf, Qequiv; auto.
  - ring.
  - contradict n0.
    ring [n0].
  - apply zero_ne_1.
Qed.

Theorem M1 : ∀ a b, a * b = b * a.
Proof.
  intros [a A] [b B].
  unfold mul in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  rewrite Qequiv in *; auto;
    try (intros Z; apply (cancellation_0_mul ℤ_order) in Z; tauto).
  ring.
Qed.

Theorem M2 : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  intros [a A] [b B] [c C].
  unfold mul in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4.
  rewrite Qequiv in *; auto;
    try (intros Z; apply (cancellation_0_mul ℤ_order) in Z; tauto).
  apply (cancellation_mul_r (integral_domain ℤ_order) x3); auto; simpl.
  now ring_simplify [e7 e8].
Qed.

Theorem D1 : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  intros [a A] [b B] [c C].
  unfold mul, add in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4, a5.
  rewrite Qequiv in *; auto;
    try (intros Z; apply (cancellation_0_mul ℤ_order) in Z; tauto).
  apply (cancellation_mul_r (integral_domain ℤ_order) x3); auto; simpl.
  apply (cancellation_mul_r (integral_domain ℤ_order) x1); auto; simpl.
  ring_simplify.
  replace (x*x5*x8*x10*x3*x1)%Z with (x*(x1*x3)*x5*x8*x10)%Z by ring.
  replace (x8*x3*x1*x4*x6*x9)%Z with ((x9*(x3*x6)*x1*x4*x8))%Z by ring.
  replace (x10*x3*x1*x4*x6*x7)%Z with (x7*(x1*x6)*x3*x4*x10)%Z by ring.
  rewrite e7, e9, e10.
  now ring_simplify.
Qed.

Theorem sub_neg : ∀ a b, a - b = a + -b.
Proof.
  auto.
Qed.

Theorem A4 : ∀ a, a + -a = 0.
Proof.
  intros [a A].
  unfold add, neg.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  unfold zero.
  rewrite Qequiv in *; eauto using zero_ne_1;
    try (intros Z; apply (cancellation_0_mul ℤ_order) in Z; tauto).
  ring [e2].
Qed.

Theorem zero_ne_1 : 1 ≠ 0.
Proof.
  intros H.
  unfold zero, one, mul in *;
    rewrite Qequiv, ? integers.M3 in H;
    now eapply zero_ne_1.
Qed.

Theorem div_inv : ∀ a b, div a b = a * b^-1.
Proof.
  auto.
Qed.

Theorem inv_l : ∀ a, a ≠ 0 → a^-1 * a = 1.
Proof.
  intros a H.
  unfold inv, mul.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  unfold one.
  rewrite Qequiv in *; auto.
  - ring [e2].
  - intros H0.
    subst.
    contradict H.
    unfold zero.
    rewrite Qequiv; auto; try ring.
    apply integers.zero_ne_1.
  - intros H0.
    apply (cancellation_0_mul ℤ_order) in H0.
    tauto.
  - apply integers.zero_ne_1.
Qed.

Definition ℚ_ring := mkRing _ 0 1 add mul neg A3 A1 A2 M3 M1 M2 D1 A4.

Definition ℚ := mkField ℚ_ring inv inv_l zero_ne_1.

Add Field rational_field_raw : (fieldify ℚ).
Add Field rational_field :
  (fieldify ℚ : field_theory 0 1 add mul sub neg div inv eq).

Definition positive : Q → Prop.
Proof.
  intros x.
  destruct (constructive_indefinite_description _ (Qlift x)) as [a e].
  destruct (constructive_indefinite_description _ e) as [b [e0 e1]].
  exact (a * b > 0).
Defined.

Lemma pos_wf : ∀ a b, b ≠ 0%Z → positive (a / b) ↔ a * b > 0.
Proof.
  assert (∀ x y z w,
             y ≠ 0 → z ≠ 0 → x * y = z * w → 0 < x → 0 < z → 0 < w * y)%Z as L.
  { intros x y z w H H0 H1 H2 H3.
    destruct (integers.T w 0), (integers.T y 0); intuition; subst;
      try (now apply (mul_neg_neg ℤ_order); simpl);
      try (now apply (mul_pos_pos ℤ_order); simpl).
    + assert (0 < x * y) by now apply (mul_pos_pos ℤ_order).
      assert (z * w < 0) by now apply (mul_pos_neg ℤ_order).
      rewrite H1 in *.
      exfalso; eapply (lt_antisym ℤ_order); eauto.
    + replace (z*0)%Z with 0%Z in * by ring.
      apply (cancellation_0_mul ℤ_order) in H1 as [H1 | H1]; subst;
        exfalso; eauto using lt_irrefl.
    + assert (x * y < 0) by now apply (mul_pos_neg ℤ_order).
      assert (0 < z * w) by now apply (mul_pos_pos ℤ_order).
      rewrite H1 in *.
      exfalso; eapply (lt_antisym ℤ_order); eauto.
    + replace (z*0)%Z with 0%Z in * by ring.
      apply (cancellation_0_mul ℤ_order) in H1 as [H1 | H1]; subst;
        exfalso; eauto using lt_irrefl. }
  split; intros H0; unfold positive in *;
    repeat destruct constructive_indefinite_description;
    destruct a0; rewrite Qequiv in *; auto;
      assert (a * x0 = b * x)%Z as e1 by ring [e0];
      assert (-x * b = -x0 * a)%Z as e2 by ring [e0];
      assert (-a * x0 = -b * x)%Z as e3 by ring [e0];
      apply (pos_mul ℤ_order) in H0 as [[H0 H1] | [H0 H1]]; eauto.
  - apply L in e2; rewrite lt_neg_0 in *; auto.
    contradict n.
    ring [n].
  - apply L in e3; rewrite lt_neg_0 in *; auto.
    contradict H.
    ring [H].
Qed.

Theorem T_pos : ∀ x, positive x ∧ x ≠ 0 ∧ ¬ positive (-x) ∨
                     ¬ positive x ∧ x = 0 ∧ ¬ positive (-x) ∨
                     ¬ positive x ∧ x ≠ 0 ∧ positive (-x).
Proof.
  intros x.
  destruct (Qlift x) as [a [b [H H0]]].
  subst.
  unfold zero.
  rewrite neg_wf, ? pos_wf, Qequiv; auto using integers.zero_ne_1.
  replace (-a*b)%Z with (-(a*b))%Z by ring.
  rewrite <-(lt_neg_0 ℤ_order).
  replace (a * 1 = b * 0)%Z with (a * b = 0)%Z.
  - destruct (integers.T (a*b) 0); intuition.
  - apply propositional_extensionality.
    replace (b*0)%Z with 0%Z by ring.
    rewrite (M3_r ℤ).
    split; intros H0; subst; try ring.
    now apply (cancellation_0_mul ℤ_order) in H0 as [H0 | H0].
Qed.

Definition lt : Q → Q → Prop.
Proof.
  intros x y.
  exact (positive (y - x)).
Defined.

Infix "<" := lt : Q_scope.

Theorem T : ∀ a b, a < b ∧ a ≠ b ∧ ¬ b < a
                   ∨ ¬ a < b ∧ a = b ∧ ¬ b < a
                   ∨ ¬ a < b ∧ a ≠ b ∧ b < a.
Proof.
  intros a b.
  unfold lt.
  replace (a-b) with (-(b-a)) by ring.
  replace (a=b) with (b-a=0); eauto using T_pos.
  apply propositional_extensionality.
  split; intros H; try ring [H].
  replace b with (a+(b-a)) by ring.
  rewrite H.
  ring.
Qed.

Theorem O0 : ∀ a b, 0 < a → 0 < b → 0 < a + b.
Proof.
  intros x y H H0.
  unfold lt, sub in *.
  replace (-0) with 0 in * by ring.
  rewrite A1, A3 in *.
  destruct (Qlift x) as [a [b [H1 H2]]], (Qlift y) as [c [d [H3 H4]]].
  rewrite <-H2, <-H4, add_wf, pos_wf in *;
    auto using (ne0_cancellation (integral_domain ℤ_order)).
  apply (pos_mul ℤ_order) in H as [[H H5] | [H H5]];
    apply (pos_mul ℤ_order) in H0 as [[H0 H6] | [H0 H6]];
    try rewrite (lt_neg_0 ℤ_order) in *;
    [ | replace ((a*d+c*b)*(b*d))%Z with ((a*-d+-c*b)*(b*-d))%Z by ring
      | replace ((a*d+c*b)*(b*d))%Z with ((-a*d+c*-b)*(-b*d))%Z by ring
      | replace ((a*d+c*b)*(b*d))%Z with ((-a*-d+-c*-b)*(-b*-d))%Z by ring ];
    eauto 6 using (mul_pos_pos ℤ_order), (O0 ℤ_order) with Z.
Qed.

Theorem lt_trans : ∀ a b c, a < b → b < c → a < c.
Proof.
  intros a b c H H0.
  unfold lt in *.
  replace (c-a) with ((b-a)+(c-b)-0) by ring.
  apply O0.
  - now replace (b-a) with ((b-a)-0) in H by ring.
  - now replace (c-b) with ((c-b)-0) in H0 by ring.
Qed.

Theorem O1 : ∀ a b c, b < c → a + b < a + c.
Proof.
  intros a b c H.
  unfold lt in *.
  now replace (a + c - (a + b)) with (c - b) by ring.
Qed.

Theorem O2 : ∀ a b, 0 < a → 0 < b → 0 < a * b.
Proof.
  intros x y H H0.
  unfold lt, sub in *.
  replace (-0) with 0 in * by ring.
  rewrite A1, A3 in *.
  destruct (Qlift x) as [a [b [H1 H2]]], (Qlift y) as [c [d [H3 H4]]].
  subst.
  rewrite mul_wf, pos_wf in *;
    auto using (ne0_cancellation (integral_domain ℤ_order)).
  replace (a*c*(b*d))%Z with ((a*b)*(c*d))%Z by ring.
  now apply (mul_pos_pos ℤ_order).
Qed.

Definition ℚ_ring_order := mkOR ℚ_ring lt lt_trans T O1 O2 zero_ne_1.
Definition ℚ_order := mkOF ℚ lt lt_trans T O1 O2.

Notation "a > b" := (b < a) (only parsing) : Q_scope.

Definition le := ordered_rings.le ℚ_ring_order : Q → Q → Prop.
Infix "≤" := le : Q_scope.
Notation "a ≥ b" := (b ≤ a) (only parsing) : Q_scope.
Notation "a < b < c" := (a < b ∧ b < c) (at level 70, b at next level): Q_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level): Q_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level): Q_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level): Q_scope.

Theorem lt_dense : ∀ a b, a < b → ∃ c, a < c ∧ c < b.
Proof.
  intros x y H.
  destruct (Qlift x) as [a [b [H0 H1]]], (Qlift y) as [c [d [H2 H3]]]; subst.
  exists ((b*c + a*d)/(2*b*d)).
  assert (2 ≠ 0)%Z as H1 by apply (ordered_rings.zero_ne_2 ℤ_order).
  split; unfold lt, sub in *; rewrite neg_wf, add_wf, pos_wf in *;
    auto using (ne0_cancellation (integral_domain ℤ_order));
    [ replace (((b*c+a*d)*b+-a*(2*b*d))*(2*b*d*b))%Z
        with (2*(b*b)*((c*b+-a*d)*(d*b)))%Z by ring |
      replace ((c*(2*b*d)+-(b*c+a*d)*d)*(d*(2*b*d)))%Z
        with (2*(d*d)*((c*b+-a*d)*(d*b)))%Z by ring ];
    eauto using (mul_pos_pos ℤ_order), (ordered_rings.O0 ℤ_order),
    (square_ne0 ℤ_order), (ordered_rings.zero_lt_1 ℤ_order) with Z.
Qed.

Theorem lt_dense2 : ∀ a b, 0 < a → 0 < b → ∃ c, 0 < c ∧ c < a ∧ c < b.
Proof.
  intros a b H H0.
  destruct (lt_or_ge ℚ_ring_order a b) as [H1 | H1]; fold le in *;
    simpl in *.
  - destruct (lt_dense 0 a) as [c [H2 H3]]; auto.
    exists c.
    eauto using lt_trans.
  - destruct (lt_dense 0 b) as [c [H2 H3]]; auto.
    exists c.
    destruct H1 as [H1 | H1]; simpl in *; subst; eauto using lt_trans.
Qed.

Theorem pos_denom : ∀ x, ∃ a b, (0 < b ∧ x = a / b)%Z.
Proof.
  intros x.
  destruct (Qlift x) as [a [b [H H0]]].
  destruct (integers.T b 0); intuition; eauto.
  exists (-a)%Z, (-b)%Z.
  rewrite <-(lt_neg_0 ℤ_order) in *.
  split; auto.
  subst.
  rewrite Qequiv; auto; try ring.
  contradict H1; ring [H1].
Qed.

Theorem reduced_form : ∀ x, ∃ a b, gcd (a,b) = 1 ∧ x = a / b ∧ b ≠ 0%Z.
Proof.
  intros x.
  destruct (Qlift x) as [a [b [H H0]]], (common_factor a b)
      as [d [H1 [[m H2] [[n H3] H4]]]]; auto.
  exists m, n.
  repeat split; auto using (div_1_l ℤ) with Z; subst.
  - intros z [k H5] [l H6].
    subst.
    assert (z*d｜d) as [e H0].
    { apply H4; rewrite <-integers.M2;
        auto using (div_mul_l ℤ), (div_refl ℤ) with Z. }
    rewrite integers.M2, <-(integers.M3 d) in H0 at 1.
    apply (cancellation_mul_r (integral_domain ℤ_order)) in H0;
      try now (exists e).
    now apply (cancellation_ne0 ℤ) in H.
  - rewrite Qequiv; simpl in *; fold Z in *; auto; try ring.
    now apply (cancellation_ne0 ℤ) in H.
  - now apply (cancellation_ne0 ℤ) in H.
Qed.

Theorem Rudin_1_1 : ¬ ∃ p : Q, p * p = 2.
Proof.
  intros [p H].
  unfold IZQ in H.
  destruct (reduced_form p) as [m [n [H0 [H1 H2]]]].
  subst.
  rewrite mul_wf, Qequiv in H;
    auto using (ne0_cancellation (integral_domain ℤ_order)),
    integers.zero_ne_1.
  rewrite (integers.M1 _ 1), integers.M3, (integers.M1 _ 2) in H.
  assert (2｜(m*m)) as H1.
  { rewrite H.
    eauto using (div_mul_r ℤ), (div_refl ℤ) with Z. }
  apply Euclid's_lemma in H1; auto using two_is_prime.
  assert (2｜m) as [k H3] by tauto; simpl in *; fold Z in *.
  subst.
  replace (k*2*(k*2))%Z with (2*(2*k*k))%Z in H by ring.
  apply (cancellation_mul_l (integral_domain ℤ_order)) in H.
  - assert (2｜(n*n)) as H3.
    { rewrite <-H;
        eauto using (div_mul_r ℤ), (div_refl ℤ) with Z. }
    apply Euclid's_lemma in H3; auto using two_is_prime.
    assert (2｜n) as [l H4] by tauto.
    subst.
    pose proof two_is_prime as [H4 H5].
    contradiction H4.
    destruct H0 as [H0 [H6 H7]].
    apply H7; auto using (div_mul_l ℤ), (div_refl ℤ) with Z.
  - intros H3; simpl in H3.
    unfold integers.zero, integers.one in *.
    rewrite INZ_add, add_1_r in H3.
    now apply eq_sym, INZ_eq, PA4 in H3.
Qed.

Theorem IZQ_add : ∀ a b : Z, a + b = (a + b)%Z.
Proof.
  intros a b.
  unfold IZQ.
  rewrite add_wf, Qequiv; auto using integers.zero_ne_1; try ring.
  rewrite integers.M3.
  auto using integers.zero_ne_1.
Qed.

Theorem IZQ_mul : ∀ a b : Z, a * b = (a * b)%Z.
Proof.
  intros a b.
  unfold IZQ.
  rewrite mul_wf, Qequiv; auto using integers.zero_ne_1; try ring.
  rewrite integers.M3.
  auto using integers.zero_ne_1.
Qed.

Theorem IZQ_neg : ∀ a : Z, -a = (-a)%Z.
Proof.
  intros a.
  unfold IZQ.
  rewrite neg_wf, Qequiv; auto using integers.zero_ne_1; ring.
Qed.

Theorem IZQ_lt : ∀ a b, (a < b)%Z ↔ a < b.
Proof.
  intros a b.
  split; intros H; unfold lt, IZQ, sub in *;
    rewrite neg_wf, add_wf, pos_wf in *; auto using integers.zero_ne_1;
      try (rewrite integers.M3 in *; auto using integers.zero_ne_1);
      replace ((b*1+-a*1)*1)%Z with (b+-a)%Z in * by ring.
  - rewrite <-(integers.A4 a), ? (integers.A1 _ (-a)).
    now apply integers.O1.
  - apply (integers.O1 a) in H.
    now ring_simplify in H.
Qed.

Theorem IZQ_eq : ∀ a b : Z, (a : Q) = (b : Q) ↔ a = b.
Proof.
  intros a b.
  split; intros H; try now subst.
  unfold IZQ in *.
  rewrite Qequiv in *; auto using integers.zero_ne_1.
  ring [H].
Qed.

Theorem IZQ_le : ∀ a b, (a ≤ b)%Z ↔ a ≤ b.
Proof.
  intros a b.
  split; intros [H | H].
  - left; now apply IZQ_lt.
  - right; now apply IZQ_eq.
  - left; now apply IZQ_lt.
  - right; now apply IZQ_eq.
Qed.

Lemma canonical_form_uniq : ∀ a b c d,
    a / b = c / d → b ≠ 0%Z → d ≠ 0%Z →
    gcd (a, b) = 1 → gcd (c, d) = 1 → a ~ c ∧ b ~ d.
Proof.
  intros a b c d H H0 H1.
  rewrite Qequiv in H; auto.
  repeat split; eapply FTA; eauto using gcd_sym;
    [ rewrite <-H | rewrite integers.M1, H |
      rewrite H | rewrite integers.M1, <-H ];
    auto using (div_mul_l ℤ), (div_mul_r ℤ), (div_refl ℤ) with Z.
Qed.

Theorem canonical_form : ∀ x, exists ! a b, gcd (a,b) = 1 ∧ x = a / b ∧ b > 0%Z.
Proof.
  intros x.
  destruct (reduced_form x) as [a [b [H [H0 H1]]]].
  destruct (classic (a = 0)%Z) as [H2 | H2].
  - subst.
    exists 0%Z.
    split.
    + exists 1%Z.
      split.
      * repeat split;
          auto using zero_lt_1, (div_0_r ℤ), (div_refl ℤ) with Z.
        -- rewrite Qequiv; auto using integers.zero_ne_1.
           ring.
        -- apply IZQ_lt, zero_lt_1.
      * intros x' [H0 [H2 H3]].
        apply gcd_0_l, assoc_pm in H0 as [H0 | H0]; auto.
        subst.
        rewrite <-IZQ_lt, <-(lt_neg_0 ℤ_order) in H3.
        contradiction (ordered_rings.lt_antisym ℤ_order 0%Z 1%Z);
          simpl; auto using zero_lt_1.
    + intros x' [y [[H0 [H2 H3]] H4]].
      rewrite <-IZQ_lt in H3.
      destruct (integers.T y 0) as [H5 | [H5 | H5]]; try tauto.
      rewrite Qequiv in H2; try tauto.
      assert (0｜x') as H6.
      { eapply FTA; eauto.
        rewrite <-H2.
        auto using (div_mul_r ℤ), (div_refl ℤ) with Z. }
      now apply div_0_l in H6.
  - destruct (integers.T b 0) as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]];
      try tauto.
    + exists (-a)%Z.
      split.
      * exists (-b)%Z.
        split.
        -- split.
           ++ rewrite <-gcd_neg.
              apply gcd_sym.
              rewrite <-gcd_neg.
              now apply gcd_sym.
           ++ split; try now rewrite <-IZQ_lt, <-(lt_neg_0 ℤ_order).
              subst.
              rewrite Qequiv; try ring; contradict H1; ring [H1].
        -- intros x' [H6 [H7 H8]].
           subst.
           rewrite <-IZQ_lt in H8.
           destruct (integers.T x' 0) as [H9 | [H9 | H9]]; try tauto.
           rewrite Qequiv in H7; try tauto.
           replace (b*-a)%Z with (a*-b)%Z in * by ring.
           apply (cancellation_mul_l (integral_domain ℤ_order)) in H7;
             auto.
      * intros x' [y [[H6 [H7 H8]] H9]].
        subst.
        rewrite <-IZQ_lt in H8.
        destruct (integers.T y 0) as [H10 | [H10 | H10]]; try tauto.
        pose proof H7 as H11.
        apply canonical_form_uniq in H11 as [H11 H12]; try tauto.
        apply assoc_pm in H11 as [H11 | H11]; try ring [H11].
        subst.
        rewrite Qequiv, integers.M1 in H7; try tauto.
        apply (cancellation_mul_r (integral_domain ℤ_order)) in H7;
          auto.
        subst.
        contradiction (ordered_rings.lt_antisym ℤ_order 0%Z b).
    + exists a.
      split.
      * exists b.
        split.
        -- repeat (split; auto).
           now rewrite <-IZQ_lt.
        -- intros x' [H6 [H7 H8]].
           subst.
           rewrite <-IZQ_lt in H8.
           destruct (integers.T x' 0) as [H9 | [H9 | H9]]; try tauto.
           rewrite Qequiv, integers.M1 in H7; try tauto.
           apply (cancellation_mul_r (integral_domain ℤ_order)) in H7;
             auto.
      * intros x' [y [[H6 [H7 H8]] H9]].
        subst.
        rewrite <-IZQ_lt in H8.
        destruct (integers.T y 0) as [H10 | [H10 | H10]]; try tauto.
        pose proof H7 as H11.
        apply canonical_form_uniq in H11 as [H11 H12]; try tauto.
        apply assoc_pm in H11 as [H11 | H11]; try ring [H11].
        subst.
        rewrite Qequiv in H7; try tauto.
        replace (-x'*y)%Z with (-y*x')%Z in * by ring.
        apply (cancellation_mul_r (integral_domain ℤ_order)) in H7;
          auto.
        -- subst.
           rewrite <-(lt_neg_0 ℤ_order) in H5.
           contradiction (ordered_rings.lt_antisym ℤ_order 0%Z y).
        -- contradict H2; simpl in *.
           rewrite H2.
           ring.
Qed.

Theorem inv_div : ∀ a b : Z, b ≠ 0%Z → a / b = a * b^-1.
Proof.
  intros a b H.
  unfold IZQ.
  rewrite inv_wf, mul_wf, Qequiv; auto using integers.zero_ne_1.
  - ring.
  - contradict H.
    ring [H].
Qed.

Theorem Z_archimedean : ∀ x, ∃ z : Z, z ≤ x < z+1.
Proof.
  intros x.
  destruct (pos_denom x) as [a [b [H H0]]].
  destruct (division_algorithm a b) as [q [r [H1 [H2 H3]]]]; auto.
  assert (b ≠ 0%Z) as H4 by (pose proof (integers.T b 0); tauto).
  exists q.
  subst.
  split.
  - destruct H2 as [H2 | H2].
    + left; simpl.
      unfold lt, sub, IZQ.
      rewrite neg_wf, add_wf, pos_wf, ? (M3_r ℤ);
        auto using integers.zero_ne_1.
      * replace ((b*q+r+-q*b)*b)%Z with (b*r)%Z in * by ring.
        now apply (mul_pos_pos ℤ_order).
      * contradict H4.
        ring [H4].
    + right.
      subst.
      rewrite (A3_r ℤ), inv_div, M1, <-IZQ_mul, M2, inv_l, M3; auto.
      contradict H4.
      unfold IZQ, zero in *.
      rewrite Qequiv in H4; auto using integers.zero_ne_1.
      ring [H4].
  - unfold IZQ, lt, sub, one.
    rewrite neg_wf, ? add_wf, pos_wf, ? (M3_r ℤ);
      auto using integers.zero_ne_1.
    + replace (((q+1)*b+-(b*q+r))*(1*b))%Z with (b*(b+-r))%Z by ring.
      apply (mul_pos_pos ℤ_order); auto; simpl.
      now apply (ordered_rings.lt_shift ℤ_order) in H3.
    + contradict H4.
      ring [H4].
    + rewrite integers.M3.
      apply integers.zero_ne_1.
Qed.

Definition floor (x : Q) : Z.
Proof.
  destruct (constructive_indefinite_description _ (Z_archimedean x)) as [z].
  exact z.
Defined.

Notation "'⌊' x '⌋'" := (floor x) (format "'⌊' x '⌋'").

Theorem floor_refl : ∀ x, ⌊x⌋ ≤ x.
Proof.
  intros x.
  unfold floor.
  destruct constructive_indefinite_description.
  tauto.
Qed.

Theorem floor_upper : ∀ x (z : Z), z ≤ x → z ≤ ⌊x⌋.
Proof.
  intros x z H.
  unfold floor.
  destruct constructive_indefinite_description as [y [H0 H1]].
  apply le_not_gt; simpl.
  intros H2.
  contradiction (lt_0_1 (z+-y)).
  - apply (lt_shift ℚ_ring_order) in H2; simpl in *.
    apply IZQ_lt.
    now rewrite <-IZQ_add, <-IZQ_neg.
  - rewrite (lt_shift ℤ_order); simpl.
    replace (1+-(z+-y))%Z with (y+1+-z)%Z by ring.
    rewrite <-(lt_shift ℤ_order); simpl.
    eapply IZQ_lt, (le_lt_trans ℚ_ring_order); eauto; simpl.
    now rewrite <-IZQ_add.
Qed.

Lemma floor_le : ∀ x y, x ≤ y → ⌊x⌋ ≤ ⌊y⌋.
Proof.
  pose proof (le_trans ℚ_ring_order : ∀ a b c : Q, a ≤ b → b ≤ c → a ≤ c).
  eauto using floor_refl, floor_upper.
Qed.

Lemma floor_lower : ∀ x (z : Z), x < z+1 → ⌊x⌋ ≤ z.
Proof.
  intros x z H.
  unfold floor.
  destruct constructive_indefinite_description as [y [H0 H1]].
  apply le_not_gt; simpl.
  intros H2.
  contradiction (lt_0_1 (y+-z)).
  - now apply IZQ_lt, (lt_shift ℤ_order) in H2.
  - assert (y < z+1)%Z.
    { apply IZQ_lt.
      eapply (le_lt_trans ℚ_ring_order); eauto.
      now rewrite <-IZQ_add. }
    rewrite (lt_shift ℤ_order) in H3 |-*; simpl in *.
    now replace (1+-(y+-z))%Z with (z+1+-y)%Z by ring.
Qed.

Theorem floor_plus_1 : ∀ x, x < ⌊x⌋+1.
Proof.
  intros x.
  unfold floor.
  now destruct constructive_indefinite_description.
Qed.

Theorem floor_add_int : ∀ x (z : Z), ⌊z+x⌋ = (z + ⌊x⌋)%Z.
Proof.
  intros x z.
  apply IZQ_eq, (ordered_rings.le_antisymm ℚ_ring_order); fold le.
  - apply floor_lower.
    rewrite <-IZQ_add, <-A2.
    apply O1, floor_plus_1.
  - apply floor_upper.
    rewrite <-IZQ_add.
    apply add_le_l, floor_refl.
Qed.

Theorem Q_archimedean : ∀ x b, 0 < b → ∃ n : Z, n * b ≤ x < (n + 1) * b.
Proof.
  intros x b H.
  assert (b ≠ 0) as H0 by (pose proof (T b 0); tauto).
  destruct (Z_archimedean (x*b^-1)) as [n [[H1 | H1] H2]]; exists n;
    repeat split; rewrite <-(M3 x), <-(inv_l b) at 1; auto;
      rewrite ? (M1 _ b), <-M2, (M1 _ x).
  * now apply or_introl, (O3 ℚ_ring_order).
  * now apply (O3 ℚ_ring_order).
  * apply or_intror; congruence.
  * now apply (O3 ℚ_ring_order).
Qed.

Theorem inv_zero : 0^-1 = 0.
Proof.
  unfold inv.
  repeat destruct constructive_indefinite_description.
  destruct a.
  unfold zero in e0.
  rewrite Qequiv, (M3_r ℤ) in e0; auto using integers.zero_ne_1.
  replace (x0*0)%Z with 0%Z in e0 by ring.
  subst.
  clear e n.
  unfold embed.
  repeat destruct excluded_middle_informative;
    apply set_proj_injective; simpl; try now contradiction n.
  unfold zero, embed.
  repeat destruct excluded_middle_informative; simpl; auto.
Qed.

Theorem inv_neg : ∀ a, -a^-1 = (-a)^-1.
Proof.
  intros a.
  destruct (classic (a = 0)); subst.
  - rewrite inv_zero.
    replace (-0) with 0 by field.
    now rewrite inv_zero.
  - now apply (fields.inv_neg ℚ).
Qed.

Definition inv_ne_0 := fields.inv_ne_0 ℚ : ∀ a, a ≠ 0 → a^-1 ≠ 0.

Theorem inv_inv : ∀ a, a^-1^-1 = a.
Proof.
  intros a.
  destruct (classic (a = 0)); subst.
  - now rewrite ? inv_zero.
  - now apply (fields.inv_inv ℚ).
Qed.

Theorem inv_mul : ∀ a b, a^-1 * b^-1 = (a*b)^-1.
Proof.
  intros a b.
  destruct (classic (a = 0)), (classic (b = 0)); subst;
    try now rewrite ? inv_zero, ? (mul_0_l ℚ_ring), ? (mul_0_r ℚ_ring);
    simpl; rewrite ? inv_zero.
  now field.
Qed.

Theorem one_lt_2 : 1 < 2.
Proof.
  apply IZQ_lt, (one_lt_2 ℤ_order).
Qed.

Definition pow := pow ℚ : Q → Z → Q.
Infix "^" := pow : Q_scope.

Definition pow_0_r := pow_0_r ℚ : ∀ a, a^0 = 1.

Theorem pow_0_l : ∀ a : Z, a ≠ 0%Z → 0^a = 0.
Proof.
  intros a H.
  destruct (classic (a < 0)%Z).
  - unfold pow, fields.pow.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description;
      try destruct a0; try tauto; simpl in *; unfold pow_N.
    + contradiction (ordered_rings.lt_antisym ℤ_order a 0%Z).
    + rewrite inv_zero, (rings.pow_0_l ℚ_ring); auto.
      contradict n0.
      now subst.
  - apply (pow_0_l ℚ).
    pose proof (integers.T a 0).
    tauto.
Qed.

Theorem pow_neg : ∀ a b, a^(-b) = (a^-1)^b.
Proof.
  intros a b.
  destruct (classic (a = 0)) as [H | H], (classic (b = 0%Z)) as [H0 | H0];
    try (now apply (pow_neg ℚ)); subst; rewrite inv_zero.
  - replace (-0)%Z with 0%Z by ring.
    now rewrite ? pow_0_r.
  - rewrite ? pow_0_l; auto.
    contradict H0.
    ring [H0].
Qed.

Theorem inv_pow : ∀ a, a^(-(1)) = a^-1.
Proof.
  intros a.
  destruct (classic (a = 0)) as [H | H].
  - subst.
    now rewrite pow_neg, (pow_1_r ℚ).
  - apply (inv_unique ℚ); auto.
    now rewrite pow_neg, (pow_1_r ℚ), M1, inv_l.
Qed.

Theorem pow_mul_l : ∀ a b c, (a*b)^c = a^c * b^c.
Proof.
  intros a b c.
  destruct (classic (a = 0)) as [H | H], (classic (b = 0)) as [H0 | H0];
    subst; try (now apply (pow_mul_l ℚ));
      destruct (classic (c = 0%Z)) as [H1 | H1];
      subst; rewrite ? pow_0_r in *; try now rewrite M3.
  - now rewrite ? (mul_0_l ℚ_ring), ? pow_0_l, ? (mul_0_l ℚ_ring).
  - now rewrite ? pow_0_l, ? (mul_0_l ℚ_ring), pow_0_l.
  - now rewrite ? pow_0_l, ? (mul_0_r ℚ_ring), pow_0_l.
Qed.

Theorem neg_pow : ∀ a b, a^(-b) = (a^b)^-1.
Proof.
  intros a b.
  destruct (classic (a = 0)); subst.
  - destruct (classic (b = 0%Z)); subst.
    + replace (-0)%Z with 0%Z by ring.
      now rewrite pow_0_r, (fields.inv_one ℚ : 1^-1 = 1).
    + rewrite ? pow_0_l, inv_zero; auto.
      contradict H.
      ring [H].
  - now apply (fields.neg_pow ℚ).
Qed.

Theorem pow_mul_r : ∀ a b c, a^(b*c) = (a^b)^c.
Proof.
  intros a b c.
  destruct (classic (a = 0)) as [H | H]; subst.
  - destruct (classic (b*c = 0)%Z) as [H0 | H0].
    + apply (cancellation_0_mul ℤ_order) in H0 as [H0 | H0];
        simpl in *; subst.
      * replace (0*c)%Z with 0%Z by ring.
        now rewrite pow_0_r, (pow_1_l ℚ).
      * replace (b*0)%Z with 0%Z by ring.
        now rewrite ? pow_0_r.
    + pose proof H0 as H.
      apply (cancellation_ne0 ℤ) in H0 as [H0 H1]; simpl in *.
      now rewrite ? pow_0_l.
  - now apply (fields.pow_mul_r ℚ).
Qed.

Theorem pow_div_distr : ∀ a b c, (a*b^-1)^c = a^c * (b^c)^-1.
Proof.
  intros a b c.
  now rewrite pow_mul_l, <-neg_pow, pow_neg.
Qed.

Lemma a_g_pow_ineq : ∀ (x : Q) (n : Z), 0 < x → (0 < n)%Z → 1 + n*x ≤ (1 + x)^n.
Proof.
  intros x n H H0.
  induction n using strong_induction.
  destruct (integers.T 1 n) as [[H2 [H3 H4]] | [[H2 [H3 H4]] | [H2 [H3 H4]]]].
  assert (0 < n+-(1))%Z as H5.
  { rewrite <-(integers.A4 1), ? (integers.A1 _ (-(1))).
    now apply integers.O1. }
  - assert (0 < 1+x) as H6.
    { apply (lt_trans _ 1); try apply (ordered_rings.zero_lt_1 ℚ_ring_order).
      rewrite <-(A3 1), A1 at 1.
      now apply O1. }
    destruct (H1 (n+-(1))%Z) as [H7 | H7]; auto.
    + split; auto.
      replace n with (n+(-(1))+1)%Z at 2 by ring.
      apply (ordered_rings.lt_succ ℤ_order).
    + left.
      apply (O3 ℚ_ring_order (1+x)) in H7; auto.
      rewrite <-(fields.pow_1_r ℚ (1+x)) in H7 at 2.
      rewrite <-(fields.pow_add_r ℚ) in H7; auto using (lt_neq ℚ_ring_order).
      replace (1 + (n + - (1)))%Z with n in * by ring.
      rewrite D1, M3, (M1 x), D1, A2, <-(A2 1), <-D1 in H7.
      rewrite <-IZQ_add, <-IZQ_neg, <-(A2 n),
      (A1 (-(1))), A4, (A1 _ 0), A3 in H7.
      eapply lt_trans; eauto.
      rewrite <-(A3 (1+n*x)), (A1 0) at 1.
      rewrite IZQ_lt, <-IZQ_add, <-IZQ_neg in H5.
      auto using O1, O2.
    + replace n with (n+(-(1))+1)%Z at 2 by ring.
      rewrite (pow_add_r ℚ); auto using (lt_neq ℚ_ring_order);
        fold pow; simpl.
      rewrite <-H7, (pow_1_r ℚ), <-IZQ_add, ? D1, M3, <-IZQ_neg.
      replace (IZQ 1%Z) with 1 by auto.
      replace (1+x+(n*x*(1+x)+-(1)*x*(1+x))) with (1+n*x+x*x*(n+-(1))) by ring.
      rewrite <-(A3 (1+n*x)), (A1 0) at 1.
      left; simpl.
      rewrite IZQ_lt, <-IZQ_add, <-IZQ_neg in H5.
      auto using O1, O2.
  - subst.
    rewrite M3, (pow_1_r ℚ).
    now right.
  - contradiction (lt_0_1 n).
Qed.

Theorem pos_pow_archimedean : ∀ a r, 1 < r → ∃ n, (0 < n)%Z ∧ a < r^n.
Proof.
  intros a r H.
  destruct (classic (1 < a)).
  - assert (0 < r+-(1)) as H1 by now rewrite <-(lt_shift ℚ_ring_order).
    apply (Q_archimedean (a+-(1))) in H1 as [n [H1 H2]].
    exists (n+1)%Z.
    assert (0 < n+1)%Z as H3.
    { rewrite IZQ_lt, <-IZQ_add.
      destruct (T 0 (n+1)) as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]];
        auto.
      - rewrite <-H4 in *.
        replace (0 * (r + - (1))) with 0 in * by ring.
        rewrite (lt_shift ℚ_ring_order) in H0; simpl in H0.
        pose proof (T 0 (a+-(1))).
        tauto.
      - apply (O3 ℚ_ring_order (r+-(1))) in H5; try now rewrite <-lt_shift.
        replace ((r + - (1)) * 0) with 0 in H5 by ring.
        rewrite M1, mul_0_r in H5.
        assert (a + -(1) < 0) as H6 by eauto using lt_trans.
        rewrite (lt_shift ℚ_ring_order) in H0; simpl in H0.
        pose proof (T 0 (a+-(1))).
        tauto. }
    split; auto.
    assert (a < 1 + (n+1)*(r+-(1))) as H4.
    { rewrite (lt_shift ℚ_ring_order) in H2 |-*; simpl in *.
      now replace (1+(n+1)*(r+-(1))+-a) with ((n+1)*(r+-(1))+-(a+-(1)))
        by ring. }
    destruct (a_g_pow_ineq (r + - (1)) (n+1)) as [H5 | H5];
      replace (1 + (r + - (1))) with r in * by ring; auto.
    + now rewrite <-(lt_shift ℚ_ring_order).
    + rewrite <-IZQ_add in H5.
      eauto using lt_trans.
    + now rewrite <-H5, <-IZQ_add.
  - assert (a = 1 ∨ a < 1) as [H1 | H1] by (pose proof (T a 1); tauto);
      exists 1%Z; split; auto using integers.zero_lt_1;
        rewrite (pow_1_r ℚ); subst; eauto using lt_trans.
Qed.

Theorem neg_pow_archimedean : ∀ a r, 0 < a → 1 < r → ∃ n, (n < 0)%Z ∧ r^n < a.
Proof.
  intros a r H H0.
  assert (0 < r) as H1.
  { eapply lt_trans; try apply H0;
      apply (ordered_rings.zero_lt_1 ℚ_ring_order). }
  apply (pos_pow_archimedean (a^-1) r) in H0 as [n [H0 H2]].
  exists (-n)%Z.
  split.
  - rewrite IZQ_lt, (lt_shift ℚ_ring_order), <-? IZQ_neg in *; simpl in *.
    replace (IZQ 0) with 0 in * by auto.
    now replace (0+--n) with (n+-0) by ring.
  - apply (O3 ℚ_ring_order a) in H2; auto.
    rewrite ? (M1 a), inv_l in H2; auto using (lt_neq ℚ_ring_order).
    apply (O3 ℚ_ring_order (r^-n)) in H2.
    + rewrite M1, M3, M2, <-(pow_add_r ℚ), integers.A1, integers.A4,
      pow_0_r, M3 in H2; auto using (lt_neq ℚ_ring_order).
    + now apply (pow_pos ℚ_order).
Qed.

Theorem square_in_interval : ∀ a, 1 < a → ∃ r, 0 < r ∧ 1 < r * r < a.
Proof.
  intros a H.
  assert (3 ≠ 0)%Z as H0.
  { apply (lt_neq ℤ_order), (ordered_rings.O0 ℤ_order);
      try apply (ordered_rings.O0 ℤ_order);
      auto using (ordered_rings.zero_lt_1 ℤ_order). }
  destruct (classic (2 < a)) as [H1 | H1].
  - exists (4/3).
    repeat split.
    + unfold zero, lt, sub.
      rewrite neg_wf, add_wf, pos_wf; rewrite ? (M3_r ℤ);
        auto using integers.zero_ne_1.
      replace ((4+-0*3)*3)%Z with (4+4+4)%Z by ring.
      repeat apply (ordered_rings.O0 ℤ_order);
        auto using (ordered_rings.zero_lt_1 ℤ_order).
    + unfold one, lt, sub.
      rewrite mul_wf, neg_wf, add_wf, pos_wf; auto using integers.zero_ne_1.
      * replace ((4*4*1+-(1)*(3*3))*(3*3*1))%Z with ((1+3+3)*(3*3))%Z by ring.
        repeat apply integers.O2; repeat apply (ordered_rings.O0 ℤ_order);
          auto using (ordered_rings.zero_lt_1 ℤ_order).
      * intros H2.
        apply (cancellation_0_mul ℤ_order) in H2 as [H2 | H2];
          try now contradiction integers.zero_ne_1.
        now apply cancellation_0_mul in H2 as [H2 | H2].
      * intros H2.
        now apply (cancellation_0_mul ℤ_order) in H2 as [H2 | H2].
    + eapply lt_trans; eauto.
      unfold IZQ, lt, sub.
      rewrite mul_wf, neg_wf, add_wf, pos_wf; auto using integers.zero_ne_1.
      * replace ((2*(3*3)+-(4*4)*1)*(1*(3*3)))%Z with (2*3*3)%Z by ring.
        repeat apply integers.O2; repeat apply (ordered_rings.O0 ℤ_order);
          auto using (ordered_rings.zero_lt_1 ℤ_order).
      * intros H2.
        apply (cancellation_0_mul ℤ_order) in H2 as [H2 | H2];
          try now contradiction integers.zero_ne_1.
        now apply cancellation_0_mul in H2 as [H2 | H2].
      * intros H2.
        now apply (cancellation_0_mul ℤ_order) in H2 as [H2 | H2].
      * intros H2.
        now apply (cancellation_0_mul ℤ_order) in H2 as [H2 | H2].
  - set (r := 1+(a+-(1)) * 3^-1).
    exists r.
    assert (1 < r) as H2.
    { rewrite <-(A3 1), (A1 0) at 1.
      apply O1, O2.
      - now rewrite <-(lt_shift ℚ_ring_order).
      - rewrite <-? IZQ_add.
        apply (inv_lt ℚ_order); simpl; repeat apply O0;
          apply (ordered_rings.zero_lt_1 ℚ_ring_order). }
    assert (0 < r) as H3.
    { eapply lt_trans; eauto.
      apply (ordered_rings.zero_lt_1 ℚ_ring_order). }
    pose proof H2 as H4.
    apply (ordered_fields.pow_gt_1 ℚ_order _ 2) in H4;
      try apply (ordered_rings.O0 ℤ_order);
      try apply (ordered_rings.zero_lt_1 ℤ_order).
    rewrite (pow_add_r ℚ) in H4; simpl in *; fold pow in *;
      auto using (lt_neq ℚ_ring_order).
    rewrite <-pow_mul_l, (pow_1_r ℚ) in H4; auto using lt_neq.
    repeat split; auto.
    assert (r*r + -(1) = (r+-(1)) * (r+1)) as H5 by ring.
    assert (a ≤ 2) as H6 by
          (destruct (T 2 a) as [[H6 _] | [[_ [H6 _]] | [_ [_ H6]]]];
           subst; unfold le, ordered_rings.le; try tauto).
    assert (r+1 < 3) as H7.
    { rewrite <-IZQ_add, (A1 2), ? (A1 _ 1), <-IZQ_add.
      unfold r.
      repeat apply O1.
      destruct H6 as [H6 | H6].
      - rewrite <-(integers.M3 1) at 4.
        rewrite <-IZQ_mul.
        apply (lt_cross_mul ℚ_ring_order).
        + now rewrite <-lt_shift.
        + apply (inv_lt ℚ_order); simpl.
          rewrite <-? IZQ_add.
          repeat apply O0; apply (ordered_rings.zero_lt_1 ℚ_ring_order).
        + rewrite lt_shift in H6 |-*; simpl in *.
          replace (-(a+-(1))) with (-a+1) by ring.
          rewrite A1, <-A2.
          replace (1 + 1%Z) with (1%Z+1%Z) by auto.
          now rewrite IZQ_add, A1.
        + apply (inv_lt_1 ℚ_order); rewrite <-? IZQ_add; simpl.
          * repeat apply O0; apply (ordered_rings.zero_lt_1 ℚ_ring_order).
          * rewrite <-(A3 1), A1, <-A2 at 1.
            unfold IZQ, one.
            apply O1, O0; apply (ordered_rings.zero_lt_1 ℚ_ring_order).
      - subst.
        rewrite <-IZQ_add, <-A2, A4, A1, A3, M3.
        apply (inv_lt_1 ℚ_order); rewrite <-? IZQ_add; simpl.
        + repeat apply O0; apply (ordered_rings.zero_lt_1 ℚ_ring_order).
        + rewrite <-(A3 1), A1, <-A2 at 1.
          unfold IZQ, one.
          apply O1, O0; apply (ordered_rings.zero_lt_1 ℚ_ring_order). }
    apply (O3 ℚ_ring_order (r+-(1))) in H7; try now rewrite <-lt_shift.
    unfold r in H7 at 3.
    rewrite <-A2, (A1 1), <-A2, ? (A1 _ 1), A4, (A1 _ 0), A3, <-M2, inv_l in H7;
      simpl in H7.
    + rewrite (A1 1), <-H5, (M1 _ 1), M3, ? (A1 _ (-(1))) in H7.
      rewrite <-(A3 (r*r)), <-(A3 a), <-(A4 1), <-? A2.
      now apply O1.
    + contradict H0.
      now rewrite <-IZQ_eq.
Qed.

Theorem division_signed : ∀ a b : Z,
    (0 < b)%Z → ∃ q r : Z, 0 ≤ r ≤ b / 2 ∧ b*q + (-(1))^⌊2 * a / b⌋ * r = a.
Proof.
  intros a b H.
  destruct (division_algorithm a b) as [q [r [H0 [H1 H2]]]]; subst; auto.
  destruct (classic (r < b/2)) as [H0 | H0]; subst.
  - exists q, r.
    repeat split; try (now apply IZQ_le || now left).
    rewrite <-IZQ_add, <-IZQ_mul.
    rewrite <-(M3 r) at 2.
    repeat f_equal.
    replace ⌊2 * (b * q + r) / b⌋ with (2*q)%Z.
    + rewrite pow_mul_r.
      unfold pow, integers.one.
      rewrite INZ_add, <-pow_wf, add_1_r.
      unfold pow_N.
      now rewrite rings.pow_2_r, rings.mul_neg_neg, M3, pow_1_l.
    + apply (ordered_rings.le_antisymm ℤ_order); fold integers.le.
      * apply IZQ_le, floor_upper.
        rewrite inv_div, <-? IZQ_mul, <-M2; auto using (pos_ne_0 ℤ_order).
        apply mul_le_l; try apply IZQ_lt, (ordered_rings.zero_lt_2 ℤ_order);
          fold le.
        apply IZQ_lt in H.
        apply IZQ_le in H1.
        rewrite <-IZQ_add, <-IZQ_mul, D1, M1, M2, inv_l;
          auto using (pos_ne_0 ℚ_ring_order).
        rewrite M3, <-(A3_r ℚ_ring (q:Q)) at 1; simpl.
        apply add_le_l, mul_nonneg_nonneg; simpl; fold le; auto.
        now apply or_introl, (inv_lt ℚ_order).
      * apply IZQ_le, floor_lower.
        rewrite inv_div, <-? IZQ_mul, <-M2; auto using (pos_ne_0 ℤ_order).
        apply IZQ_lt in H.
        rewrite <-? (IZQ_add _ r), <-IZQ_mul, D1, (M1 (b*q)), M2, inv_l;
          auto using (pos_ne_0 ℚ_ring_order).
        rewrite M3, (rings.D1_l ℚ_ring); simpl.
        apply O1.
        rewrite <-(inv_l 2), (M1 _ 2).
        2: { intros H4.
             now apply IZQ_eq, (zero_ne_2 ℤ_order) in H4. }
        apply (O3 ℚ_ring_order); simpl.
        { apply IZQ_lt, (ordered_rings.zero_lt_2 ℤ_order). }
        rewrite <-(M3 (2^-1)), (M1 1), <-(inv_l b), (M1 _ b), M2;
          auto using (pos_ne_0 ℚ_ring_order).
        apply (O3_r ℚ_ring_order); simpl; try now apply (inv_lt ℚ_order).
        rewrite M1, <-inv_div; auto using (zero_ne_2 ℤ_order).
  - exists (q+1)%Z, (b+-r)%Z.
    repeat split.
    { rewrite <-(A4 r), <-IZQ_add, <-IZQ_neg.
      now apply (add_le_r ℚ_ring_order), IZQ_le, or_introl. }
    { apply (le_not_gt ℚ_ring_order) in H0; fold le in H0.
      rewrite <-(A3 (b/2)), (A1 0), <-(A4 r), A2, <-IZQ_add, <-IZQ_neg.
      apply (add_le_r ℚ_ring_order); fold le.
      rewrite <-(M3 b), M1, <-(inv_l 2), (M1 _ 2), M2, inv_div;
        auto using (zero_ne_2 ℤ_order).
      2: { intros H5; apply IZQ_eq in H5; auto using (zero_ne_2 ℤ_order). }
      rewrite <-IZQ_add, (D1_l ℚ_ring), ? M3_r, D1 at 1; simpl.
      apply add_le_l; fold le.
      rewrite <-inv_div; auto using (zero_ne_2 ℤ_order). }
    replace ((-(1)) ^ ⌊2 * (b * q + r) / b⌋) with (-(1)).
    { rewrite <-? IZQ_add, <-IZQ_mul, <-IZQ_neg.
      unfold IZQ at 3.
      fold one.
      ring. }
    replace ⌊2 * (b * q + r) / b⌋ with (2*q+1)%Z.
    { rewrite (pow_add_r ℚ), pow_1_r, pow_mul_r;
        auto using (minus_one_nonzero ℚ); simpl.
      unfold pow, integers.one.
      rewrite INZ_add, <-pow_wf, add_1_r.
      unfold pow_N.
      now rewrite rings.pow_2_r, rings.mul_neg_neg, ? M3, pow_1_l, M3. }
    apply (ordered_rings.le_antisymm ℤ_order); fold integers.le.
    + apply IZQ_le, floor_upper.
      rewrite inv_div, <-? IZQ_mul, <-M2; auto using (pos_ne_0 ℤ_order).
      apply IZQ_lt in H.
      rewrite <- (IZQ_add _ r), <-IZQ_mul, D1, (M1 (b*q)), M2, inv_l, M3;
        auto using (pos_ne_0 ℚ_ring_order).
      rewrite (D1_l ℚ_ring), <-IZQ_add, <-IZQ_mul; simpl.
      apply add_le_l; fold le.
      apply (le_not_gt ℚ_ring_order) in H0; fold le in H0.
      unfold IZQ at 1; fold one.
      rewrite <-(inv_l b); auto using (pos_ne_0 ℚ_ring_order).
      rewrite M2, (M1 _ (b^-1)).
      apply mul_le_l; simpl; fold le; try now apply (inv_lt ℚ_order).
      rewrite <-(M3 b), <-(inv_l 2), (M1 _ 2), <-M2.
      2: { intros H5; apply IZQ_eq in H5; auto using (zero_ne_2 ℤ_order). }
      apply mul_le_l; simpl; fold le; try (apply IZQ_lt, (zero_lt_2 ℤ_order)).
      rewrite M1, <-inv_div; auto using (zero_ne_2 ℤ_order).
    + apply IZQ_le, floor_lower.
      rewrite inv_div, <-? IZQ_mul, <-M2; auto using (pos_ne_0 ℤ_order).
      apply IZQ_lt in H, H2.
      rewrite <- (IZQ_add _ r), <-IZQ_mul, D1, (M1 (b*q)), M2, inv_l, M3;
        auto using (pos_ne_0 ℚ_ring_order).
      rewrite <-(IZQ_add (2*q)), <-IZQ_mul, (D1_l ℚ_ring), <-A2; simpl.
      apply O1.
      unfold one.
      fold (IZQ 1).
      rewrite IZQ_add.
      rewrite <-(M3 2) at 2.
      rewrite (M1 1).
      apply (O3 ℚ_ring_order); simpl.
      * apply IZQ_lt, (ordered_rings.zero_lt_2 ℤ_order).
      * rewrite <-(inv_l b), (M1 _ b); auto using (pos_ne_0 ℚ_ring_order).
        apply (mul_lt_r ℚ_ring_order); auto; now apply (inv_lt ℚ_order).
Qed.

Theorem QR_epsilon_construction :
  ∀ a b : Z, (0 < a → 0 < b → 0 ≤ ⌊a / b⌋)%Z.
Proof.
  intros a b H H0.
  apply IZQ_le, floor_upper.
  rewrite inv_div; auto using (pos_ne_0 ℤ_order).
  apply (mul_nonneg_nonneg ℚ_ring_order); simpl; fold le.
  - apply IZQ_le; fold integers.le; left; simpl; auto.
  - now apply or_introl, (inv_lt ℚ_order), IZQ_lt.
Qed.

Definition QR_ε_exp (a b : Z) : N.
Proof.
  destruct (excluded_middle_informative (0 < a)%Z) as [H | H].
  - destruct (excluded_middle_informative (0 < b)%Z) as [H0 | H0].
    + eapply QR_epsilon_construction, le_def in H0; try apply H.
      destruct (constructive_indefinite_description _ H0) as [c H1].
      exact c.
    + exact 0%N.
  - exact 0%N.
Defined.

Theorem IZQ_pow : ∀ (a : Z) (n : N), a^n = (a^n : Z)%Z.
Proof.
  intros a n.
  destruct (classic (a = 0%Z)); subst.
  { destruct (classic (n = 0%N)); subst.
    - unfold pow.
      now rewrite rings.pow_0_r, pow_0_r.
    - rewrite rings.pow_0_l, pow_0_l; auto.
      contradict H.
      now apply INZ_eq. }
  induction n using Induction.
  - now rewrite pow_0_r, rings.pow_0_r.
  - unfold pow in *.
    rewrite pow_succ_r, <-add_1_r, <-INZ_add, pow_add_r, pow_1_r,
    <-IZQ_mul, <-pow_wf, <-IHn, <-pow_wf; auto.
    contradict H.
    now apply IZQ_eq.
Qed.

Definition QR_ε (a b : Z) := ((-(1))^(QR_ε_exp a b) : Z)%Z.

Theorem division_QR : ∀ a b : Z,
    (0 < a → 0 < b → ∃ q r : Z, 0 ≤ r ≤ ⌊b / 2⌋ ∧ b*q + QR_ε (2*a) b * r = a)%Z.
Proof.
  intros a b H H0.
  unfold QR_ε, QR_ε_exp.
  repeat destruct excluded_middle_informative; try tauto.
  2: { contradiction n.
       apply (ordered_rings.mul_pos_pos ℤ_order);
       auto; apply (ordered_rings.zero_lt_2 ℤ_order). }
  destruct constructive_indefinite_description.
  rewrite integers.A3 in e.
  eapply division_signed in H0 as [q [r [[H0 H1] H2]]]; try apply H.
  exists q, r.
  repeat split.
  - now apply IZQ_le.
  - now apply IZQ_le, floor_upper.
  - apply IZQ_eq.
    now rewrite <-H2, e, <-IZQ_add, <-? IZQ_mul, <-IZQ_pow, <-IZQ_neg.
Qed.
