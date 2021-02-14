Require Export ordered_fields Field.

Definition ℤ0 := {z in ℤ × ℤ | (proj2 ℤ ℤ z) ≠ 0}.

Definition rational_relation :=
  {z in ℤ0 × ℤ0 | ∃ a b c d : Z, z = ((a, b), (c, d)) ∧ a * d = b * c}.

Theorem rational_equivalence : is_equivalence ℤ0 rational_relation.
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
    apply (cancellation_mul_l (integral_domain_OR integer_order) b'); simpl.
    + apply Specify_classification in H0 as [H0 H4].
      rewrite proj2_eval in H4; unfold IZS; auto using elts_in_set.
      contradict H4.
      now subst.
    + now ring_simplify [H5 H9].
Qed.

Definition ℚ := ℤ0 / rational_relation.

Definition Q := elts ℚ.

Definition IQS (a : Q) := elt_to_set _ a : set.
Coercion IQS : Q >-> set.

Delimit Scope Q_scope with Q.
Open Scope Q_scope.
Bind Scope Q_scope with Q.

Definition embed : Z → Z → Q.
Proof.
  intros a b.
  destruct (excluded_middle_informative (b = 0)).
  - assert ((0, 1) ∈ ℤ0) as H.
    { apply Specify_classification.
      split.
      + apply Product_classification.
        exists 0, 1.
        unfold IZS; repeat split; auto using elts_in_set.
      + unfold proj2.
        destruct excluded_middle_informative.
        repeat destruct constructive_indefinite_description.
        * destruct a0 as [H [H0 H1]].
          apply Ordered_pair_iff in H1 as [H1 H2].
          subst.
          intros H1.
          contradiction zero_ne_1.
          now apply set_proj_injective.
        * contradiction n.
          apply Product_classification.
          exists 0, 1.
          unfold IZS; repeat split; auto using elts_in_set. }
    exact (quotient_map ℤ0 rational_relation (exist _ _ H)).
  - destruct a as [a' A], b as [b' B].
    assert ((a', b') ∈ ℤ0) as H.
    { apply Specify_classification.
      split.
      + apply Product_classification; eauto.
      + contradict n.
        unfold proj2 in *.
        destruct excluded_middle_informative.
        * repeat destruct constructive_indefinite_description.
          destruct a as [H [H0 H1]].
          apply Ordered_pair_iff in H1 as [H1 H2].
          subst.
          now apply set_proj_injective.
        * contradict n0.
          apply Product_classification; eauto. }
    exact (quotient_map ℤ0 rational_relation (exist _ _ H)).
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
  unfold ℚ.
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
      assert (∀ e f (F : f ∈ ℤ), e ∈ ℤ → (exist _ _ F) ≠ 0 → (e, f) ∈ ℤ0);
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
    intros H1; apply (cancellation_0_mul integer_order) in H1; tauto.
Qed.

Theorem mul_wf : ∀ a b c d : Z,
    b ≠ 0%Z → d ≠ 0%Z → (a / b) * (c / d) = (a * c) / (b * d).
Proof.
  intros a b c d H H0.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  rewrite Qequiv in *; auto; try ring [e1 e2];
    intros H1; apply (cancellation_0_mul integer_order) in H1; tauto.
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
  apply (cancellation_0_mul integer_order) in e0.
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
    try (intros Z; apply (cancellation_0_mul integer_order) in Z; tauto).
  ring.
Qed.

Theorem A2 : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  intros [a A] [b B] [c C].
  unfold add in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4.
  rewrite Qequiv in *; auto;
    try (intros Z; apply (cancellation_0_mul integer_order) in Z; tauto).
  apply (cancellation_mul_r (integral_domain_OR integer_order) x3); auto; simpl.
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
    try (intros Z; apply (cancellation_0_mul integer_order) in Z; tauto).
  ring.
Qed.

Theorem M2 : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  intros [a A] [b B] [c C].
  unfold mul in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4.
  rewrite Qequiv in *; auto;
    try (intros Z; apply (cancellation_0_mul integer_order) in Z; tauto).
  apply (cancellation_mul_r (integral_domain_OR integer_order) x3); auto; simpl.
  now ring_simplify [e7 e8].
Qed.

Theorem D1 : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  intros [a A] [b B] [c C].
  unfold mul, add in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4, a5.
  rewrite Qequiv in *; auto;
    try (intros Z; apply (cancellation_0_mul integer_order) in Z; tauto).
  apply (cancellation_mul_r (integral_domain_OR integer_order) x3); auto; simpl.
  apply (cancellation_mul_r (integral_domain_OR integer_order) x1); auto; simpl.
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
    try (intros Z; apply (cancellation_0_mul integer_order) in Z; tauto).
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
    apply (cancellation_0_mul integer_order) in H0.
    tauto.
  - apply integers.zero_ne_1.
Qed.

Add Field rational_field :
  (mk_field div inv
            (mk_rt 0 1 add mul sub neg eq A3 A1 A2 M3 M1 M2 D1 sub_neg A4)
            zero_ne_1 div_inv inv_l).

Definition rationals :=
  mkField _ zero one add mul neg inv A3 A1 A2 M3 M1 M2 D1 A4 inv_l zero_ne_1.

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
      try (now apply (mul_neg_neg integer_order); simpl);
      try (now apply (integers.mul_pos_pos); simpl).
    + assert (0 < x * y) by now apply (integers.mul_pos_pos).
      assert (z * w < 0) by now apply (mul_pos_neg integer_order).
      rewrite H1 in *.
      exfalso; eapply (lt_antisym integer_order); eauto.
    + replace (z*0)%Z with 0%Z in * by ring.
      apply (cancellation_0_mul integer_order) in H1 as [H1 | H1]; subst;
        exfalso; eauto using lt_irrefl.
    + assert (x * y < 0) by now apply (mul_pos_neg integer_order).
      assert (0 < z * w) by now apply (integers.mul_pos_pos).
      rewrite H1 in *.
      exfalso; eapply (lt_antisym integer_order); eauto.
    + replace (z*0)%Z with 0%Z in * by ring.
      apply (cancellation_0_mul integer_order) in H1 as [H1 | H1]; subst;
        exfalso; eauto using lt_irrefl. }
  split; intros H0; unfold positive in *;
    repeat destruct constructive_indefinite_description;
    destruct a0; rewrite Qequiv in *; auto;
      assert (a * x0 = b * x)%Z as e1 by ring [e0];
      assert (-x * b = -x0 * a)%Z as e2 by ring [e0];
      assert (-a * x0 = -b * x)%Z as e3 by ring [e0];
      apply (pos_mul integer_order) in H0 as [[H0 H1] | [H0 H1]]; eauto.
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
  rewrite <-(lt_neg_0 integer_order).
  replace (a * 1 = b * 0)%Z with (a * b = 0)%Z.
  - destruct (integers.T (a*b) 0); intuition.
  - apply propositional_extensionality.
    replace (b*0)%Z with 0%Z by ring.
    rewrite (M3_r integers).
    split; intros H0; subst; try ring.
    now apply (cancellation_0_mul integer_order) in H0 as [H0 | H0].
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
  replace (a-b) with (-(b-a)) by field.
  replace (a=b) with (b-a=0); eauto using T_pos.
  apply propositional_extensionality.
  split; intros H; try ring [H].
  replace b with (a+(b-a)) by field.
  rewrite H.
  field.
Qed.

Theorem O0 : ∀ a b, 0 < a → 0 < b → 0 < a + b.
Proof.
  intros x y H H0.
  unfold lt, sub in *.
  replace (-0) with 0 in * by ring.
  rewrite A1, A3 in *.
  destruct (Qlift x) as [a [b [H1 H2]]], (Qlift y) as [c [d [H3 H4]]].
  rewrite <-H2, <-H4, add_wf, pos_wf in *;
    auto using (ne0_cancellation (integral_domain_OR integer_order)).
  apply (pos_mul integer_order) in H as [[H H5] | [H H5]];
    apply (pos_mul integer_order) in H0 as [[H0 H6] | [H0 H6]];
    try rewrite (lt_neg_0 integer_order) in *;
    [ | replace ((a*d+c*b)*(b*d))%Z with ((a*-d+-c*b)*(b*-d))%Z by ring
      | replace ((a*d+c*b)*(b*d))%Z with ((-a*d+c*-b)*(-b*d))%Z by ring
      | replace ((a*d+c*b)*(b*d))%Z with ((-a*-d+-c*-b)*(-b*-d))%Z by ring ];
    eauto 6 using integers.mul_pos_pos, integers.O0.
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
    auto using (ne0_cancellation (integral_domain_OR integer_order)).
  replace (a*c*(b*d))%Z with ((a*b)*(c*d))%Z by ring.
  now apply (integers.mul_pos_pos).
Qed.

Definition rational_ring := (ring_from_field rationals).
Definition rational_order :=
  mkOring rational_ring lt lt_trans T O1 O2 zero_ne_1.
Definition rational_field_order := mkOfield rationals lt lt_trans T O1 O2.

Notation "a > b" := (b < a) (only parsing) : Q_scope.

Definition le := ordered_rings.le rational_order : Q → Q → Prop.
Infix "≤" := le : Q_scope.
Notation "a ≥ b" := (b ≤ a) (only parsing) : Q_scope.
Notation "a < b < c" := (a < b ∧ b < c) (at level 70, b at next level): Q_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level): Q_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level): Q_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level): Q_scope.

Definition O3 :=
  ordered_rings.O3 rational_order : ∀ a b c, 0 < a → b < c → a * b < a * c.
Definition lt_irrefl := ordered_rings.lt_irrefl rational_order : ∀ a, ¬ a < a.
Definition lt_antisym :=
  ordered_rings.lt_antisym rational_order : ∀ a b, a < b → ¬ b < a.
Definition le_trans :=
  ordered_rings.le_trans rational_order : ∀ a b c, a ≤ b → b ≤ c → a ≤ c.

Theorem lt_dense : ∀ a b, a < b → ∃ c, a < c ∧ c < b.
Proof.
  intros x y H.
  destruct (Qlift x) as [a [b [H0 H1]]], (Qlift y) as [c [d [H2 H3]]].
  exists ((b*c + a*d)/(2*b*d)).
  subst.
  assert (2 ≠ 0)%Z as H1 by apply (ordered_rings.zero_ne_2 integer_order).
  split; unfold lt, sub in *; rewrite neg_wf, add_wf, pos_wf in *;
    auto using (ne0_cancellation (integral_domain_OR integer_order)).
  - replace (((b*c+a*d)*b+-a*(2*b*d))*(2*b*d*b))%Z
      with (2*(b*b)*((c*b+-a*d)*(d*b)))%Z by ring;
      eauto using integers.mul_pos_pos, integers.O0,
      integers.square_ne0, zero_lt_1.
  - replace ((c*(2*b*d)+-(b*c+a*d)*d)*(d*(2*b*d)))%Z
      with (2*(d*d)*((c*b+-a*d)*(d*b)))%Z by ring;
      eauto using integers.mul_pos_pos, integers.O0,
      integers.square_ne0, zero_lt_1.
Qed.

Theorem lt_dense2 : ∀ a b, 0 < a → 0 < b → ∃ c, 0 < c ∧ c < a ∧ c < b.
Proof.
  intros a b H H0.
  destruct (lt_or_ge rational_order a b) as [H1 | H1]; fold le in *;
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
  rewrite <-(lt_neg_0 integer_order) in *.
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
  repeat split; auto using (div_1_l integers) with Z; subst.
  - intros z [k H5] [l H6].
    subst.
    assert (z*d｜d) as [e H0].
    { apply H4; rewrite <-integers.M2;
        auto using (div_mul_l integers), (div_refl integers) with Z. }
    rewrite integers.M2, <-(integers.M3 d) in H0 at 1.
    apply (cancellation_mul_r (integral_domain_OR integer_order)) in H0;
      try now (exists e).
    now apply (cancellation_ne0 integers) in H.
  - rewrite Qequiv; simpl in *; fold Z in *; auto; try ring.
    now apply (cancellation_ne0 integers) in H.
  - now apply (cancellation_ne0 integers) in H.
Qed.

Theorem Rudin_1_1 : ¬ ∃ p : Q, p * p = 2.
Proof.
  intros [p H].
  unfold IZQ in H.
  destruct (reduced_form p) as [m [n [H0 [H1 H2]]]].
  subst.
  rewrite mul_wf, Qequiv in H;
    auto using (ne0_cancellation (integral_domain_OR integer_order)),
    integers.zero_ne_1.
  rewrite (integers.M1 _ 1), integers.M3, (integers.M1 _ 2) in H.
  assert (2｜(m*m)) as H1.
  { rewrite H.
    eauto using (div_mul_r integers), (div_refl integers) with Z. }
  apply Euclid's_lemma in H1; auto using two_is_prime.
  assert (2｜m) as [k H3] by tauto; simpl in *; fold Z in *.
  subst.
  replace (k*2*(k*2))%Z with (2*(2*k*k))%Z in H by ring.
  apply (cancellation_mul_l (integral_domain_OR integer_order)) in H.
  - assert (2｜(n*n)) as H3.
    { rewrite <-H;
        eauto using (div_mul_r integers), (div_refl integers) with Z. }
    apply Euclid's_lemma in H3; auto using two_is_prime.
    assert (2｜n) as [l H4] by tauto.
    subst.
    pose proof two_is_prime as [H4 H5].
    contradiction H4.
    destruct H0 as [H0 [H6 H7]].
    apply H7; auto using (div_mul_l integers), (div_refl integers) with Z.
  - intros H3; simpl in H3.
    unfold integers.zero, integers.one in *.
    rewrite integers.add_wf, Zequiv, ? add_0_l, ? add_0_r, ? add_1_r in H3.
    now apply eq_sym, PA4 in H3.
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

Lemma canonical_form_uniq : ∀ a b c d,
    a / b = c / d → b ≠ 0%Z → d ≠ 0%Z →
    gcd (a,b) = 1 → gcd (c,d) = 1 → a ~ c ∧ b ~ d.
Proof.
  intros a b c d H H0 H1.
  rewrite Qequiv in H; auto.
  repeat split.
  - eapply FTA; eauto.
    rewrite <-H.
    auto using (div_mul_r integers), (div_refl integers) with Z.
  - eapply FTA; eauto using gcd_sym.
    rewrite integers.M1, H.
    auto using (div_mul_l integers), (div_refl integers) with Z.
  - eapply FTA; eauto using gcd_sym.
    rewrite H.
    auto using (div_mul_r integers), (div_refl integers) with Z.
  - eapply FTA; eauto using gcd_sym.
    rewrite integers.M1, <-H.
    auto using (div_mul_l integers), (div_refl integers) with Z.
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
          auto using zero_lt_1, (div_0_r integers), (div_refl integers) with Z.
        -- rewrite Qequiv; auto using integers.zero_ne_1.
           ring.
        -- apply IZQ_lt, zero_lt_1.
      * intros x' [H0 [H2 H3]].
        apply gcd_zero_l, assoc_pm in H0 as [H0 | H0]; auto.
        subst.
        rewrite <-IZQ_lt, <-(lt_neg_0 integer_order) in H3.
        contradiction (ordered_rings.lt_antisym integer_order 0%Z 1%Z);
          simpl; auto using zero_lt_1.
    + intros x' [y [[H0 [H2 H3]] H4]].
      rewrite <-IZQ_lt in H3.
      destruct (integers.T y 0) as [H5 | [H5 | H5]]; try tauto.
      rewrite Qequiv in H2; try tauto.
      assert (0｜x') as H6.
      { eapply FTA; eauto.
        rewrite <-H2.
        auto using (div_mul_r integers), (div_refl integers) with Z. }
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
           ++ split; try now rewrite <-IZQ_lt, <-(lt_neg_0 integer_order).
              subst.
              rewrite Qequiv; try ring; contradict H1; ring [H1].
        -- intros x' [H6 [H7 H8]].
           subst.
           rewrite <-IZQ_lt in H8.
           destruct (integers.T x' 0) as [H9 | [H9 | H9]]; try tauto.
           rewrite Qequiv in H7; try tauto.
           replace (b*-a)%Z with (a*-b)%Z in * by ring.
           apply (cancellation_mul_l (integral_domain_OR integer_order)) in H7;
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
        apply (cancellation_mul_r (integral_domain_OR integer_order)) in H7;
          auto.
        subst.
        contradiction (ordered_rings.lt_antisym integer_order 0%Z b).
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
           apply (cancellation_mul_r (integral_domain_OR integer_order)) in H7;
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
        apply (cancellation_mul_r (integral_domain_OR integer_order)) in H7;
          auto.
        -- subst.
           rewrite <-(lt_neg_0 integer_order) in H5.
           contradiction (ordered_rings.lt_antisym integer_order 0%Z y).
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
      rewrite neg_wf, add_wf, pos_wf, ? (M3_r integers);
        auto using integers.zero_ne_1.
      * replace ((b*q+r+-q*b)*b)%Z with (b*r)%Z in * by ring.
        auto using mul_pos_pos.
      * contradict H4.
        ring [H4].
    + right.
      subst.
      rewrite (A3_r integers), inv_div, M1, <-IZQ_mul, M2, inv_l, M3; auto.
      contradict H4.
      unfold IZQ, zero in *.
      rewrite Qequiv in H4; auto using integers.zero_ne_1.
      ring [H4].
  - unfold IZQ, lt, sub, one.
    rewrite neg_wf, ? add_wf, pos_wf, ? integers.(M3_r);
      auto using integers.zero_ne_1.
    + replace (((q+1)*b+-(b*q+r))*(1*b))%Z with (b*(b+-r))%Z by ring.
      apply mul_pos_pos; auto.
      rewrite <-(integers.A4 r), ? (integers.A1 _ (-r)).
      now apply integers.O1.
    + contradict H4.
      ring [H4].
    + intros H5.
      contradiction integers.zero_ne_1.
      ring [H5].
Qed.

Theorem Q_archimedean : ∀ x b, 0 < b → ∃ n : Z, n * b ≤ x < (n + 1) * b.
Proof.
  intros x b H.
  assert (b ≠ 0) as H0 by (pose proof (T b 0); tauto).
  destruct (Z_archimedean (x*b^-1)) as [n [[H1 | H1] H2]]; exists n;
    repeat split; try (rewrite <-(M3 x), <-(inv_l b) at 1; auto;
                       rewrite ? (M1 _ b), <-M2, (M1 _ x); now apply O3).
  - left; simpl in *.
    rewrite <-(M3 x), <-(inv_l b), ? (M1 _ b), <-M2, (M1 _ x); auto using O3.
  - right.
    now rewrite H1, <-M2, inv_l, M1, M3.
Qed.

Definition neg_lt_0 :=
  ordered_rings.neg_lt_0 rational_order : ∀ a, 0 < a ↔ -a < 0.
Definition lt_neg_0 :=
  ordered_rings.lt_neg_0 rational_order : ∀ a, a < 0 ↔ 0 < -a.
Definition lt_sub_pos :=
  ordered_rings.lt_sub_pos rational_order : ∀  a b, 0 < b → a - b < a.
Definition lt_neq :=
  ordered_rings.lt_neq rational_order : ∀ a b, a < b → b ≠ a.
Definition lt_cross_mul :=
  ordered_rings.lt_cross_mul rational_order :
    ∀ a b c d, 0 < a → 0 < c → a < b → c < d → a * c < b * d.
Definition inv_unique :=
  inv_unique rationals : ∀ a, (∀ b, a * b = 1 → b = a^-1).
Definition inv_one := inv_one rationals : 1^-1 = 1.

Theorem inv_zero : 0^-1 = 0.
Proof.
  unfold inv.
  repeat destruct constructive_indefinite_description.
  destruct a.
  unfold zero in e0.
  rewrite Qequiv, integers.(M3_r) in e0; auto using integers.zero_ne_1.
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
  destruct (classic (a = 0)).
  - subst.
    rewrite inv_zero.
    replace (-0) with 0 by field.
    now rewrite inv_zero.
  - now apply (fields.inv_neg rationals).
Qed.

Definition inv_ne_0 := fields.inv_ne_0 rationals : ∀ a, a ≠ 0 → a^-1 ≠ 0.

Theorem inv_inv : ∀ a, a^-1^-1 = a.
Proof.
  intros a.
  destruct (classic (a = 0)).
  - subst.
    now rewrite ? inv_zero.
  - now apply (fields.inv_inv rationals).
Qed.

Theorem inv_mul : ∀ a b, a^-1 * b^-1 = (a*b)^-1.
Proof.
  intros a b.
  destruct (classic (a = 0)), (classic (b = 0)); subst;
    try now rewrite ? inv_zero, ? (mul_0_l (ring_from_field rationals)),
    ? (mul_0_r (ring_from_field rationals)); simpl; rewrite ? inv_zero.
  now field.
Qed.

Definition cancellation_mul_0 :=
  cancellation_ID (integral_domain_from_field rationals) :
    ∀ a b, a * b = 0 → a = 0 ∨ b = 0.

Definition cancellation_mul_l :=
  cancellation_mul_l (integral_domain_from_field rationals) :
    ∀ a b c, a ≠ 0 → a * b = a * c → b = c.

Definition zero_lt_1 := ordered_rings.zero_lt_1 rational_order : 0 < 1.

Theorem one_lt_2 : 1 < 2.
Proof.
  apply IZQ_lt, (one_lt_2 integer_order).
Qed.

Definition pow := pow rationals : Q → Z → Q.
Infix "^" := pow : Q_scope.

Definition pow_0_r := pow_0_r rationals : ∀ a, a^0 = 1.

Theorem pow_0_l : ∀ a : Z, a ≠ 0%Z → 0^a = 0.
Proof.
  intros a H.
  destruct (classic (a < 0)%Z).
  - unfold pow, fields.pow.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description;
      try destruct a0; try tauto; simpl in *; unfold pow_N.
    + contradiction (ordered_rings.lt_antisym integer_order a 0%Z).
    + rewrite inv_zero, (rings.pow_0_l rational_ring); auto.
      contradict n0.
      now subst.
  - apply (pow_0_l rationals).
    pose proof (integers.T a 0).
    tauto.
Qed.

Theorem pow_neg : ∀ a b, a^(-b) = (a^-1)^b.
Proof.
  intros a b.
  destruct (classic (a = 0)) as [H | H], (classic (b = 0%Z)) as [H0 | H0];
    try (now apply (pow_neg rationals)); subst; rewrite inv_zero.
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
    now rewrite pow_neg, (pow_1_r rationals).
  - apply inv_unique; auto.
    now rewrite pow_neg, (pow_1_r rationals), M1, inv_l.
Qed.

Theorem pow_mul_l : ∀ a b c, (a*b)^c = a^c * b^c.
Proof.
  intros a b c.
  destruct (classic (a = 0)) as [H | H], (classic (b = 0)) as [H0 | H0];
    subst; try (now apply (pow_mul_l rationals));
      destruct (classic (c = 0%Z)) as [H1 | H1];
      subst; rewrite ? pow_0_r in *; try now rewrite M3.
  - now rewrite ? (mul_0_l rational_ring), ? pow_0_l, ? (mul_0_l rational_ring).
  - now rewrite ? pow_0_l, ? (mul_0_l rational_ring), pow_0_l.
  - now rewrite ? pow_0_l, ? (mul_0_r rational_ring), pow_0_l.
Qed.

Theorem neg_pow : ∀ a b, a^(-b) = (a^b)^-1.
Proof.
  intros a b.
  destruct (classic (a = 0)); subst.
  - destruct (classic (b = 0%Z)); subst.
    + replace (-0)%Z with 0%Z by ring.
      now rewrite pow_0_r, inv_one.
    + rewrite ? pow_0_l, inv_zero; auto.
      contradict H.
      ring [H].
  - now apply (fields.neg_pow rationals).
Qed.

Theorem pow_mul_r : ∀ a b c, a^(b*c) = (a^b)^c.
Proof.
  intros a b c.
  destruct (classic (a = 0)) as [H | H]; subst.
  - destruct (classic (b*c = 0)%Z) as [H0 | H0].
    + apply (cancellation_0_mul integer_order) in H0 as [H0 | H0];
        simpl in *; subst.
      * replace (0*c)%Z with 0%Z by ring.
        now rewrite pow_0_r, (pow_1_l rationals).
      * replace (b*0)%Z with 0%Z by ring.
        now rewrite ? pow_0_r.
    + pose proof H0 as H.
      apply (cancellation_ne0 integers) in H0 as [H0 H1]; simpl in *.
      now rewrite ? pow_0_l.
  - now apply (fields.pow_mul_r rationals).
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
    { apply (lt_trans _ 1); auto using zero_lt_1.
      rewrite <-(A3 1), A1 at 1.
      now apply O1. }
    destruct (H1 (n+-(1))%Z) as [H7 | H7]; auto.
    + split; auto.
      replace n with (n+(-(1))+1)%Z at 2 by ring.
      apply (ordered_rings.lt_succ integer_order).
    + left.
      apply (O3 (1+x)) in H7; auto.
      rewrite <-(fields.pow_1_r rationals (1+x)) in H7 at 2.
      rewrite <-(fields.pow_add_r rationals) in H7; auto using lt_neq.
      replace (1 + (n + - (1)))%Z with n in * by ring.
      rewrite D1, M3, (M1 x), D1, A2, <-(A2 1), <-D1 in H7.
      rewrite <-IZQ_add, <-IZQ_neg, <-(A2 n),
      (A1 (-(1))), A4, (A1 _ 0), A3 in H7.
      eapply lt_trans; eauto.
      rewrite <-(A3 (1+n*x)), (A1 0) at 1.
      rewrite IZQ_lt, <-IZQ_add, <-IZQ_neg in H5.
      auto using O1, O2.
    + replace n with (n+(-(1))+1)%Z at 2 by ring.
      rewrite (pow_add_r rationals); auto using lt_neq; fold pow; simpl.
      rewrite <-H7, (pow_1_r rationals), <-IZQ_add, ? D1, M3, <-IZQ_neg.
      replace (IZQ 1%Z) with 1 by auto.
      replace (1+x+(n*x*(1+x)+-(1)*x*(1+x))) with (1+n*x+x*x*(n+-(1))) by ring.
      rewrite <-(A3 (1+n*x)), (A1 0) at 1.
      left; simpl.
      rewrite IZQ_lt, <-IZQ_add, <-IZQ_neg in H5.
      auto using O1, O2.
  - subst.
    rewrite M3, (pow_1_r rationals).
    now right.
  - contradiction (lt_0_1 n).
Qed.

Definition lt_shift := (lt_shift rational_order) : ∀ a b, a < b ↔ 0 < b + -a.

Theorem pos_pow_archimedean : ∀ a r, 1 < r → ∃ n, (0 < n)%Z ∧ a < r^n.
Proof.
  intros a r H.
  destruct (classic (1 < a)).
  - assert (0 < r+-(1)) as H1 by now rewrite <-lt_shift.
    apply (Q_archimedean (a+-(1))) in H1 as [n [H1 H2]].
    exists (n+1)%Z.
    assert (0 < n+1)%Z as H3.
    { rewrite IZQ_lt, <-IZQ_add.
      destruct (T 0 (n+1)) as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]];
        auto.
      - rewrite <-H4 in *.
        replace (0 * (r + - (1))) with 0 in * by ring.
        rewrite lt_shift in H0.
        pose proof (T 0 (a+-(1))).
        tauto.
      - apply (O3 (r+-(1))) in H5; try now rewrite <-lt_shift.
        replace ((r + - (1)) * 0) with 0 in H5 by ring.
        rewrite M1 in H5.
        assert (a + -(1) < 0) as H6 by eauto using lt_trans.
        rewrite lt_shift in H0.
        pose proof (T 0 (a+-(1))).
        tauto. }
    split; auto.
    assert (a < 1 + (n+1)*(r+-(1))) as H4.
    { rewrite lt_shift in H2 |-*.
      now replace (1+(n+1)*(r+-(1))+-a) with ((n+1)*(r+-(1))+-(a+-(1)))
        by ring. }
    destruct (a_g_pow_ineq (r + - (1)) (n+1)) as [H5 | H5];
      replace (1 + (r + - (1))) with r in * by ring; auto.
    + now rewrite <-lt_shift.
    + rewrite <-IZQ_add in H5.
      eauto using lt_trans.
    + now rewrite <-H5, <-IZQ_add.
  - assert (a = 1 ∨ a < 1) as [H1 | H1] by (pose proof (T a 1); tauto);
      exists 1%Z; split; auto using integers.zero_lt_1;
        rewrite (pow_1_r rationals); subst; eauto using lt_trans.
Qed.

Theorem neg_pow_archimedean : ∀ a r, 0 < a → 1 < r → ∃ n, (n < 0)%Z ∧ r^n < a.
Proof.
  intros a r H H0.
  assert (0 < r) as H1 by eauto using lt_trans, zero_lt_1.
  apply (pos_pow_archimedean (a^-1) r) in H0 as [n [H0 H2]].
  exists (-n)%Z.
  split.
  - rewrite IZQ_lt, lt_shift in H0.
    rewrite IZQ_lt, lt_shift, <-IZQ_neg.
    replace (IZQ 0) with 0 in * by auto.
    now replace (0+--n) with (n+-0) by ring.
  - apply (O3 a) in H2; auto.
    rewrite ? (M1 a), inv_l in H2; auto using lt_neq.
    apply (O3 (r^-n)) in H2.
    + rewrite M1, M3, M2, <-(pow_add_r rationals), integers.A1, integers.A4,
      pow_0_r, M3 in H2; auto using lt_neq.
    + now apply (pow_pos rational_field_order).
Qed.

Theorem square_in_interval : ∀ a, 1 < a → ∃ r, 0 < r ∧ 1 < r * r < a.
Proof.
  intros a H.
  assert (3 ≠ 0)%Z as H0.
  { apply (ordered_rings.lt_neq integer_order), integers.O0;
      auto using integers.zero_lt_1.
    apply integers.O0; auto using integers.zero_lt_1. }
  destruct (classic (2 < a)) as [H1 | H1].
  - exists (4/3).
    repeat split.
    + unfold zero, lt, sub.
      rewrite neg_wf, add_wf, pos_wf; auto using integers.zero_ne_1.
      replace ((4*1+-0*3)*(3*1))%Z with (4+4+4)%Z by ring.
      auto 6 using integers.O0, integers.zero_lt_1.
      now rewrite integers.M1, integers.M3.
    + unfold one, lt, sub.
      rewrite mul_wf, neg_wf, add_wf, pos_wf; auto using integers.zero_ne_1.
      * replace ((4*4*1+-(1)*(3*3))*(3*3*1))%Z with ((4+3)*(3*3))%Z by ring.
        auto 6 using integers.O2, integers.O0, integers.zero_lt_1.
      * intros H2.
        apply (cancellation_0_mul integer_order) in H2 as [H2 | H2];
          try now contradiction integers.zero_ne_1.
        now apply cancellation_0_mul in H2 as [H2 | H2].
      * intros H2.
        now apply (cancellation_0_mul integer_order) in H2 as [H2 | H2].
    + eapply lt_trans; eauto.
      unfold IZQ, lt, sub.
      rewrite mul_wf, neg_wf, add_wf, pos_wf; auto using integers.zero_ne_1.
      * replace ((2*(3*3)+-(4*4)*1)*(1*(3*3)))%Z with (2*3*3)%Z by ring.
        auto 6 using integers.O2, integers.O0, integers.zero_lt_1.
      * intros H2.
        apply (cancellation_0_mul integer_order) in H2 as [H2 | H2];
          try now contradiction integers.zero_ne_1.
        now apply cancellation_0_mul in H2 as [H2 | H2].
      * intros H2.
        now apply (cancellation_0_mul integer_order) in H2 as [H2 | H2].
      * intros H2.
        now apply (cancellation_0_mul integer_order) in H2 as [H2 | H2].
  - set (r := 1+(a+-(1)) * 3^-1).
    exists r.
    assert (1 < r) as H2.
    { rewrite <-(A3 1), (A1 0) at 1.
      apply O1, O2.
      - now rewrite <-lt_shift.
      - rewrite <-? IZQ_add.
        apply (inv_lt rational_field_order); simpl; auto using O0, zero_lt_1. }
    assert (0 < r) as H3 by eauto using lt_trans, zero_lt_1.
    pose proof H2 as H4.
    apply (ordered_fields.pow_gt_1 rational_field_order _ 2) in H4;
      auto using integers.O0, integers.zero_lt_1.
    rewrite (pow_add_r rationals) in H4; simpl in *; fold pow in *;
      auto using lt_neq.
    rewrite <-pow_mul_l, (pow_1_r rationals) in H4; auto using lt_neq.
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
        apply lt_cross_mul.
        + now rewrite <-lt_shift.
        + apply (inv_lt rational_field_order); simpl.
          rewrite <-? IZQ_add.
          auto using O0, zero_lt_1.
        + rewrite lt_shift in H6 |-*.
          replace (-(a+-(1))) with (-a+1) by ring.
          rewrite A1, <-A2.
          replace (1 + 1%Z) with (1%Z+1%Z) by auto.
          now rewrite IZQ_add, A1.
        + apply (inv_lt_1 rational_field_order); rewrite <-? IZQ_add; simpl.
          * auto using O0, zero_lt_1.
          * rewrite <-(A3 1), A1, <-A2 at 1.
            unfold IZQ, one.
            auto using O1, O0, zero_lt_1.
      - subst.
        rewrite <-IZQ_add, <-A2, A4, A1, A3, M3.
        apply (inv_lt_1 rational_field_order); rewrite <-? IZQ_add; simpl.
        + auto using O0, zero_lt_1.
        + rewrite <-(A3 1), A1, <-A2 at 1.
          unfold IZQ, one.
          auto using O1, O0, zero_lt_1. }
    apply (O3 (r+-(1))) in H7; try now rewrite <-lt_shift.
    unfold r in H7 at 3.
    rewrite <-A2, (A1 1), <-A2, ? (A1 _ 1), A4, (A1 _ 0), A3, <-M2, inv_l in H7.
    + rewrite (A1 1), <-H5, (M1 _ 1), M3, ? (A1 _ (-(1))) in H7.
      rewrite <-(A3 (r*r)), <-(A3 a), <-(A4 1), <-? A2.
      now apply O1.
    + contradict H0.
      now rewrite <-IZQ_eq.
Qed.
