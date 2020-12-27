Require Export arithmetic Field.

Definition ℤ0 := {z in ℤ × ℤ | (proj2 ℤ ℤ z) ≠ value ℤ 0}.

Definition rational_relation :=
  {z in ℤ0 × ℤ0 | ∃ a b c d : Z,
     b ≠ 0 ∧ d ≠ 0 ∧ z = ((value ℤ a, value ℤ b), (value ℤ c, value ℤ d)) ∧ 
     a * d = b * c}.

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
      exists (mkSet ℤ x0 H1), (mkSet ℤ x1 H2), (mkSet ℤ x0 H1), (mkSet ℤ x1 H2).
      simpl.
      repeat split; try ring; contradict H0; now rewrite <-H0.
    + contradiction n.
      apply Product_classification; eauto.
  - intros x y H H0 H1.
    rewrite Specify_classification in *.
    destruct H1 as [H1 [a [b [c [d [H2 [H3 [H4 H5]]]]]]]].
    split; try apply Product_classification; eauto.
    exists c, d, a ,b.
    repeat split; auto; try ring [H5].
    repeat rewrite Ordered_pair_iff in *.
    intuition.
  - intros x y z H H0 H1 H2 H3.
    rewrite Specify_classification in *.
    destruct H2 as [H2 [a [b [c [d [H4 [H5 [H6 H7]]]]]]]],
                   H3 as [H3 [a' [b' [c' [d' [H8 [H9 [H10 H11]]]]]]]].
    split; try apply Product_classification; eauto.
    exists a, b, c', d'.
    repeat split; auto; repeat rewrite Ordered_pair_iff in *; intuition;
      subst; rewrite Ordered_pair_iff in *; intuition.
    apply set_proj_injective in H10.
    apply set_proj_injective in H12.
    subst.
    apply (cancellation_mul_l b'); auto.
    ring [H7 H11].
Qed.

Definition ℚ := ℤ0 / rational_relation.

Definition Q := elts ℚ.

Delimit Scope Q_scope with Q.
Open Scope Q_scope.
Bind Scope Q_scope with Q.

Definition embed : Z → Z → Q.
Proof.
  intros a b.
  destruct (excluded_middle_informative (b = 0)).
  - assert (((value ℤ 0), (value ℤ 1)) ∈ ℤ0) as H.
    { apply Specify_classification.
      split.
      + apply Product_classification.
        eauto using in_set.
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
          apply Product_classification; eauto using in_set. }
    exact (quotient_map ℤ0 rational_relation
                        (mkSet ℤ0 (value ℤ 0, value ℤ 1) H)).
  - destruct a as [_ a' A], b as [_ b' B].
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
    exact (quotient_map ℤ0 rational_relation (mkSet ℤ0 (a', b') H)).
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
  exists (mkSet _ _ H0), (mkSet _ _ H4).
  set (a' := {| value := a; in_set := H0 |}).
  set (b' := {| value := b; in_set := H4 |}).
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
  rewrite quotient_image, H1.
  unfold embed; destruct excluded_middle_informative; simpl; intuition.
Qed.

Theorem Qequiv : ∀ a b c d, b ≠ 0 → d ≠ 0 → a / b = c / d ↔ a * d = b * c.
Proof.
  intros [_ a A] [_ b B] [_ c C] [_ d D] H H0.
  split; intros H1; unfold embed in *; destruct excluded_middle_informative;
    try (now contradiction); [symmetry in H1 | symmetry]; 
      destruct excluded_middle_informative; try (now contradiction);
        [apply quotient_wf in H1 | apply quotient_wf];
        auto using rational_equivalence; simpl in *.
  - apply Specify_classification in H1
      as [H1 [c' [d' [a' [b' [H2 [H3 [H4 H5]]]]]]]].
    repeat rewrite Ordered_pair_iff in *.
    intuition.
    subst.
    replace {| in_set := A |} with a'; replace {| in_set := B |} with b';
      replace {| in_set := C |} with c'; replace {| in_set := D |} with d';
        try (now apply set_proj_injective); ring [H5].
  - apply Specify_classification.
    split.
    + apply Product_classification.
      exists (c, d), (a, b).
      assert (∀ e f (F : f ∈ ℤ), e ∈ ℤ → {| in_set := F |} ≠ 0 → (e, f) ∈ ℤ0);
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
    + exists {| in_set := C |}, {| in_set := D |},
      {| in_set := A |}, {| in_set := B |}.
      repeat split; auto.
      ring [H1].
Qed.

Definition IZQ a := a / 1.
Definition zero := 0 / 1.
Definition one := 1 / 1.

Notation "0" := zero : Q_scope.
Notation "1" := one : Q_scope.

Coercion IZQ : Z >-> Q.

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
Notation "a '^-1' " := (inv a) (at level 35, format "a '^-1'") : Q_scope.

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
    intros H1; apply cancellation_0_mul in H1; tauto.
Qed.

Theorem mul_wf : ∀ a b c d : Z,
    b ≠ 0%Z → d ≠ 0%Z → (a / b) * (c / d) = (a * c) / (b * d).
Proof.
  intros a b c d H H0.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  rewrite Qequiv in *; auto; try ring [e1 e2];
    intros H1; apply cancellation_0_mul in H1; tauto.
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
  apply cancellation_0_mul in e0.
  tauto.
Qed.

Theorem A3 : ∀ x, 0 + x = x.
Proof.
  intros [_ x H].
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
  intros [_ a A] [_ b B].
  unfold add in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  rewrite Qequiv in *; auto;
    try (intros Z; apply cancellation_0_mul in Z; tauto).
  ring.
Qed.

Theorem A2 : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  intros [_ a A] [_ b B] [_ c C].
  unfold add in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4.
  rewrite Qequiv in *; auto;
    try (intros Z; apply cancellation_0_mul in Z; tauto).
  apply (cancellation_mul_r x3); auto.
  ring [e7 e8].
Qed.

Theorem M3 : ∀ x, 1 * x = x.
Proof.
  intros [_ x H].
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
  intros [_ a A] [_ b B].
  unfold mul in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  rewrite Qequiv in *; auto;
    try (intros Z; apply cancellation_0_mul in Z; tauto).
  ring.
Qed.

Theorem M2 : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  intros [_ a A] [_ b B] [_ c C].
  unfold mul in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4.
  rewrite Qequiv in *; auto;
    try (intros Z; apply cancellation_0_mul in Z; tauto).
  apply (cancellation_mul_r x3); auto.
  ring [e7 e8].
Qed.

Theorem D1 : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  intros [_ a A] [_ b B] [_ c C].
  unfold mul, add in *.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1, a2, a3, a4, a5.
  rewrite Qequiv in *; auto;
    try (intros Z; apply cancellation_0_mul in Z; tauto).
  apply (cancellation_mul_r x3); auto.
  apply (cancellation_mul_r x1); auto.
  ring_simplify.
  replace (x*x5*x8*x10*x3*x1)%Z with (x*(x1*x3)*x5*x8*x10)%Z by ring.
  replace (x8*x3*x1*x4*x6*x9)%Z with ((x9*(x3*x6)*x1*x4*x8))%Z by ring.
  replace (x10*x3*x1*x4*x6*x7)%Z with (x7*(x1*x6)*x3*x4*x10)%Z by ring.
  rewrite e7, e9, e10.
  ring.
Qed.

Theorem sub_neg : ∀ a b, a - b = a + -b.
Proof.
  auto.
Qed.

Theorem A4 : ∀ a, a + -a = 0.
Proof.
  intros [_ a A].
  unfold add, neg.
  repeat destruct constructive_indefinite_description.
  destruct a0, a1.
  unfold zero.
  rewrite Qequiv in *; eauto using zero_ne_1;
    try (intros Z; apply cancellation_0_mul in Z; tauto).
  ring [e2].
Qed.

Theorem one_ne_0 : 1 ≠ 0.
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
    apply zero_ne_1.
  - intros H0.
    apply cancellation_0_mul in H0.
    tauto.
  - apply zero_ne_1.
Qed.

Add Field rational_field :
  (mk_field div inv
            (mk_rt 0 1 add mul sub neg eq A3 A1 A2 M3 M1 M2 D1 sub_neg A4)
            one_ne_0 div_inv inv_l).

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
    destruct (T w 0), (T y 0); intuition; subst;
      auto using mul_neg_neg, mul_pos_pos.
    + assert (0 < x * y) by now apply mul_pos_pos.
      assert (z * w < 0) by now apply mul_pos_neg.
      rewrite H1 in *.
      exfalso; eapply lt_antisym; eauto.
    + replace (z*0)%Z with 0%Z in * by ring.
      apply cancellation_0_mul in H1 as [H1 | H1]; subst;
        exfalso; eauto using lt_irrefl.
    +  assert (x * y < 0) by now apply mul_pos_neg.
       assert (0 < z * w) by now apply mul_pos_pos.
       rewrite H1 in *.
       exfalso; eapply lt_antisym; eauto.
    + replace (z*0)%Z with 0%Z in * by ring.
      apply cancellation_0_mul in H1 as [H1 | H1]; subst;
        exfalso; eauto using lt_irrefl. }
  split; intros H0; unfold positive in *;
    repeat destruct constructive_indefinite_description;
    destruct a0; rewrite Qequiv in *; auto;
      assert (a * x0 = b * x)%Z as e1 by ring [e0];
      assert (-x * b = -x0 * a)%Z as e2 by ring [e0];
      assert (-a * x0 = -b * x)%Z as e3 by ring [e0];
      apply pos_mul in H0 as [[H0 H1] | [H0 H1]]; eauto.
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
  rewrite neg_wf, ? pos_wf, Qequiv; auto using zero_ne_1.
  replace (-a*b)%Z with (-(a*b))%Z by ring.
  rewrite <-lt_neg_0.
  replace (a * 1 = b * 0)%Z with (a * b = 0)%Z.
  - destruct (T (a*b) 0); intuition.
  - apply propositional_extensionality.
    replace (b*0)%Z with 0%Z by ring.
    rewrite integers.M3_r.
    split; intros H0; subst; try ring.
    now apply cancellation_0_mul in H0 as [H0 | H0].
Qed.

Definition lt : Q → Q → Prop.
Proof.
  intros x y.
  exact (positive (y-x)).
Defined.

Infix "<" := lt : Q_scope.

Notation "a > b" := (b < a) (only parsing) : Q_scope.

Definition le a b := a < b ∨ a = b.
Infix "≤" := le : Q_scope.
Notation "a ≥ b" := (b ≤ a) (only parsing) : Q_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level): Q_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level): Q_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level): Q_scope.

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
  rewrite <-H2, <-H4, add_wf, pos_wf in *; auto using ne0_cancellation.
  apply pos_mul in H as [[H H5] | [H H5]];
    apply pos_mul in H0 as [[H0 H6] | [H0 H6]];
    try rewrite lt_neg_0 in *;
    [ | replace ((a*d+c*b)*(b*d))%Z with ((a*-d+-c*b)*(b*-d))%Z by ring
      | replace ((a*d+c*b)*(b*d))%Z with ((-a*d+c*-b)*(-b*d))%Z by ring
      | replace ((a*d+c*b)*(b*d))%Z with ((-a*-d+-c*-b)*(-b*-d))%Z by ring ];
    apply mul_pos_pos; try apply integers.O0; now apply mul_pos_pos.
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
  rewrite mul_wf, pos_wf in *; auto using ne0_cancellation.
  replace (a*c*(b*d))%Z with ((a*b)*(c*d))%Z by ring.
  auto using mul_pos_pos.
Qed.

Theorem O3 : ∀ a b c, 0 < a → b < c → a * b < a * c.
Proof.
  intros a b c H H0.
  unfold lt in *.
  replace (a*c - a*b) with (a*(c-b) - 0) by ring.
  apply O2; auto.
  now replace (c-b) with (c-b-0) in H0 by ring.
Qed.

Theorem lt_irrefl : ∀ a, ¬ a < a.
Proof.
  intros a.
  pose proof (T a a).
  tauto.
Qed.

Theorem lt_antisym : ∀ a b, a < b → ¬ b < a.
Proof.
  intros a b H.
  pose proof (T a b).
  tauto.
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

Theorem lt_dense : ∀ a b, a < b → ∃ c, a < c ∧ c < b.
Proof.
  intros x y H.
  destruct (Qlift x) as [a [b [H0 H1]]], (Qlift y) as [c [d [H2 H3]]].
  exists ((b*c + a*d)/(2*b*d)).
  subst.
  assert (2 ≠ 0)%Z.
  { intros H1.
    contradiction (arithmetic.lt_irrefl 0).
    rewrite <-H1 at 2.
    eauto using integers.O0, zero_lt_1. }
  split; unfold lt, sub in *; rewrite neg_wf, add_wf, pos_wf in *;
    auto using ne0_cancellation.
  - replace (((b*c+a*d)*b+-a*(2*b*d))*(2*b*d*b))%Z
      with (2*(b*b)*((c*b+-a*d)*(d*b)))%Z by ring.
    eauto using mul_pos_pos, integers.O0, zero_lt_1, square_ne0.
  - replace ((c*(2*b*d)+-(b*c+a*d)*d)*(d*(2*b*d)))%Z
      with (2*(d*d)*((c*b+-a*d)*(d*b)))%Z by ring.
    eauto using mul_pos_pos, integers.O0, zero_lt_1, square_ne0.
Qed.

Theorem pos_denom : ∀ x, ∃ a b, (0 < b ∧ x = a / b)%Z.
Proof.
  intros x.
  destruct (Qlift x) as [a [b [H H0]]].
  destruct (integers.T b 0); intuition; eauto.
  exists (-a)%Z, (-b)%Z.
  rewrite <-lt_neg_0 in *.
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
  repeat split; auto using div_1_l; subst.
  - intros z [k H5] [l H6].
    subst.
    assert (z*d｜d) as [e H0] by
          (apply H4; rewrite <-integers.M2; auto using div_mul_l, div_refl).
    rewrite integers.M2, <-(integers.M3 d) in H0 at 1.
    apply cancellation_mul_r in H0; try now (exists e).
    now apply cancellation_ne0 in H.
  - rewrite Qequiv; auto; try ring.
    now apply cancellation_ne0 in H.
  - now apply cancellation_ne0 in H.
Qed.

Theorem Rudin_1_1 : ¬ ∃ p : Q, p * p = 2.
Proof.
  intros [p H].
  unfold IZQ in H.
  destruct (reduced_form p) as [m [n [H0 [H1 H2]]]].
  subst.
  rewrite mul_wf, Qequiv in H; auto using ne0_cancellation, zero_ne_1.
  rewrite (integers.M1 _ 1), integers.M3, (integers.M1 _ 2) in H.
  assert (2｜(m*m)) as H1 by (rewrite H; eauto using div_mul_r, div_refl).
  apply Euclid's_lemma in H1; auto using two_is_prime.
  assert (2｜m) as [k H3] by tauto.
  subst.
  replace (k*2*(k*2))%Z with (2*(2*k*k))%Z in H by ring.
  apply cancellation_mul_l in H.
  - assert (2｜(n*n)) as H3 by (rewrite <-H; eauto using div_mul_r, div_refl).
    apply Euclid's_lemma in H3; auto using two_is_prime.
    assert (2｜n) as [l H4] by tauto.
    subst.
    pose proof two_is_prime as [H4 H5].
    contradiction H4.
    destruct H0 as [H0 [H6 H7]].
    apply H7; auto using div_mul_l, div_refl.
  - intros H3.
    unfold integers.zero, integers.one in *.
    rewrite integers.add_wf, Zequiv, ? add_0_l, ? add_0_r, ? add_1_r in H3.
    now apply eq_sym, PA4 in H3.
Qed.
