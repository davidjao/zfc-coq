Set Warnings "-notation-overridden,-uniform-inheritance".
Set Warnings "-fragile-hint-constr,-ambiguous-paths".
Require Export naturals rings ordered_rings List Permutation.

Definition integer_relation := {z in (ω × ω) × (ω × ω) | ∃ a b c d : N,
                                  z = ((a, b), (c, d)) ∧ a + d = b + c}.

Theorem integer_equivalence : is_equivalence (ω × ω) integer_relation.
Proof.
  repeat split; unfold integer_relation in *.
  - intros a H.
    apply Specify_classification.
    split.
    + apply Product_classification; eauto.
    + apply Product_classification in H as [x [y [H [H0 H1]]]].
      exists (exist _ _ H : N), (exist _ _ H0 : N),
      (exist _ _ H : N), (exist _ _ H0 : N).
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
    destruct H2 as [H2 [a [b [c [d [H4 H5]]]]]], H3
        as [H3 [e [f [g [h [H6 H7]]]]]].
    split.
    + apply Product_classification; eauto.
    + exists a, b, g, h.
      split; rewrite Ordered_pair_iff in *; intuition.
      subst.
      rewrite Ordered_pair_iff in *; intuition.
      apply set_proj_injective in H6.
      apply set_proj_injective in H8.
      subst.
      apply (naturals.cancellation_add e).
      ring_simplify [H5 H7].
      rewrite H7, add_comm, add_assoc, H5.
      ring.
Qed.

Definition Zset := (ω × ω) / integer_relation.
Definition Z := (elts Zset).

Declare Scope Z_scope.
Delimit Scope Z_scope with Z.
Open Scope Z_scope.
Bind Scope Z_scope with Z.

Definition IZS (a : Z) := elt_to_set _ a : set.
Coercion IZS : Z >-> set.

Definition embed : N → N → Z.
Proof.
  intros [a A] [b B].
  assert ((a, b) ∈ ω × ω).
  { apply Product_classification.
    now exists a, b. }
  exact (quotient_map _ _ (exist _ _ H)).
Defined.

Infix "-" := embed : set_scope.

Theorem Zlift : ∀ z, ∃ a b, (a - b = z)%set.
Proof.
  intros z.
  destruct (quotient_lift _ _ z) as [y H].
  destruct (unique_set_element _ y) as [x [[H0 H1] H2]].
  apply Product_classification in H0 as [a [b [H3 [H4 H5]]]].
  exists (exist _ _ H3 : N), (exist _ _ H4 : N).
  apply set_proj_injective.
  simpl in *.
  now rewrite <-H, <-H5, H1, quotient_image.
Qed.

Theorem Zequiv : (∀ a b c d, a - b = c - d ↔ a + d = b + c)%set.
Proof.
  intros [a A] [b B] [c C] [d D].
  split; intros H; unfold embed in *.
  - apply quotient_equiv in H; auto using integer_equivalence.
    simpl in *.
    apply Specify_classification in H as [H [a0 [b0 [c0 [d0 [H0 H1]]]]]].
    rewrite ? Ordered_pair_iff in *; intuition; subst.
    destruct a0, b0, c0, d0.
    simpl in *.
    replace A with i; replace B with i0; replace C with i1;
      replace D with i2; auto using proof_irrelevance.
  - apply quotient_equiv; auto using integer_equivalence.
    simpl.
    apply Specify_classification; split.
    + apply Product_classification.
      exists (a,b), (c,d).
      repeat split; auto; apply Product_classification; eauto.
    + now exists (exist _ _ A : N), (exist _ _ B : N),
      (exist _ _ C : N), (exist _ _ D : N).
Qed.

Definition INZ a := (a - 0)%set.
Coercion INZ : N >-> Z.

Definition add : Z → Z → Z.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (Zlift x)) as [a H].
  destruct (constructive_indefinite_description _ H) as [b H0].
  destruct (constructive_indefinite_description _ (Zlift y)) as [c H1].
  destruct (constructive_indefinite_description _ H1) as [d H2].
  exact ((a + c) - (b + d))%set.
Defined.

Definition mul : Z → Z → Z.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (Zlift x)) as [m H].
  destruct (constructive_indefinite_description _ H) as [n H0].
  destruct (constructive_indefinite_description _ (Zlift y)) as [p H1].
  destruct (constructive_indefinite_description _ H1) as [q H2].
  exact ((m * p + n * q) - (n * p + m * q))%set.
Defined.

Definition neg : Z → Z.
Proof.
  intros x.
  destruct (constructive_indefinite_description _ (Zlift x)) as [a H].
  destruct (constructive_indefinite_description _ H) as [b H0].
  exact (b - a)%set.
Defined.

Definition zero := 0%N : Z.
Definition one := 1%N : Z.

Infix "+" := add : Z_scope.
Infix "*" := mul : Z_scope.
Notation "- a" := (neg a) : Z_scope.
Notation "0" := zero : Z_scope.
Notation "1" := one : Z_scope.
Notation "2" := (1+1) : Z_scope.
Notation "3" := (2+1) : Z_scope.
Notation "4" := (3+1) : Z_scope.

Theorem INZ_add : ∀ a b : N, a + b = (a + b)%N.
Proof.
  intros a b.
  unfold add, INZ.
  repeat destruct constructive_indefinite_description.
  rewrite Zequiv in *.
  ring [e0 e2].
Qed.

Theorem INZ_mul : ∀ a b : N, a * b = (a * b)%N.
Proof.
  intros a b.
  unfold mul, INZ.
  repeat destruct constructive_indefinite_description.
  rewrite Zequiv in *.
  ring [e0 e2].
Qed.

Theorem INZ_eq : ∀ a b : N, (a : Z) = (b : Z) ↔ a = b.
Proof.
  intros a b.
  split; intros H; try now subst.
  apply Zequiv in H.
  ring [H].
Qed.

Theorem add_wf : ∀ a b c d, ((a - b) + (c - d) = (a + c) - (b + d))%set.
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
  apply (naturals.cancellation_add x2).
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

Theorem neg_wf : ∀ a b, - (a - b)%set = (b - a)%set.
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

Theorem mul_wf : ∀ a b c d,
    ((a - b) * (c - d) = (a * c + b * d) - (b * c + a * d))%set.
Proof.
  intros a b c d.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  rewrite Zequiv in *.
  apply (naturals.cancellation_add (b*x1)).
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
  rewrite <-? mul_wf, e6, e8, ? mul_wf, Zequiv.
  ring.
Qed.

Theorem M3 : ∀ a, 1 * a = a.
Proof.
  intros [a H].
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
  rewrite <-mul_wf, <-add_wf, e4, e8, e10, add_wf, mul_wf, Zequiv.
  ring.
Qed.

Definition sub a b := (a + -b).
Infix "-" := sub : Z_scope.

Definition ℤ := mkRing _ zero one add mul neg A3 A1 A2 M3 M1 M2 D1 A4.

Add Ring integer_ring_raw : (ringify ℤ).
Add Ring integer_ring : (ringify ℤ : ring_theory 0 1 add mul sub neg eq).
Infix "^" := (rings.pow ℤ) : Z_scope.

Definition lt : Z → Z → Prop.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (Zlift x)) as [a H].
  destruct (constructive_indefinite_description _ H) as [b H0].
  destruct (constructive_indefinite_description _ (Zlift y)) as [c H1].
  destruct (constructive_indefinite_description _ H1) as [d H2].
  exact (a+d < b+c).
Defined.

Infix "<" := lt : Z_scope.

Theorem T : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ b < a) ∨
                   (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
                   (¬ a < b ∧ a ≠ b ∧ b < a).
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
        try rewrite add_wf, Zequiv in *.
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
    apply INZ_eq, eq_sym, naturals.cancellation_0_add in H3 as [H3 H4];
      subst; auto.
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
    apply INZ_eq, eq_sym, naturals.cancellation_0_mul in H3 as [H3 | H3];
      subst; auto.
  - subst.
    ring_simplify.
    auto using INZ_mul.
Qed.

Theorem zero_lt_1 : 0 < 1.
Proof.
  rewrite lt_def.
  exists 1%N.
  split.
  - intros H.
    replace 0 with (INZ 0) in *; auto.
    now apply INZ_eq, PA4 in H.
  - now ring_simplify.
Qed.

Theorem zero_ne_1 : 1 ≠ 0.
Proof.
  intros H.
  symmetry in H.
  pose proof zero_lt_1.
  pose proof (T 0 1).
  tauto.
Qed.

Definition ℤ_order := mkOR ℤ lt lt_trans T O1 O2 zero_ne_1.
Definition ℤ_ID := integral_domain ℤ_order.
Definition le := (le ℤ_order) : Z → Z → Prop.

Infix "≤" := le : Z_scope.
Notation "a > b" := (b < a) (only parsing) : Z_scope.
Notation "a ≥ b" := (b ≤ a) (only parsing) : Z_scope.
Notation "x < y < z" := (x < y ∧ y < z) : Z_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level): Z_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level): Z_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level): Z_scope.

Theorem le_def : ∀ a b, a ≤ b ↔ ∃ c : N, b = a + c.
Proof.
  split; intros H; unfold le, ordered_rings.le in *; rewrite lt_def in *.
  - destruct H as [[c [H H0]] | H]; eauto.
    subst.
    exists 0%N.
    now rewrite A1, A3.
  - destruct H as [c H].
    destruct (classic (0 = c)).
    + subst.
      right; now rewrite <-H0, A1, A3.
    + left; eauto.
Qed.

Theorem INZ_lt : ∀ a b : N, INZ a < INZ b ↔ (a < b)%N.
Proof.
  intros a b.
  split; intros H; rewrite lt_def, naturals.lt_def in *;
    destruct H as [c [H H0]]; exists c; split.
  - contradict H.
    now subst.
  - now rewrite INZ_add, INZ_eq in H0.
  - contradict H.
    now apply INZ_eq in H.
  - subst.
    auto using INZ_add.
Qed.

Theorem INZ_le : ∀ a b : N, INZ a ≤ INZ b ↔ (a ≤ b)%N.
Proof.
  intros a b.
  split; intros H.
  - apply le_def in H as [c H].
    exists c.
    rewrite INZ_add in H.
    now apply INZ_eq in H.
  - destruct H as [c H].
    apply le_def.
    exists c.
    rewrite INZ_add.
    now subst.
Qed.

Theorem lt_0_1 : ∀ a, 0 < a → ¬ a < 1.
Proof.
  intros a H H0.
  rewrite lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  contradiction (naturals.lt_0_1 x).
  split; rewrite naturals.lt_def.
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
      now rewrite <-INZ_eq, <-INZ_add.
Qed.

Theorem lt_n_Sn : ∀ x n, x < S n → x < n ∨ x = n.
Proof.
  intros x n H.
  destruct (T x n); intuition; try tauto.
  rewrite lt_def in *.
  destruct H as [a [H H2]], H3 as [b [H3 H4]].
  subst.
  rewrite ? INZ_add, INZ_eq, <-add_1_r, <-add_assoc in H2.
  apply naturals.cancellation_add, eq_sym, cancellation_1_add in H2
    as [H2 | H2]; subst; [ contradiction H3 | contradiction H ]; auto.
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
  - split; [ apply H |]; intros y [H3 H4]; contradiction (naturals.lt_irrefl 0);
      [ eapply INZ_lt, lt_trans | eapply naturals.lt_trans ]; eauto.
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

Definition divide := divide ℤ : Z → Z → Prop.

Notation "x ｜ y" := (divide x y) (at level 60, format "x '｜' y") : Z_scope.

Theorem N_ge_0 : ∀ a : N, 0 ≤ a.
Proof.
  induction a using Induction.
  - now right.
  - left.
    destruct IHa as [H | H]; rewrite <-add_1_r, <-INZ_add.
    + now apply succ_lt.
    + rewrite <-H, A3.
      now apply zero_lt_1.
Qed.

Theorem lt_0_le_1 : ∀ a, 0 < a ↔ 1 ≤ a.
Proof.
  intros a.
  destruct (T a 1); unfold le, ordered_rings.le in *; intuition; subst;
    eauto using zero_lt_1, (one_lt ℤ_order : ∀ a, 1 < a → 0 < a).
  exfalso; apply (lt_0_1 a); auto.
Qed.

Theorem div_le : ∀ a b, 0 < b → a｜b → a ≤ b.
Proof.
  intros a b H [d H0].
  destruct (T a b); unfold le, ordered_rings.le; intuition; subst; simpl in *.
  assert (0 < a) by eauto using lt_trans.
  eapply (pos_div_r ℤ_order), lt_0_le_1, mul_le_r in H;
    try rewrite M3 in H; eauto.
Qed.

Definition assoc := assoc ℤ : Z → Z → Prop.
Infix "~" := assoc (at level 70) : Z_scope.
Definition unit := unit ℤ : Z → Prop.

Definition pm a b := (a = b ∨ a = -b).
Notation " a = ± b " := (pm a b) (at level 60) : Z_scope.
Global Hint Unfold assoc unit pm : Z.

Theorem assoc_N : ∀ a b : N, a ~ b → a = b.
Proof.
  intros a b [H H0]; apply INZ_eq; fold divide in *.
  destruct (N_ge_0 a), (N_ge_0 b); simpl in *; try rewrite <-H1 in *;
    try rewrite <-H2 in *; try rewrite (div_0_l ℤ) in *; auto;
      apply (le_antisymm ℤ_order); now apply div_le.
Qed.

Theorem assoc_pos : ∀ a b, 0 < a → 0 < b → a ~ b → a = b.
Proof.
  intros a b H H0 H1.
  rewrite lt_def in H, H0.
  destruct H as [c [H H2]], H0 as [d [H0 H3]].
  subst.
  rewrite ? A3 in *.
  now apply INZ_eq, assoc_N.
Qed.

Theorem assoc_unit : ∀ a b, a ~ b → ∃ u, unit u ∧ b = a * u.
Proof.
  intros a b [[c H] [d H0]];
    destruct (classic (b = 0)); simpl in *; subst.
  - exists 1.
    split; auto using (one_unit ℤ) with Z.
    rewrite H0, H1.
    ring.
  - exists c.
    split; try ring.
    exists d; simpl.
    apply (cancellation_mul_r ℤ_ID a); simpl.
    + contradict H1; subst; ring.
    + now rewrite M3, <-M2.
Qed.

Theorem assoc_pm : ∀ a b, a ~ b → a = ± b.
Proof.
  intros a b H.
  destruct (T a 0), (T b 0); intuition; rewrite (lt_neg_0 ℤ_order) in *;
    subst; try (now (destruct H; rewrite (div_0_l ℤ) in *; intuition));
      [ assert (-a = -b → a = b) by (intro M; ring [M]); left |
        assert (-a = b → a = -b) by (intro M; ring [M]); right | right | left ];
      eauto 8 using assoc_pos, (assoc_sign ℤ),
      (assoc_sym ℤ), (assoc_sign ℤ) with Z.
Qed.

Theorem unit_pm_1 : ∀ a, unit a → a = ± 1.
Proof.
  intros a H.
  apply assoc_pm; split; auto using (div_1_l ℤ) with Z.
Qed.

Theorem pm_refl : ∀ a, a = ± a.
Proof.
  intros a.
  now left.
Qed.

Theorem pm_sym : ∀ a b, a = ± b → b = ± a.
Proof.
  intros a b [H | H].
  - now left.
  - right.
    ring [H].
Qed.

Theorem pm_trans : ∀ a b c, a = ± b → b = ± c → a = ± c.
Proof.
  intros a b c [H | H] [H0 | H0]; subst; intuition.
  left.
  ring.
Qed.

Add Parametric Relation : Z pm
      reflexivity proved by (pm_refl)
      symmetry proved by (pm_sym)
      transitivity proved by (pm_trans) as pm_equivalence.

Theorem division_algorithm_N : ∀ a b,
    0 < a → 0 < b → ∃ q r, b * q + r = a ∧ 0 ≤ r < b.
Proof.
  intros a b H H0.
  induction a as [a IHa] using strong_induction.
  destruct (T a b); unfold le, ordered_rings.le; intuition;
    [ exists 0, a | exists 1, 0 | ];
    repeat split; auto; subst; try ring.
  assert (0 < a + -b) as H3
      by (rewrite <-(A4 a); now apply O1, (neg_neg_lt ℤ_order)).
  destruct (IHa (a + -b)) as [q [r [H5 H6]]]; repeat split; auto.
  - rewrite <-(A3_r ℤ a) at 2.
    now apply O1, (neg_lt_0 ℤ_order).
  - exists (q+1), r.
    split; auto.
    rewrite (D1_l ℤ), <-A2, (A1 _ r), A2; simpl.
    rewrite H5; ring.
Qed.

Theorem division_algorithm : ∀ a b, 0 < b → ∃ q r, b * q + r = a ∧ 0 ≤ r < b.
Proof.
  intros a b H.
  destruct (T a 0) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]];
    auto using division_algorithm_N.
  - rewrite (lt_neg_0 ℤ_order) in H0; simpl in *.
    destruct (division_algorithm_N (-a) b) as [q [r [H3 [[H4 | H4] H5]]]]; auto.
    + exists (-q-1), (b+-r).
      repeat split.
      * replace a with (--a); try ring; rewrite <-H3; ring.
      * rewrite <-(A4 r), ? (A1 _ (-r)).
        now apply or_introl, O1.
      * rewrite A1, <-(A3_r ℤ b), A1, <-A2.
        apply O1.
        now rewrite A3, <-(neg_lt_0 ℤ_order).
    + exists (-q), 0.
      subst.
      repeat split; auto using (le_refl ℤ_order : ∀ a : Z, a ≤ a).
      replace a with (--a); try ring; rewrite <-H3; ring.
  - exists 0, 0.
    subst; repeat split;
      auto using (le_refl ℤ_order : ∀ a : Z, a ≤ a); ring.
Qed.

Definition gcd a b d := d｜a ∧ d｜b ∧ ∀ x, x｜a → x｜b → x｜d.

Notation "'gcd' ( a , b )  = d" := (gcd a b d) (at level 80).

Global Hint Resolve (div_add ℤ : ∀ a b c, a｜b → a｜c → a｜b+c)
       (div_1_l ℤ : ∀ a, 1｜a) (div_refl ℤ : ∀ a, a｜a) (div_0_r ℤ : ∀ a, a｜0)
       (div_mul_l ℤ : ∀ a b c, a｜c → a｜b * c)
       (div_mul_r ℤ : ∀ a b c, a｜b → a｜b * c)
      (div_sign_neg_r ℤ : ∀ a b, a｜-b → a｜b)
      (div_sign_l_neg ℤ : ∀ a b, a｜b → -a｜b)
      (div_trans ℤ : ∀ a b c, a｜b → b｜c → a｜c)
      (mul_pos_pos ℤ_order : ∀ a b, 0 < a → 0 < b → 0 < a * b)
      (O0 ℤ_order : ∀ a b, 0 < a → 0 < b → 0 < a + b)
      (square_ne0 ℤ_order : ∀ a : Z, a ≠ 0 → 0 < a * a) : Z.

Theorem Euclidean_algorithm_N :
  ∀ a b, 0 < a → 0 < b → gcd (a,b) = 1 → ∃ x y, 1 = a * x + b * y.
Proof.
  intros a b H; revert b.
  induction a as [a IHa] using strong_induction.
  intros b H0 [H1 [H2 H3]].
  destruct (division_algorithm b a) as [q [r [H4 [[H5 | H5] H6]]]]; subst; auto.
  - destruct (IHa r (conj H5 H6) H5 a) as [x [y H4]]; repeat split;
      auto using (div_mul_r ℤ) with Z.
    exists (y+-(q*x)), x.
    rewrite H4.
    ring.
  - exists 1, 0.
    ring_simplify.
    apply assoc_pos; auto using zero_lt_1.
    split; fold divide;
      auto using (div_mul_r ℤ), (div_add ℤ), (div_0_r ℤ),
      (div_mul_r ℤ), (div_refl ℤ) with Z.
Qed.

Lemma gcd_0_l : ∀ a d, gcd (0,a) = d → a ~ d.
Proof.
  intros a d [H [H0 H1]].
  split; fold divide; auto using (div_0_r ℤ), (div_refl ℤ) with Z.
Qed.

Lemma gcd_sym : ∀ a b d, gcd (a,b) = d → gcd(b,a) = d.
Proof.
  intros a b d [H [H0 H1]].
  repeat split; auto.
Qed.

Lemma gcd_0_r : ∀ a d, gcd (a,0) = d → a ~ d.
Proof.
  intros a d H.
  auto using gcd_0_l, gcd_sym.
Qed.

Lemma gcd_1_l : ∀ a, gcd (1,a) = 1.
Proof.
  intros a.
  repeat split; auto using (div_1_l ℤ) with Z.
Qed.

Lemma gcd_1_r : ∀ a, gcd (a,1) = 1.
Proof.
  intros a.
  repeat split; auto using (div_1_l ℤ) with Z.
Qed.

Lemma gcd_neg : ∀ a b d, gcd (a,b) = d ↔ gcd(a,-b) = d.
Proof.
  intros a b d.
  split; intros [H [H0 H1]].
  - repeat split; try rewrite <-(div_sign_r ℤ); auto.
    intros x H2 H3.
    rewrite <-(div_sign_r ℤ) in *.
    auto.
  - repeat split; try rewrite <-(div_sign_r ℤ) in H0; auto.
    intros x H2 H3.
    rewrite (div_sign_r ℤ) in H3.
    auto.
Qed.

Theorem Euclidean_algorithm :
  ∀ a b, gcd (a,b) = 1 → ∃ x y, 1 = a * x + b * y.
Proof.
  intros a b H.
  destruct (T a 0), (T b 0); intuition; subst;
    try apply gcd_0_l in H; try apply gcd_0_r in H;
      try (now (destruct H as [[x H]]; exists x, 0;
                simpl in *; fold Z in x; rewrite H; ring));
      try (now (destruct H as [[x H]]; exists 0, x;
                simpl in *; fold Z in x; rewrite H; ring));
      destruct H; intuition; rewrite (lt_neg_0 ℤ_order) in *; simpl in *;
        [ set (c := -a) | set (c := -a) | set (c := a) | set (c := a) ];
        [ set (d := -b) | set (d := b) | set (d := -b) | set (d := b) ];
        destruct (Euclidean_algorithm_N c d) as [x [y Z]]; try split;
          auto using (div_1_l ℤ), (div_sign_neg_r ℤ) with Z;
          unfold c, d in *;
          [ exists (-x), (-y) | exists (-x), y | exists x, (-y) | exists x, y ];
          rewrite Z; ring.
Qed.

Theorem FTA : ∀ a b c, gcd (a, b) = 1 → a｜b * c → a｜c.
Proof.
  intros a b c H [d H0]; simpl in *; fold Z in *.
  destruct (Euclidean_algorithm a b H) as [x [y H1]].
  rewrite <-(M3 c), H1.
  exists (c*x + d*y); simpl.
  now ring_simplify [H0].
Qed.

Definition prime p := ¬ unit p ∧ ∀ d : Z, d｜p → unit d ∨ d ~ p.

Fixpoint product L :=
  match L with
    | nil => 1
    | p :: L => p * product L
  end.

Notation "∏ L" := (product L) (at level 50) : Z_scope.

Definition prime_factorization n L :=
  n = ∏ L ∧ (∀ p, List.In p L → 0 < p ∧ prime p).

Notation "n = ∏' L" := (prime_factorization n L) (at level 50) : Z_scope.

Lemma prod_lemma : ∀ t1 t2 p,
    ∏ (t1 ++ p :: t2) = p * (∏ (t1 ++ t2)).

Proof.
  induction t1 as [| a t1 IHt1]; auto.
  intros t2 p.
  simpl.
  rewrite IHt1.
  ring.
Qed.

Theorem not_prime_divide :
  ∀ p, 1 < p → ¬ prime p → ∃ n, 1 < n < p ∧ n｜p.
Proof.
  intros p H H0.
  pose proof (T p 1) as H1.
  apply NNPP; contradict H0.
  split; eauto.
  - intros H2.
    apply div_le in H2 as [H2 | H2]; auto using zero_lt_1; intuition.
  - intros d H2.
    apply NNPP; contradict H0;
      destruct (T d 0) as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H5 [H4 H3]]]];
      rewrite (lt_neg_0 ℤ_order) in *;
      try (now (subst; apply (div_0_l ℤ) in H2; subst;
                contradiction (lt_irrefl ℤ_order 0);
                eapply lt_trans; eauto using zero_lt_1));
      [ exists (-d) | exists d ]; repeat split;
        auto using (div_sign_l_neg ℤ) with Z.
    * apply lt_0_le_1 in H3 as [H3 | H3]; simpl in *; auto.
      contradict H0.
      symmetry in H3.
      replace d with (- (1)) by (rewrite <-H3; ring).
      eauto using (unit_sign_r ℤ), (one_unit ℤ) with Z.
    * apply div_sign_l_neg, div_le in H2 as [H2 | H2];
        eauto using lt_trans, zero_lt_1; simpl in *.
      contradict H0.
      rewrite <-H2.
      auto using (assoc_sign ℤ), (assoc_refl ℤ) with Z.
    * apply lt_0_le_1 in H3 as [H3 | H3]; auto; simpl in *.
      contradict H0.
      rewrite <-H3.
      eauto using (one_unit ℤ) with Z.
    * apply div_le in H2 as [H2 | H2];
        eauto using lt_trans, zero_lt_1.
      contradict H0.
      rewrite H2.
      eauto using (assoc_refl ℤ) with Z.
Qed.

Theorem exists_prime_divisor :
  ∀ n, 1 < n → ∃ p, 0 < p ∧ prime p ∧ p｜n.
Proof.
  intros n H.
  induction n as [n H0] using strong_induction.
  destruct (classic (prime n)) as [H1 | H1].
  - exists n; split;
      eauto using (div_refl ℤ), lt_trans, zero_lt_1 with Z.
  - destruct (not_prime_divide n H H1) as [x [[H2 H3] H4]].
    apply H0 in H2 as [p [H5 [H6 H7]]];
      eauto 6 using (div_trans ℤ), lt_trans, zero_lt_1 with Z.
Qed.

Lemma prime_factors_in_interval :
  ∀ p x, 0 < p → 0 < x → prime p → p｜x → ∃ k, k * p = x ∧ 0 < k < x.
Proof.
  intros p x H H0 [H1 H2] [k H3].
  subst.
  assert (0 < k) as H4 by (eapply (pos_div_r ℤ_order) in H0; eauto).
  exists k.
  repeat split; auto.
  assert (k ≤ k * p) as [H3 | H3];
    eauto using div_le, (div_mul_r ℤ), (div_refl ℤ) with Z.
  rewrite <-(M3_r _ k) in H3 at 1.
  apply (cancellation_mul_l ℤ_ID) in H3.
  - contradict H1; subst; eauto using (one_unit ℤ) with Z.
  - intro; subst; contradiction (lt_irrefl ℤ_order 0).
Qed.

Theorem exists_prime_factorization : ∀ n, 0 < n → ∃ L : list Z, n = ∏' L.
Proof.
  intros n H.
  induction n as [n H0] using strong_induction.
  destruct (T 1 n) as [[H1 [H2 H3]] | [[H1 [H2 H3]] | [H1 [H2 H3]]]].
  - apply exists_prime_divisor in H1 as [p [H4 [H5 H6]]].
    apply prime_factors_in_interval in H6 as [k [H6 H7]]; auto.
    apply H0 in H7 as [L [H7 H8]]; intuition.
    exists (p::L).
    split; auto; simpl.
    + now rewrite <-H6, H7, M1.
    + intros p0 [H1 | H1]; subst; auto.
  - now (exists nil).
  - contradiction (lt_0_1 n).
Qed.

Lemma prime_rel_prime : ∀ p a, prime p → ¬ p｜a → gcd (p,a) = 1.
Proof.
  intros p a H H0.
  repeat split; auto using (div_1_l ℤ) with Z.
  intros d H1 H2.
  apply H in H1 as [H1 | [H1 H3]]; auto.
  exfalso; eauto using (div_trans ℤ) with Z.
Qed.

Theorem Euclid's_lemma : ∀ a b p, prime p → p｜a * b → p｜a ∨ p｜b.
Proof.
  intros a b p H H0.
  destruct (classic (p｜a)); eauto using prime_rel_prime, FTA.
Qed.

Theorem divisors_are_factors :
  ∀ L p x, 0 < p → 0 < x → x = ∏' L → prime p → p｜x → In p L.
Proof.
  intro L.
  induction L as [| a L IHL]; intros p x H H0 [H1 H2] [H3 H4] H5;
    subst; try now contradict H3.
  destruct (H2 a (in_eq a L)) as [H1 [H6 H7]].
  destruct (Euclid's_lemma a (∏ L) p) as [H8 | H8]; repeat split; auto.
  - apply H7 in H8 as [H8 | H8]; try contradiction.
    apply assoc_pm in H8 as [H8 | H8]; subst; try now left.
    rewrite <-(lt_neg_0 ℤ_order) in H.
    contradiction (lt_antisym ℤ_order 0 a).
  - assert (0 < (∏ L)) as H9 by (eapply (pos_div_l ℤ_order) in H0; eauto).
    apply in_cons.
    eapply IHL; unfold prime; try split; eauto using in_cons.
Qed.

Lemma one_has_unique_factorization : ∀ L, 1 = ∏' L → L = nil.
Proof.
  intros L [H H0].
  induction L as [| a L IHL]; auto.
  destruct (H0 a) as [H1 [H2 H3]]; try now intuition.
  contradict H2.
  exists (∏ L).
  now rewrite M1.
Qed.

Theorem unique_prime_factorization :
  ∀ x, 0 < x → ∀ L1 L2 : list Z, x = ∏' L1 → x = ∏' L2 → Permutation L1 L2.
Proof.
  intros x H.
  induction x as [x H0] using strong_induction.
  intros L1 L2 [H1 H2] [H3 H4].
  induction L1 as [ | q L1 IHL1]; simpl in *.
  - subst.
    now rewrite (one_has_unique_factorization _ (conj H3 H4)).
  - destruct (H2 q) as [H5 H6]; try apply in_eq.
    assert (q｜x) as H7 by
          (subst; eauto using (div_mul_r ℤ), (div_refl ℤ) with Z).
    eapply divisors_are_factors in H as H8; eauto; try (split; eauto).
    apply in_split in H8 as [l1 [l2 H8]].
    subst.
    apply prime_factors_in_interval in H7 as [k [H8 H9]]; auto.
    rewrite (M1 k), <-H8, prod_lemma in *.
    apply (cancellation_mul_l ℤ_ID) in H3;
      apply (cancellation_mul_l ℤ_ID) in H8;
      try now (intro; subst; contradiction (lt_irrefl ℤ_order 0)).
    apply Permutation_cons_app, (H0 k); intuition; split; auto.
    intros p H9.
    apply H4.
    rewrite in_app_iff in *.
    intuition.
Qed.

Theorem WOP : ∀ S : Z → Prop,
    (∀ x, S x → 0 < x) → (∃ x, 0 < x ∧ S x) → ∃ s, S s ∧ ∀ t, S t → s ≤ t.
Proof.
  intros S H [s [H0 H1]].
  apply NNPP.
  intros H2.
  revert s H0 H1.
  induction s as [s IHs] using strong_induction.
  intros H3 H4.
  contradict H2.
  exists s.
  split; auto.
  intros t H0.
  unfold le, ordered_rings.le.
  destruct (T s t) as [H1 | [H1 | [H1 [H2 H5]]]]; try tauto.
  contradiction (IHs t); auto.
Qed.

Theorem common_factor_N : ∀ a b, 0 < a → 0 < b → ∃ d, 0 < d ∧ gcd (a,b) = d.
Proof.
  intros a b H H0.
  destruct (WOP (λ z, 0 < z ∧ ∃ x y, z = a*x + b*y))
    as [d [[H1 [x [y H2]]] H3]]; try tauto.
  - exists b.
    repeat split; auto.
    exists 0, 1.
    ring.
  - exists d.
    repeat split; auto.
    + destruct (division_algorithm a d) as [q [r [H4 [[H5 | H5] H6]]]]; auto.
      replace a with (d*q + (a - d*q)) in H4 by ring.
      apply (cancellation_add ℤ) in H4.
      * destruct (H3 r); auto.
        -- split; auto.
           exists (1-x*q), (-y*q).
           rewrite H4, H2.
           ring.
        -- contradiction (lt_antisym ℤ_order d r).
        -- rewrite H7 in *.
           contradiction (lt_irrefl ℤ_order r).
      * rewrite <-H5 in *.
        exists q; simpl.
        rewrite <-H4.
        now ring_simplify.
    + destruct (division_algorithm b d) as [q [r [H4 [[H5 | H5] H6]]]]; auto.
      replace b with (d*q + (b - d*q)) in H4 by ring.
      apply (cancellation_add ℤ) in H4.
      * destruct (H3 r); auto.
        -- split; auto.
           exists (-x*q), (1-y*q).
           rewrite H4, H2.
           ring.
        -- contradiction (lt_antisym ℤ_order d r).
        -- rewrite H7 in *.
           contradiction (lt_irrefl ℤ_order r).
      * rewrite <-H5 in *.
        exists q; simpl.
        rewrite <-H4.
        now ring_simplify.
    + intros z H4 H5.
      subst.
      now apply div_mul_add.
Qed.

Theorem common_factor : ∀ a b, b ≠ 0 → ∃ d, 0 < d ∧ gcd (a,b) = d.
Proof.
  intros a b H.
  destruct (T a 0), (T b 0); intuition; rewrite (lt_neg_0 ℤ_order) in *.
  - destruct (common_factor_N (-a) (-b)) as [d [D1 D2]]; auto.
    exists d.
    split; auto.
    now apply gcd_neg, gcd_sym, gcd_neg, gcd_sym.
  - destruct (common_factor_N (-a) b) as [d [D1 D2]]; auto.
    exists d.
    split; auto.
    now apply gcd_sym, gcd_neg, gcd_sym.
  - exists (-b).
    repeat split; subst; auto using (div_0_r ℤ) with Z.
    + rewrite <-(div_sign_l ℤ).
      auto using (div_refl ℤ) with Z.
    + intros x H3 H5.
      now rewrite <-(div_sign_r ℤ).
  - destruct (common_factor_N a (-b)) as [d [D1 D2]]; auto.
    exists d.
    split; auto.
    now apply gcd_neg.
  - exists b.
    repeat split; subst;
      auto using (div_0_r ℤ), (div_refl ℤ) with Z.
  - destruct (common_factor_N a b) as [d [D1 D2]]; eauto.
Qed.

Theorem two_is_prime : prime 2.
Proof.
  split.
  - intros H.
    apply div_le in H as [H | H]; auto using zero_lt_1; simpl in *.
    + rewrite lt_def in H.
      destruct H as [c [H H0]].
      unfold one, INZ in H0.
      rewrite A1, A2, ? add_wf, Zequiv, ? add_0_r, ? add_0_l, ? add_1_r in H0.
      now apply PA5, PA4 in H0.
    + unfold one, INZ in H.
      rewrite ? add_wf, Zequiv, ? add_0_r, add_0_l, add_1_r in H.
      now apply PA5, eq_sym, PA4 in H.
  - assert (∀ d : Z, 0 < d → d｜2 → unit d ∨ d ~ 2) as H.
    { intros d H H0.
      apply div_le in H0 as [H0 | H0].
      - apply lt_0_le_1 in H as [H | H].
        + contradiction (lt_0_1 (d+-(1))).
          * rewrite <-(A4 1), ? (A1 _ (-(1))).
            now apply O1.
          * rewrite <-(A3_r ℤ 1) at 2; simpl.
            rewrite <-(A4 1), A2, ? (A1 _ (-(1))).
            now apply O1.
        + subst.
          left.
          now apply div_refl.
      - subst.
        auto using (assoc_refl ℤ) with Z.
      - eapply lt_trans; try exact zero_lt_1.
        rewrite <-(A3_r ℤ 1) at 1.
        eauto using O1, zero_lt_1. }
    intros d H0.
    destruct (T d 0) as [[H1 [H2 H3]] | [[H1 [H2 H3]] | [H1 [H2 H3]]]]; auto.
    + destruct (H (-d)); auto using (div_sign_l_neg ℤ) with Z.
      * now rewrite <-(lt_neg_0 ℤ_order).
      * now apply or_introl, unit_sign.
      * replace d with (--d) by ring.
        now apply or_intror, assoc_sym, assoc_sign, assoc_sym.
    + subst.
      apply div_0_l, eq_sym in H0; simpl in *.
      unfold zero, one in *.
      rewrite INZ_add, add_1_r in H0.
      now apply INZ_eq, PA4 in H0.
Qed.

Theorem INZ_sub : ∀ a b : N, b ≤ a → a - b = (a - b)%N.
Proof.
  intros a b H.
  unfold sub.
  replace (a : Z) with ((a-b)%N + b); try ring.
  rewrite INZ_add.
  f_equal.
  apply INZ_le in H.
  now rewrite add_comm, sub_abab.
Qed.

Section IZR.

  Variable Ring : rings.ring.
  Notation R := (elts (Rset Ring)).
  Add Ring generic_ring : (ringify Ring).

  Definition IZR : Z → R.
  Proof.
    intros x.
    destruct (excluded_middle_informative (0 ≤ x)).
    - apply le_def in l.
      destruct (constructive_indefinite_description _ l) as [c H].
      exact (INR _ c).
    - apply lt_not_ge, lt_shift in n.
      simpl in n.
      rewrite A3 in n.
      apply lt_def in n.
      destruct (constructive_indefinite_description _ n) as [c H].
      exact (rings.neg _ (INR _ c)).
  Defined.

  Coercion IZR : Z >-> R.

  Theorem IZR_INZ : ∀ n : N, INR _ n = (n : Z).
  Proof.
    intros n.
    unfold IZR.
    destruct excluded_middle_informative;
      destruct constructive_indefinite_description.
    - ring_simplify in e.
      apply INZ_eq in e.
      congruence.
    - contradict n0.
      apply INZ_le, zero_le.
  Qed.

  Theorem IZR_zero : rings.zero _ = 0.
  Proof.
    unfold IZR.
    destruct excluded_middle_informative, constructive_indefinite_description.
    - rewrite A3 in e.
      apply INZ_eq in e.
      subst.
      now rewrite INR_zero.
    - contradict n.
      apply le_refl.
  Qed.

  Theorem IZR_one : rings.one _ = 1.
  Proof.
    unfold IZR.
    destruct excluded_middle_informative, constructive_indefinite_description.
    - rewrite A3 in e.
      apply INZ_eq in e.
      subst.
      now rewrite INR_one.
    - contradict n.
      apply or_introl, zero_lt_1.
  Qed.

  Theorem IZR_add : ∀ a b : Z, rings.add _ a b = a + b.
  Proof.
    intros a b.
    unfold IZR.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description; rewrite A3 in *;
        repeat destruct a0; repeat destruct a1; repeat destruct a2.
    - subst.
      rewrite INR_add, INZ_add in *.
      now apply f_equal, INZ_eq.
    - contradict n.
      rewrite <-(A3 0).
      now apply le_cross_add.
    - replace (INR _ x) with (rings.add Ring (INR _ x0) (INR _ x1)); try ring.
      rewrite ? INR_add.
      f_equal.
      rewrite <-INZ_eq, <-INZ_add, <-e0, <-e, <-H0 in *.
      ring.
    - replace (INR _ x0) with (rings.add Ring (INR _ x) (INR _ x1)); try ring.
      rewrite ? INR_add.
      f_equal.
      rewrite <-INZ_eq, <-INZ_add, <-e, <-H0, <-H2.
      ring.
    - replace (INR _ x0) with (rings.add Ring (INR _ x) (INR _ x1)); try ring.
      rewrite ? INR_add.
      f_equal.
      rewrite <-INZ_eq, <-INZ_add, <-H0, <-e, <-e0.
      ring.
    - replace (INR _ x) with (rings.add Ring (INR _ x0) (INR _ x1)); try ring.
      rewrite ? INR_add.
      f_equal.
      rewrite <-INZ_eq, <-INZ_add, <-H0, <-e, <-H2.
      ring.
    - rewrite <-(ordered_rings.lt_not_ge ℤ_order) in n, n0; simpl in *.
      apply le_not_gt in l; simpl in *.
      contradict l.
      rewrite <-(A3 0).
      now apply (lt_cross_add ℤ_order).
    - replace (INR _ x1) with (rings.add Ring (INR _ x) (INR _ x0)); try ring.
      rewrite ? INR_add.
      f_equal.
      rewrite <-INZ_eq, <-INZ_add, <-H0, <-H2, <-H4.
      ring.
  Qed.

  Theorem IZR_mul : ∀ a b : Z, rings.mul _ a b = a * b.
  Proof.
    intros a b.
    unfold IZR.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description; rewrite A3 in *;
        repeat destruct a0; repeat destruct a1; repeat destruct a2.
    - subst.
      rewrite INR_mul, INZ_mul in *.
      now apply f_equal, INZ_eq.
    - contradict n.
      now apply mul_nonneg_nonneg.
    - apply lt_not_ge in n; simpl in *.
      apply le_not_gt in l0; simpl in *.
      destruct l as [l | l]; simpl in *.
      + contradict l0.
        now apply (mul_pos_neg ℤ_order).
      + subst.
        rewrite (rings.mul_0_l ℤ) in e0; simpl in *.
        rewrite ? IZR_INZ, <-e, <-e0, <-IZR_zero.
        ring.
    - rewrite <-mul_neg_1_l, rings.M1, <-rings.M2, mul_neg_1_l, INR_mul.
      apply f_equal, f_equal, INZ_eq.
      rewrite <-INZ_mul, <-e, <-H0, <-H2.
      ring.
    - apply lt_not_ge in n; simpl in *.
      apply le_not_gt in l0; simpl in *.
      destruct l as [l | l]; simpl in *.
      + contradict l0.
        now apply (mul_neg_pos ℤ_order).
      + subst.
        rewrite (rings.mul_0_r ℤ) in e0; simpl in *.
        rewrite ? IZR_INZ, <-e, <-e0, <-IZR_zero.
        ring.
    - rewrite <-mul_neg_1_l, <-rings.M2, mul_neg_1_l, INR_mul.
      apply f_equal, f_equal, INZ_eq.
      rewrite <-INZ_mul, <-e, <-H0, <-H2.
      ring.
    - rewrite rings.mul_neg_neg, INR_mul.
      apply f_equal, INZ_eq.
      rewrite <-INZ_mul, <-H0, <-H2, <-e.
      ring.
    - contradict n1.
      left; simpl.
      apply (ordered_rings.mul_neg_neg ℤ_order); now rewrite lt_not_ge.
  Qed.

  Theorem IZR_neg : ∀ a : Z, rings.neg _ a = -a.
  Proof.
    intros a.
    unfold IZR.
    repeat destruct excluded_middle_informative,
    constructive_indefinite_description.
    - destruct l as [l | l], l0 as [l0 | l0]; subst; simpl in *.
      + ring_simplify in e0.
        apply (lt_neg_0 ℤ_order) in l0; simpl in *.
        contradiction (lt_antisym ℤ_order 0 (0 + INZ x)).
      + apply (lt_not_ge ℤ_order) in l.
        contradict l.
        right.
        now rewrite l0, A3, A1, A4 at 1.
      + contradiction (lt_irrefl ℤ_order 0).
        now replace 0 with (-0) at 2 by ring.
      + rewrite A3 in *.
        replace (-0) with 0 in * by ring.
        rewrite ? IZR_INZ, <-e, <-e0, <-IZR_zero.
        ring.
    - destruct a0 as [H H0].
      replace (--a) with a in * by ring.
      now rewrite A3, ? IZR_INZ, <-e, <-H0 in *.
    - destruct a0 as [H H0].
      rewrite A3, ? IZR_INZ, <-e, <-H0 in *.
      ring.
    - contradict n0.
      left; simpl.
      now apply (lt_neg_0 ℤ_order), (lt_not_ge ℤ_order).
  Qed.

End IZR.

Theorem INZ_pow : ∀ a b : N, ((a : Z)^b) = ((a^b)%N : Z).
Proof.
  intros a b.
  induction b using Induction.
  - now rewrite pow_0_r, naturals.pow_0_r.
  - now rewrite pow_succ_r, naturals.pow_succ_r, IHb, INZ_mul.
Qed.

Theorem INZ_sum_0 : ∀ m (f : N → N),
    (sum ℤ (λ n, f n : Z) 0 m : Z) = sum_N f 0 m.
Proof.
  intros m f.
  induction m using Induction.
  - unfold sum, sum_N.
    now rewrite ? iterate_0.
  - rewrite sum_succ, sum_N_succ, IHm, INZ_add; auto using zero_le.
Qed.

Theorem INZ_sum : ∀ a b (f : N → N),
    (sum ℤ (λ n, f n : Z) a b : Z) = sum_N f a b.
Proof.
  intros a b f.
  destruct (classic (a ≤ b)%N) as [[c H] | H]; subst.
  2: { unfold sum, sum_N, iterate_with_bounds.
       repeat destruct excluded_middle_informative; tauto. }
  - unfold sum, sum_N.
    rewrite ? iterate_shift.
    apply INZ_sum_0.
Qed.

Theorem INZ_prod_0 : ∀ m (f : N → N),
    (prod ℤ (λ n, f n : Z) 0 m : Z) = prod_N f 0 m.
Proof.
  intros m f.
  induction m using Induction.
  - unfold prod, prod_N.
    now rewrite ? iterate_0.
  - rewrite prod_succ, prod_N_succ, IHm, INZ_mul; auto using zero_le.
Qed.

Theorem INZ_prod : ∀ a b (f : N → N),
    (prod ℤ (λ n, f n : Z) a b : Z) = prod_N f a b.
Proof.
  intros a b f.
  destruct (classic (a ≤ b)%N) as [[c H] | H]; subst.
  2: { unfold prod, prod_N, iterate_with_bounds.
       repeat destruct excluded_middle_informative; tauto. }
  - unfold prod, prod_N.
    rewrite ? iterate_shift.
    apply INZ_prod_0.
Qed.

Definition even (x : Z) := 2｜x.
Definition odd (x : Z) := ¬ even x.

Theorem odd_classification : ∀ x, odd x ↔ ∃ k, x = 2 * k + 1.
Proof.
  split; intros H.
  - destruct (division_algorithm x 2) as [q [r [H0 H1]]];
      try apply (ordered_rings.zero_lt_2 ℤ_order).
    exists q.
    rewrite <-H0.
    f_equal.
    destruct (integers.T r 1) as [[H2 _] | [[_ [H2_]] | [_ [_ H2]]]].
    + destruct H1 as [[H1 | H1] _]; simpl in *.
      * contradiction (lt_0_1 r).
      * subst.
        contradiction H.
        exists q; simpl.
        now replace (2*q+0) with (q*2) by ring.
    + congruence.
    + destruct H1 as [_ H1].
      contradiction (lt_0_1 (r+(-1%Z))%Z).
      * now rewrite <-(ordered_rings.lt_shift ℤ_order).
      * rewrite <-(integers.A3 1) at 2.
        rewrite (integers.A1 0), <-(integers.A4 1), integers.A2,
        ? (integers.A1 _ (-(1))).
        now apply (ordered_rings.O1 ℤ_order).
  - destruct H as [k H].
    subst.
    intros [x H]; simpl in *.
    destruct two_is_prime as [H0 H1].
    contradict H0.
    exists (x+-k); simpl.
    rewrite integers.D1, <-H.
    now ring_simplify.
Qed.

Theorem odd_add : ∀ a b, odd a → odd b → even (a+b).
Proof.
  intros a b H H0.
  apply odd_classification in H as [k H], H0 as [l H0].
  subst.
  exists (k+l+1).
  simpl.
  now replace ((k+l+1)*2) with (2*k+1+(2*l+1)) by ring.
Qed.
