Require Export integers.

Definition divide x y := exists z, y = z * x.

Notation "x ｜ y" := (divide x y) (at level 60, format "x '｜' y") : Z_scope.

Theorem div_mul_r : ∀ a b c, a｜b → a｜b*c.
Proof.
  intros a b c [d H].
  exists (d*c).
  ring [H].
Qed.

Theorem div_mul_l : ∀ a b c, a｜c → a｜b*c.
Proof.
  intros a b c [d H].
  exists (d*b).
  ring [H].
Qed.

Theorem div_add : ∀ a b c, a｜b → a｜c → a｜b+c.
Proof.
  intros a b c [x H] [y H0].
  exists (x+y).
  ring [H H0].
Qed.

Theorem div_mul_add : ∀ a m n x y, a｜m → a｜n → a｜m*x + n*y.
Proof.
  auto using div_add, div_mul_r.
Qed.

Theorem div_0_r : ∀ a, a｜0.
Proof.
  exists 0.
  ring.
Qed.

Theorem div_0_l : ∀ a, 0｜a ↔ a = 0.
Proof.
  split; intros H; [ destruct H as [x H] | exists 0 ]; ring [H].
Qed.

Theorem div_refl : ∀ a, a｜a.
Proof.
  exists 1.
  ring.
Qed.

Theorem div_trans : ∀ a b c, a｜b → b｜c → a｜c.
Proof.
  intros a b c [x H] [y H0].
  exists (x*y).
  ring [H H0].
Qed.

Theorem div_1_l : ∀ a, 1｜a.
Proof.
  intros a.
  exists a.
  ring.
Qed.

Theorem div_sign_r : ∀ a b, a｜b ↔ a｜-b.
Proof.
  split; intros [x H]; exists (-x); ring [H].
Qed.

Theorem div_sign_l : ∀ a b, a｜b ↔ -a｜b.
Proof.
  split; intros [x H]; exists (-x); ring [H].
Qed.

Definition mul_pos_pos := O2.
Definition mul_lt_l := O3.

Theorem mul_lt_r : ∀ a b c, a < b →  0 < c → a * c < b * c.
Proof.
  intros a b c H H0.
  rewrite ? (M1 _ c).
  now apply mul_lt_l.
Qed.

Theorem neg_lt_0 : ∀ a, 0 < a ↔ -a < 0.
Proof.
  split; intros H.
  - eapply (O1 (-a)) in H.
    now rewrite A3_r, A1, A4 in H.
  - eapply (O1 a) in H.
    now rewrite A3_r, A4 in H.
Qed.

Theorem lt_neg_0 : ∀ a, a < 0 ↔ 0 < -a.
Proof.
  intros a.
  rewrite neg_lt_0.
  now replace (- -a) with a by ring.
Qed.

Theorem mul_pos_neg : ∀ a b, 0 < a → b < 0 → a * b < 0.
Proof.
  intros a b H H0.
  rewrite lt_neg_0 in *.
  eapply O2 in H; eauto.
  replace (-(a*b)) with (-b*a) in * by ring; auto.
Qed.

Theorem mul_neg_pos : ∀ a b, a < 0 → 0 < b → a * b < 0.
Proof.
  intros a b H H0.
  rewrite M1.
  now apply mul_pos_neg.
Qed.

Theorem mul_neg_neg : ∀ a b, a < 0 → b < 0 → 0 < a * b.
Proof.
  intros a b H H0.
  rewrite lt_neg_0 in *.
  replace (a*b) with (-a*-b) by ring; eauto using mul_pos_pos.
Qed.

Theorem pos_mul : ∀ a b, 0 < a * b → (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0).
Proof.
  intros a b H.
  destruct (T (a*b) 0), (T a 0), (T b 0); intuition; subst;
    try replace (a*0) with 0 in * by ring;
    try replace (0*b) with 0 in * by ring;
    try replace (0*0) with 0 in * by ring; auto;
      exfalso; eauto using mul_neg_pos, mul_pos_neg.
Qed.

Theorem neg_mul : ∀ a b, a * b < 0 → (0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b).
Proof.
  intros a b H.
  destruct (T (a*b) 0), (T a 0), (T b 0); intuition; subst;
    try replace (a*0) with 0 in * by ring;
    try replace (0*b) with 0 in * by ring;
    try replace (0*0) with 0 in * by ring; auto;
      exfalso; eauto using mul_neg_neg, mul_pos_pos.
Qed.

Theorem cancellation_Z_0_add : ∀ a b, a + b = 0 → b = -a.
Proof.
  intros a b H.
  now rewrite <-(A3 b), <-(A4 a), <-A2, (A1 (-a)), A2, H, A3.
Qed.

Theorem cancellation_Z_add : ∀ a b c, a + b = a + c → b = c.
Proof.
  intros a b c H.
  rewrite <-(A3 b), <-(A3 c), <-(A4 a), A1, A2, (A1 _ a), H.
  ring.
Qed.

Theorem cancellation_Z_0_mul : ∀ a b, a * b = 0 → a = 0 ∨ b = 0.
Proof.
  intros a b H.
  destruct (T (a*b) 0), (T a 0), (T b 0); intuition;
    eauto using pos_mul, neg_mul; exfalso;
      eauto using mul_neg_neg, mul_neg_pos, mul_pos_neg, mul_pos_pos.
Qed.

Theorem cancellation_mul_l : ∀ a b c, a ≠ 0 → a * b = a * c → b = c.
Proof.
  intros a b c H H0.
  assert (a * (b - c) = 0) as H1 by ring [H0].
  apply cancellation_Z_0_mul in H1 as [H1 | H1]; intuition.
  apply cancellation_Z_0_add in H1.
  ring [H1].
Qed.

Theorem cancellation_mul_r : ∀ a b c, a ≠ 0 → b * a = c * a → b = c.
Proof.
  eauto using M1, eq_trans, cancellation_mul_l.
Qed.

Lemma pos_div_l : ∀ a b, 0 < a → 0 < a * b → 0 < b.
Proof.
  intros a b H H0.
  pose proof (pos_mul a b).
  destruct (T 0 a), (T 0 b); intuition.
Qed.

Lemma pos_div_r : ∀ a b, 0 < a → 0 < b * a → 0 < b.
Proof.
  intros a b H H0.
  rewrite M1 in *.
  eauto using pos_div_l.
Qed.

Theorem le_trans : ∀ a b c, a ≤ b → b ≤ c → a ≤ c.
Proof.
  intros a b c [H | H] [H0 | H0]; subst; unfold le; eauto using lt_trans.
Qed.

Lemma one_lt : ∀ a, 1 < a → 0 < a.
Proof.
  eauto using lt_trans, zero_lt_1.
Qed.

Lemma lt_succ : ∀ m, m < m + 1.
Proof.
  intros m.
  rewrite <-(A3 m), A1 at 1.
  eauto using O1, zero_lt_1.
Qed.

Lemma succ_lt : ∀ n m : Z, n < m → n < m + 1.
Proof.
  eauto using lt_succ, lt_trans.
Qed.

Theorem lt_0_le_1 : ∀ a, 0 < a ↔ 1 ≤ a.
Proof.
  intros a.
  destruct (T a 1); unfold le in *; intuition; subst;
    eauto using zero_lt_1, one_lt.
  exfalso; apply (lt_0_1 a); eauto.
Qed.

Theorem mul_le_l : ∀ a b c, 0 < a → b ≤ c → a * b ≤ a * c.
Proof.
  intros a b c H H0.
  unfold le in *.
  destruct H0 as [H0 | H0]; [ left | right ]; subst; auto.
  apply mul_lt_l; eauto.
Qed.

Theorem mul_le_r : ∀ a b c, a ≤ b → 0 < c → a * c ≤ b * c.
Proof.
  intros a b c H H0.
  rewrite ? (M1 _ c).
  now apply mul_le_l.
Qed.

Theorem neg_neg_lt : ∀ a b, a < b → -b < -a.
Proof.
  intros a b H.
  rewrite lt_def in *.
  destruct H as [c [H H0]].
  exists c.
  split; auto; ring [H0].
Qed.

Theorem N_ge_0 : ∀ a : N, 0 ≤ a.
Proof.
  induction a using Induction.
  - now right.
  - left.
    destruct IHa as [H | H]; rewrite <-add_1_r, <-INZ_add.
    + eauto using succ_lt.
    + rewrite <-H, A3.
      eauto using zero_lt_1.
Qed.

Theorem lt_irrefl : ∀ a, ¬ a < a.
Proof.
  intros a.
  destruct (T a a); intuition.
Qed.

Theorem lt_antisym : ∀ a b, a < b → ¬ b < a.
Proof.
  intros a b H.
  destruct (T a b); intuition.
Qed.

Theorem le_antisymm : ∀ a b, a ≤ b → b ≤ a → a = b.
Proof.
  intros a b [H | H] [H0 | H0]; destruct (T a b); intuition.
Qed.

Theorem div_le : ∀ a b, 0 < b → a｜b → a ≤ b.
Proof.
  intros a b H [d H0].
  destruct (T a b); unfold le; intuition; subst.
  assert (0 < a) by eauto using lt_trans.
  eapply pos_div_r, lt_0_le_1, mul_le_r in H; try rewrite M3 in H; eauto.
Qed.

Definition assoc a b := a｜b ∧ b｜a.
Infix "~" := assoc (at level 70) : Z_scope.
Definition unit a := a｜1.
Definition pm a b := (a = b ∨ a = -b).
Notation " a = ± b " := (pm a b) (at level 60) : Z_scope.

Theorem assoc_N : ∀ a b : N, a ~ b → a = b.
Proof.
  intros a b [H H0]; apply INZ_inj.
  destruct (N_ge_0 a), (N_ge_0 b); try rewrite <-H1 in *;
    try rewrite <-H2 in *; try rewrite div_0_l in *; try congruence.
  eauto using div_le, le_antisymm.
Qed.

Theorem assoc_pos : ∀ a b, 0 < a → 0 < b → a ~ b → a = b.
Proof.
  intros a b H H0 H1.
  rewrite lt_def in H, H0.
  destruct H as [c [H H2]], H0 as [d [H0 H3]].
  subst.
  rewrite ? A3 in *.
  now apply INZ_inj, assoc_N.
Qed.

Theorem assoc_refl : ∀ a, a ~ a.
Proof.
  split; eauto using div_refl.
Qed.

Theorem assoc_sym : ∀ a b : Z, a ~ b → b ~ a.
Proof.
  now intros a b [H H0].
Qed.

Theorem assoc_sym_iff : ∀ a b, a ~ b ↔ b ~ a.
Proof.
  now split; intros [H H0].
Qed.

Theorem assoc_trans : ∀ a b c, a ~ b → b ~ c → a ~ c.
Proof.
  intros a b c [H H0] [H1 H2].
  split; eapply div_trans; eauto.
Qed.

Theorem assoc_zero : ∀ a, a ~ 0 ↔ a = 0.
Proof.
  split; intros H; subst; auto using assoc_refl.
  destruct H; now apply div_0_l.
Qed.

Theorem assoc_sign : ∀ a b, a ~ b → a ~ -b.
Proof.
  intros a b [H H0].
  split; now try rewrite <-div_sign_l; try rewrite <-div_sign_r.
Qed.

Theorem unit_sign : ∀ a, unit a → unit (-a).
Proof.
  intros a H.
  now apply div_sign_l in H.
Qed.

Theorem one_unit : unit 1.
Proof.
  apply div_refl.
Qed.

Theorem assoc_unit : ∀ a b, a ~ b → ∃ u, unit u ∧ b = a * u.
Proof.
  intros a b [[c H] [d H0]].
  destruct (classic (b = 0)); subst.
  - assert (a = 0) by ring [H0 H1].
    exists 1.
    split; auto using one_unit; ring [H H1].
  - exists c.
    split; try ring.
    exists d.
    apply (cancellation_mul_r a).
    + contradict H1; ring [H1].
    + now rewrite M3, <-M2.
Qed.

Theorem assoc_pm : ∀ a b, a ~ b → a = ± b.
Proof.
  intros a b H.
  unfold pm.
  destruct (T a 0), (T b 0); intuition; rewrite lt_neg_0 in *; subst;
    try (now (destruct H; rewrite div_0_l in *; intuition));
    [ assert (-a = -b → a = b) by (intro M; ring [M]) ; left |
      assert (-a = b → a = -b) by (intro M; ring [M]) ; right | right | left ];
    eauto 7 using assoc_pos, assoc_sign, assoc_sym, assoc_sign.
Qed.

Theorem unit_pm_1 : ∀ a, unit a → a = ± 1.
Proof.
  intros a H.
  apply assoc_pm; split; auto using div_1_l.
Qed.

Theorem division_algorithm : ∀ a b,
    0 < a → 0 < b → ∃ q r : Z, b * q + r = a ∧ 0 ≤ r < b.
Proof.
  intros a b H H0.
  induction a as [a IHa] using strong_induction.
  destruct (T a b); unfold le; intuition; [ exists 0, a | exists 1, 0 | ];
    repeat split; auto; subst; try ring.
  assert (0 < a + -b) as H3 by (rewrite <-(A4 a); eauto using O1, neg_neg_lt).
  destruct (IHa (a + -b)) as [q [r [H5 H6]]]; repeat split; auto.
  - rewrite <-(A3_r a) at 2.
    now apply O1, neg_lt_0.
  - exists (q+1), r.
    split; auto.
    rewrite D1_l, <-A2, (A1 _ r), A2, H5; ring.
Qed.
