Require Export iterated_ops Ring.
Set Warnings "-notation-bound-to-variable,-notation-overridden".
Set Warnings "-ambiguous-paths,-uniform-inheritance".

Record ring :=
  mkRing {
      Rset : set;
      zero : elts Rset where "0" := zero;
      one : elts Rset where "1" := one;
      add : elts Rset → elts Rset → elts Rset where "a + b" := (add a b);
      mul : elts Rset → elts Rset → elts Rset where "a * b" := (mul a b);
      neg : elts Rset → elts Rset where "- a" := (neg a);
      A3 : ∀ a, 0 + a = a;
      A1 : ∀ a b, a + b = b + a;
      A2 : ∀ a b c, a + (b + c) = (a + b) + c;
      M3 : ∀ a, 1 * a = a;
      M1 : ∀ a b, a * b = b * a;
      M2 : ∀ a b c, a * (b * c) = (a * b) * c;
      D1 : ∀ a b c, (a + b) * c = a * c + b * c;
      A4 : ∀ a, a + (-a) = 0;
    }.

Section Ring_theorems.

  Variable Ring : ring.
  Notation R := (elts (Rset Ring)).
  Declare Scope Ring_scope.
  Delimit Scope Ring_scope with ring.
  Open Scope Ring_scope.
  Bind Scope Ring_scope with R.
  Notation "0" := (zero Ring) : Ring_scope.
  Notation "1" := (one Ring) : Ring_scope.
  Infix "+" := (add Ring) : Ring_scope.
  Infix "*" := (mul Ring) : Ring_scope.
  Notation "- a" := (neg Ring a) : Ring_scope.

  Definition IRS (a : R) := elt_to_set _ a : set.

  Coercion IRS : R >-> set.

  Definition sub (a b : R) := a + (-b) : R.

  Infix "-" := sub : Ring_scope.

  Lemma sub_is_neg : ∀ a b, a - b = a + -b.
  Proof.
    auto.
  Qed.

  Definition ringify :=
    (mk_rt 0 1 (add _) (mul _) sub (neg _) eq (A3 _) (A1 _) (A2 _)
           (M3 _) (M1 _) (M2 _) (D1 _) sub_is_neg (A4 _)).
  Add Ring generic_ring : ringify.

  Theorem mul_0_r : ∀ a, a * 0 = 0.
  Proof.
    intros a.
    ring.
  Qed.

  Theorem mul_neg_1_l : ∀ a, (-(1)) * a = -a.
  Proof.
    intros a.
    ring.
  Qed.

  Theorem mul_neg_1_r : ∀ a, a * (-(1)) = -a.
  Proof.
    intros a.
    ring.
  Qed.

  Theorem mul_neg_neg : ∀ a b, (-a) * (-b) = a * b.
  Proof.
    intros a b.
    ring.
  Qed.

  Theorem neg_0 : 0 = -0.
  Proof.
    ring.
  Qed.

  Theorem mul_0_l : ∀ a, 0 * a = 0.
  Proof.
    intros a.
    ring.
  Qed.

  Theorem A3_r : ∀ a, a + 0 = a.
  Proof.
    intros a.
    ring.
  Qed.

  Theorem A4_l : ∀ a, -a + a = 0.
  Proof.
    intros a.
    ring.
  Qed.

  Theorem M3_r : ∀ a, a * 1 = a.
  Proof.
    intros a.
    ring.
  Qed.

  Theorem D1_l : ∀ a b c, a * (b + c) = a * b + a * c.
  Proof.
    intros a b c.
    ring.
  Qed.

  Theorem D1_minus_l : ∀ a b c, a * (b - c) = a * b - a * c.
  Proof.
    intros a b c.
    ring.
  Qed.

  Theorem D1_minus_r : ∀ a b c, (a - b) * c = a * c - b * c.
  Proof.
    intros a b c.
    ring.
  Qed.

  Theorem neg_neg : ∀ a, --a = a.
  Proof.
    intros a.
    ring.
  Qed.

  Theorem difference_of_squares : ∀ a b, a * a - b * b = (a - b) * (a + b).
  Proof.
    intros a b.
    ring.
  Qed.

  Definition divide x y := ∃ z, y = z * x.

  Notation "x ｜ y" :=
    (divide x y) (at level 60, format "x '｜' y") : Ring_scope.

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
  Definition divide_refl := div_refl.

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

  Theorem div_sign_neg_r : ∀ a b, a｜-b → a｜b.
  Proof.
    intros a b H.
    now rewrite div_sign_r.
  Qed.

  Theorem div_sign_r_neg : ∀ a b, a｜b → a｜-b.
  Proof.
    intros a b H.
    now rewrite <-div_sign_r.
  Qed.

  Theorem div_sign_l : ∀ a b, a｜b ↔ -a｜b.
  Proof.
    split; intros [x H]; exists (-x); ring [H].
  Qed.

  Theorem div_sign_neg_l : ∀ a b, -a｜b → a｜b.
  Proof.
    intros a b H.
    now rewrite div_sign_l.
  Qed.

  Theorem div_sign_l_neg : ∀ a b, a｜b → -a｜b.
  Proof.
    intros a b H.
    now rewrite <-div_sign_l.
  Qed.

  Definition assoc a b := a｜b ∧ b｜a.
  Infix "~" := assoc (at level 70) : Ring_scope.
  Definition unit a := a｜1.

  Theorem assoc_refl : ∀ a, a ~ a.
  Proof.
    split; eauto using div_refl.
  Qed.

  Theorem assoc_sym : ∀ a b, a ~ b → b ~ a.
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

  Add Parametric Relation : (elts (Rset Ring)) assoc
      reflexivity proved by (assoc_refl)
      symmetry proved by (assoc_sym)
      transitivity proved by (assoc_trans) as assoc_equivalence.

  Theorem assoc_zero : ∀ a, a ~ 0 ↔ a = 0.
  Proof.
    split; intros H; subst; auto using assoc_refl.
    destruct H; now apply div_0_l.
  Qed.

  Theorem assoc_sign : ∀ a b, a ~ b → a ~ -b.
  Proof.
    intros a b [H H0].
    split; auto using div_sign_l_neg, div_sign_r_neg.
  Qed.

  Theorem unit_closure : ∀ a b, unit a → unit b → unit (a * b).
  Proof.
    intros a b [x H] [y H0].
    exists (x*y).
    rewrite <-(M3 _ 1), H, H0 at 1.
    ring.
  Qed.

  Theorem unit_square : ∀ u, unit (u * u) → unit u.
  Proof.
    intros u [x H].
    exists (x*u).
    rewrite H.
    ring.
  Qed.

  Theorem unit_sign : ∀ a, unit a ↔ unit (-a).
  Proof.
    split; intros H; unfold unit in *; now rewrite <-div_sign_l in *.
  Qed.

  Theorem unit_sign_r : ∀ a, unit a → unit (-a).
  Proof.
    intros a H; now apply div_sign_l_neg.
  Qed.

  Theorem one_unit : unit 1.
  Proof.
    apply div_refl.
  Qed.

  Theorem neg_one_unit : unit (-(1)).
  Proof.
    apply unit_sign_r, one_unit.
  Qed.

  Theorem unit_cancel : ∀ a b c, unit a → a * b = a * c → b = c.
  Proof.
    intros a b c [x H] H0.
    now rewrite <-(M3 _ b), H, <-M2, H0, M2, <-H, M3.
  Qed.

  Theorem cancellation_0_add : ∀ a b, a + b = 0 → b = -a.
  Proof.
    intros a b H.
    rewrite <-(A3 _ (-a)), <-H.
    ring.
  Qed.

  Theorem cancellation_add : ∀ a b c, a + b = a + c → b = c.
  Proof.
    intros a b c H.
    rewrite <-(A3 _ b), <-(A4 _ a), (A1 _ a), <-A2, H.
    ring.
  Qed.

  Lemma cancellation_ne0 : ∀ a b, a * b ≠ 0 → a ≠ 0 ∧ b ≠ 0.
  Proof.
    intros a b H; split; contradict H; subst; ring.
  Qed.

  Definition sum f a b := iterate_with_bounds _ (add _) f 0 a b.
  Definition prod f a b := iterate_with_bounds _ (mul _) f 1 a b.

  Theorem sum_succ : ∀ f a b,
      a ≤ S b → (sum f a (S b)) = (sum f a b) + (f (S b)).
  Proof.
    intros f a b H.
    apply iterate_succ_lower_limit; auto.
    ring.
  Qed.

  Theorem prod_succ : ∀ f a b,
      a ≤ S b → (prod f a (S b)) = (prod f a b) * (f (S b)).
  Proof.
    intros f a b H.
    apply iterate_succ_lower_limit; auto.
    ring.
  Qed.

  Theorem sum_dist :
    ∀ f g a b, sum (λ n, (f n) + (g n)) a b = sum f a b + sum g a b.
  Proof.
    intros f g a b.
    destruct (classic (a ≤ b)) as [[c H] | H].
    2: { unfold sum, iterate_with_bounds.
         repeat destruct excluded_middle_informative; try tauto.
         now rewrite A3. }
    subst.
    induction c using Induction.
    - rewrite add_0_r.
      unfold sum.
      now rewrite ? iterate_0.
    - rewrite add_succ_r, ? sum_succ, IHc; try ring;
        exists (c+1)%N; now rewrite add_1_r, add_succ_r.
  Qed.

  Theorem sum_mul : ∀ f a b c, c * sum f a b = sum (λ n, c * (f n)) a b.
  Proof.
    intros f a b c.
    destruct (classic (a ≤ b)) as [[d H] | H].
    2: { unfold sum, iterate_with_bounds.
         repeat destruct excluded_middle_informative; try tauto; ring. }
    subst.
    induction d using Induction.
    - rewrite add_0_r.
      unfold sum.
      now rewrite ? iterate_0.
    - now rewrite add_succ_r, ? sum_succ, D1_l, IHd;
        try (exists (d+1)%N; now rewrite add_1_r, add_succ_r).
  Qed.

  Theorem prod_dist :
    ∀ f g a b, prod (λ n, (f n) * (g n)) a b = prod f a b * prod g a b.
  Proof.
    intros f g a b.
    destruct (classic (a ≤ b)) as [[c H] | H].
    2: { unfold prod, iterate_with_bounds.
         repeat destruct excluded_middle_informative; try tauto; ring. }
    subst.
    induction c using Induction.
    - rewrite add_0_r.
      unfold prod.
      now rewrite ? iterate_0.
    - rewrite add_succ_r, ? prod_succ, IHc; try ring;
        exists (c+1)%N; now rewrite add_1_r, add_succ_r.
  Qed.

  Theorem sum_of_0 : ∀ d, (sum (λ n, 0) 0 d) = 0.
  Proof.
    induction d using Induction.
    - apply iterate_0.
    - rewrite sum_succ, IHd; auto using zero_le; ring.
  Qed.

  Theorem unit_prod_closure_0 :
    ∀ n f, (∀ i, 0 ≤ i ≤ n → unit (f i)) → unit (prod f 0 n).
  Proof.
    induction n using Induction; intros f H.
    - unfold prod.
      rewrite iterate_0.
      auto using le_refl.
    - rewrite prod_succ; try apply unit_closure; eauto using le_refl, zero_le.
      apply IHn.
      intros i [H0 H1].
      eauto using le_trans, le_succ.
  Qed.

  Theorem unit_prod_closure :
    ∀ a b f, (∀ i, a ≤ i ≤ b → unit (f i)) → unit (prod f a b).
  Proof.
    intros a b f H.
    destruct (classic (a ≤ b)%N) as [[c H0] | H0]; subst.
    2: { unfold prod, iterate_with_bounds.
         destruct excluded_middle_informative; auto using one_unit; tauto. }
    unfold prod.
    rewrite iterate_shift.
    apply unit_prod_closure_0.
    intros i H0.
    apply H.
    rewrite <-(add_0_l a), ? (add_comm a) at 1.
    split; apply O1_le; intuition.
  Qed.

  Definition pow a n := iterated_op _ (mul _) 1 (λ x, a) n.

  Infix "^" := pow : Ring_scope.

  Theorem pow_0_r : ∀ x, x^0 = 1.
  Proof.
    intros x.
    apply iterated_op_0.
  Qed.

  Theorem pow_succ_r : ∀ x y, x^(S y) = x^y * x.
  Proof.
    intros x y.
    apply iterated_op_succ.
  Qed.

  Theorem pow_1_r : ∀ x, x^1 = x.
  Proof.
    intros x.
    unfold naturals.one.
    now rewrite pow_succ_r, pow_0_r, M3.
  Qed.

  Theorem pow_1_l : ∀ x, 1^x = 1.
  Proof.
    induction x using Induction.
    - now rewrite pow_0_r.
    - now rewrite pow_succ_r, IHx, M3.
  Qed.

  Theorem pow_0_l : ∀ x, x ≠ 0%N → 0^x = 0.
  Proof.
    induction x using Induction; intros H; try tauto.
    now rewrite pow_succ_r, mul_0_r.
  Qed.

  Theorem pow_2_r : ∀ x, x^2 = x * x.
  Proof.
    intros x.
    now rewrite pow_succ_r, pow_1_r.
  Qed.

  Theorem pow_add_r : ∀ a b c, a^(b+c) = a^b * a^c.
  Proof.
    induction c using Induction.
    - now rewrite add_0_r, pow_0_r, M3_r.
    - now rewrite add_succ_r, ? pow_succ_r, IHc, M2.
  Qed.

  Theorem pow_mul_l : ∀ a b c, (a*b)^c = a^c * b^c.
  Proof.
    induction c using Induction.
    - now rewrite ? pow_0_r, M3.
    - now rewrite ? pow_succ_r, <-? M2, (M2 _ a), (M1 _ _ (b^c)), IHc, ? M2.
  Qed.

  Theorem pow_mul_r : ∀ a b c, a^(b*c) = (a^b)^c.
  Proof.
    induction c using Induction.
    - now rewrite naturals.mul_0_r, ? pow_0_r.
    - now rewrite mul_succ_r, pow_succ_r, pow_add_r, IHc.
  Qed.

  Theorem prod_mul : ∀ f a b c,
      a ≤ b → c^(S (b-a)) * prod f a b = prod (λ n, c * (f n)) a b.
  Proof.
    intros f a b c [d H].
    subst.
    induction d using Induction.
    - rewrite add_0_r, sub_diag, pow_1_r.
      unfold prod.
      now rewrite ? iterate_0.
    - rewrite ? (add_comm a), sub_abba, ? pow_succ_r, ? (add_comm _ a),
      add_succ_r, ? prod_succ, (add_comm a), <-IHd in *;
        try (exists (d+1)%N; rewrite <-? add_1_r); ring.
  Qed.

  Theorem unit_pow_closure : ∀ a n, 0 < n → unit (a^n) → unit a.
  Proof.
    intros a n H H0.
    destruct (classic (n = 0%N)) as [H1 | H1].
    { subst.
      contradiction (lt_irrefl 0). }
    apply succ_0 in H1 as [m H1].
    subst.
    rewrite pow_succ_r in H0.
    destruct H0 as [x H0].
    exists (x * a^m).
    rewrite H0.
    ring.
  Qed.

  Definition INR (n : N) := sum (λ n, 1) 1 n.
  Coercion INR : N >-> R.

  Theorem INR_zero : 0 = 0%N.
  Proof.
    unfold INR, sum, iterate_with_bounds.
    destruct excluded_middle_informative; auto.
    exfalso.
    apply le_not_gt in l.
    eauto using succ_lt.
  Qed.

  Theorem INR_one : 1 = 1%N.
  Proof.
    unfold INR, sum.
    now rewrite iterate_0.
  Qed.

  Theorem INR_add : ∀ a b : N, a + b = (a + b)%N.
  Proof.
    intros a b.
    unfold INR.
    induction b using Induction.
    { fold (INR 0).
      rewrite <-INR_zero, add_0_r.
      ring. }
    rewrite add_succ_r, ? sum_succ, <-IHb; try ring;
      [ exists (a+b)%N | exists b ]; now rewrite <-add_1_r, naturals.add_comm.
  Qed.

  Theorem INR_mul : ∀ a b : N, a * b = ((a * b)%N).
  Proof.
    intros a b.
    unfold INR.
    induction b using Induction.
    { rewrite naturals.mul_0_r.
      fold (INR 0).
      rewrite <-? INR_zero.
      ring. }
    rewrite mul_succ_r, sum_succ, D1_l, IHb.
    - fold (INR (a*b)) (INR a) (INR (a*b+a)).
      ring_simplify.
      apply INR_add.
    - exists b.
      now rewrite <-add_1_r, naturals.add_comm.
  Qed.

  Section Subring_construction.

    Variable S : set.
    Hypothesis subset : S ⊂ Rset Ring.
    Definition is_subring S := (∀ a b : R, a ∈ S → b ∈ S → a + b ∈ S) ∧
                               (∀ a b : R, a ∈ S → b ∈ S → a * b ∈ S) ∧
                               (∀ a : R, a ∈ S → -a ∈ S) ∧
                               (1 ∈ S).
    Hypothesis SR : is_subring S.
    Definition sub_R := elts S.

    Definition ISR : sub_R → R.
    Proof.
      intros x.
      pose proof (elts_in_set _ x) as H; simpl in H.
      apply subset in H.
      exact (exist _ _ H).
    Defined.

    Coercion ISR : sub_R >-> R.

    Definition sub_add : sub_R → sub_R → sub_R.
    Proof.
      intros a b.
      assert (a + b ∈ S) as H.
      { destruct SR as [H [H0 [H1 H2]]].
        apply H; apply (elts_in_set S). }
      exact (exist _ _ H).
    Defined.

    Definition sub_mul : sub_R → sub_R → sub_R.
    Proof.
      intros a b.
      assert (a * b ∈ S) as H.
      { destruct SR as [H [H0 [H1 H2]]].
        apply H0; apply (elts_in_set S). }
      exact (exist _ _ H).
    Defined.

    Definition sub_neg : sub_R → sub_R.
    Proof.
      intros a.
      assert (-a ∈ S) as H.
      { destruct SR as [H [H0 [H1 H2]]].
        apply H1; apply (elts_in_set S). }
      exact (exist _ _ H).
    Defined.

    Declare Scope Subring_scope.
    Delimit Scope Subring_scope with subring.
    Open Scope Subring_scope.
    Bind Scope Subring_scope with sub_R.

    Infix "+" := sub_add : Subring_scope.
    Infix "*" := sub_mul : Subring_scope.

    Notation "- a" := (sub_neg a) : Subring_scope.

    Definition sub_one : sub_R.
    Proof.
      destruct SR as [H [H0 [H1 H2]]].
      exact (exist _ _ H2).
    Defined.
    Notation "1" := sub_one : Subring_scope.

    Theorem ISR_eq : ∀ a b : sub_R, (a : R) = (b : R) → a = b.
    Proof.
      intros [a A] [b B] H.
      unfold ISR in H.
      simpl in *.
      apply set_proj_injective.
      now inversion H.
    Qed.

    Theorem ISR_add : ∀ a b : sub_R, (a + b)%ring = a + b.
    Proof.
      intros a b.
      now apply set_proj_injective.
    Qed.

    Theorem ISR_mul : ∀ a b : sub_R, (a * b)%ring = a * b.
    Proof.
      intros a b.
      now apply set_proj_injective.
    Qed.

    Theorem ISR_neg : ∀ a : sub_R, (-a)%ring = -a.
    Proof.
      intros a.
      now apply set_proj_injective.
    Qed.

    Lemma zero_construction : 0 ∈ S.
    Proof.
      destruct SR as [H [H0 [H1 H2]]].
      rewrite <-(A4 _ (1%ring)).
      auto.
    Qed.

    Definition sub_zero := (exist _ _ zero_construction) : sub_R.
    Notation "0" := sub_zero : Subring_scope.
    Theorem sub_A1 : ∀ a b, a + b = b + a.
    Proof.
      intros a b.
      apply ISR_eq.
      now rewrite <-? ISR_add, A1.
    Qed.

    Theorem sub_A2 : ∀ a b c, a + (b + c) = (a + b) + c.
    Proof.
      intros a b c.
      apply ISR_eq.
      now rewrite <-? ISR_add, A2.
    Qed.

    Theorem sub_zero_is_zero : 0%ring = 0.
    Proof.
      now apply set_proj_injective.
    Qed.

    Theorem sub_one_is_one : 1%ring = 1.
    Proof.
      unfold sub_one.
      destruct SR as [H [H0 [H1 H2]]].
      now apply set_proj_injective.
    Qed.

    Theorem sub_A3 : ∀ a, 0 + a = a.
    Proof.
      intros a.
      apply ISR_eq.
      now rewrite <-? ISR_add, <-sub_zero_is_zero, A3.
    Qed.

    Theorem sub_A4 : ∀ a, a + -a = 0.
    Proof.
      intros a.
      apply ISR_eq.
      now rewrite <-? ISR_add, <-ISR_neg, A4, sub_zero_is_zero.
    Qed.

    Theorem sub_M1 : ∀ a b, a * b = b * a.
    Proof.
      intros a b.
      apply ISR_eq.
      now rewrite <-? ISR_mul, M1.
    Qed.

    Theorem sub_M2 : ∀ a b c, a * (b * c) = (a * b) * c.
    Proof.
      intros a b c.
      apply ISR_eq.
      now rewrite <-? ISR_mul, M2.
    Qed.

    Theorem sub_M3 : ∀ a, 1 * a = a.
    Proof.
      intros a.
      apply ISR_eq.
      now rewrite <-? ISR_mul, <-sub_one_is_one, M3.
    Qed.

    Theorem sub_D1 : ∀ a b c, (a + b) * c = a * c + b * c.
    Proof.
      intros a b c.
      apply ISR_eq.
      now rewrite <-? ISR_mul, <-? ISR_add, <-? ISR_mul, D1.
    Qed.

    Definition subring :=
      mkRing _ sub_zero sub_one sub_add sub_mul sub_neg sub_A3 sub_A1 sub_A2
             sub_M3 sub_M1 sub_M2 sub_D1 sub_A4.

  End Subring_construction.

  Definition subring_of_arbitrary_set (S : set) : rings.ring.
  Proof.
    destruct (excluded_middle_informative (S ⊂ Rset Ring)).
    - destruct (excluded_middle_informative (is_subring S)).
      + exact (mkRing _ (sub_zero S i) (sub_one S i) (sub_add S s i)
                      (sub_mul S s i) (sub_neg S s i) (sub_A3 S s i)
                      (sub_A1 S s i) (sub_A2 S s i) (sub_M3 S s i)
                      (sub_M1 S s i) (sub_M2 S s i) (sub_D1 S s i)
                      (sub_A4 S s i)).
      + exact Ring.
    - exact Ring.
  Defined.

  Section Subring_generation.

    Variable S : set.

    Hypothesis subset : S ⊂ Rset Ring.

    Definition subset_generated_by S :=
      ⋂ {s in P (Rset Ring) | S ⊂ s ∧ is_subring s}.

    Lemma generated_nonempty : {s in P (Rset Ring) | S ⊂ s ∧ is_subring s} ≠ ∅.
    Proof.
      apply Nonempty_classification.
      exists (Rset Ring).
      rewrite Specify_classification, Powerset_classification.
      repeat split; eauto using Set_is_subset, elts_in_set.
    Qed.

    Lemma generated_subset : subset_generated_by S ⊂ Rset Ring.
    Proof.
      unfold subset_generated_by.
      intros x H.
      rewrite Intersection_classification in H; auto using generated_nonempty.
      pose proof generated_nonempty as H0.
      apply Nonempty_classification in H0 as [s H0].
      apply H in H0 as H1.
      apply Specify_classification in H0 as [H0 [H2 H3]].
      apply Powerset_classification in H0.
      auto.
    Qed.

    Lemma subring_generation_construction : is_subring (subset_generated_by S).
    Proof.
      unfold subset_generated_by.
      repeat split.
      - intros a b H H0.
        rewrite Intersection_classification in *; auto using generated_nonempty.
        intros s H1.
        apply H in H1 as H2.
        apply H0 in H1 as H3.
        apply Specify_classification in H1 as [H1 [H4 [H5 [H6 [H7 H8]]]]].
        auto.
      - intros a b H H0.
        rewrite Intersection_classification in *; auto using generated_nonempty.
        intros s H1.
        apply H in H1 as H2.
        apply H0 in H1 as H3.
        apply Specify_classification in H1 as [H1 [H4 [H5 [H6 [H7 H8]]]]].
        auto.
      - intros a H.
        rewrite Intersection_classification in *; auto using generated_nonempty.
        intros s H1.
        apply H in H1 as H2.
        apply Specify_classification in H1 as [H1 [H3 [H4 [H5 [H6 H7]]]]].
        auto.
      - rewrite Intersection_classification in *; auto using generated_nonempty.
        intros s H.
        now apply Specify_classification in H as [H [H0 [H1 [H2 [H3 H4]]]]].
    Qed.

    Definition subring_generated_by :=
      subring (subset_generated_by S) generated_subset
              subring_generation_construction.

    Theorem subset_generated_by_subring :
      is_subring S → S = subset_generated_by S.
    Proof.
      intros H.
      unfold subset_generated_by.
      apply Extensionality.
      split; intros H0.
      - apply Intersection_classification; auto using generated_nonempty.
        intros s H1.
        apply Specify_classification in H1 as [H1 [H2 H3]].
        auto.
      - rewrite Intersection_classification in *; auto using generated_nonempty.
        assert (S ∈ {s in P (Rset Ring) | S ⊂ s ∧ is_subring s}) as H1; auto.
        apply Specify_classification.
        split; auto using Set_is_subset.
        now apply Powerset_classification.
    Qed.

  End Subring_generation.

  Theorem subring_wf :
    ∀ S T, S = T → subring_of_arbitrary_set S = subring_of_arbitrary_set T.
  Proof.
    intros S T H.
    now rewrite H.
  Qed.

  Section Subrings_match.
    Variable S : set.
    Hypothesis subset_S : S ⊂ Rset Ring.
    Hypothesis subring_S : is_subring S.

    Theorem subrings_match :
      subring_of_arbitrary_set S = subring S subset_S subring_S.
    Proof.
      unfold subring_of_arbitrary_set.
      repeat destruct excluded_middle_informative; try tauto.
      unfold subring.
      replace s with subset_S by now apply proof_irrelevance.
      now replace i with subring_S by now apply proof_irrelevance.
    Qed.
  End Subrings_match.

  Section Subrings_generated_by_subrings.
    Variable S : set.
    Hypothesis subset_S : S ⊂ Rset Ring.
    Hypothesis subring_S : is_subring S.

    Theorem subring_generated_by_subring :
      subring S subset_S subring_S = subring_generated_by S subset_S.
    Proof.
      unfold subring_generated_by.
      rewrite <-? subrings_match, <-(subset_generated_by_subring S); auto.
    Qed.
  End Subrings_generated_by_subrings.

  Theorem zero_ring_degeneracy : 1 = 0 → ∀ a b : R, a = b.
  Proof.
    intros H a b.
    ring [H].
  Qed.

  Theorem unit_nonzero : 1 ≠ 0 → ∀ a, unit a → a ≠ 0.
  Proof.
    intros H a [x H0] H1.
    subst.
    now ring_simplify in H0.
  Qed.

  Theorem singleton_sum : ∀ m n a,
      m ≤ n →
      sum (λ k, if (excluded_middle_informative (k = m)) then a else 0) 0 n = a.
  Proof.
    intros m n a H.
    induction n using Induction.
    { unfold sum.
      rewrite iterate_0.
      destruct excluded_middle_informative; auto.
      assert (m ≠ 0%N) as H0 by auto.
      apply succ_0 in H0 as [k H0].
      subst.
      rewrite le_not_gt in H.
      contradict H.
      now apply lt_succ. }
    destruct (classic (m = S n)) as [H0 | H0].
    - subst.
      rewrite sum_succ, <-(A3 _ a) at 1; auto using zero_le.
      f_equal.
      + rewrite <-(sum_of_0 n).
        apply iterate_extensionality.
        intros k H0.
        destruct excluded_middle_informative; auto using sum_of_0.
        subst.
        destruct H0 as [H0 H1].
        apply le_not_gt in H1.
        contradict H1.
        auto using succ_lt.
      + destruct excluded_middle_informative; tauto.
    - rewrite sum_succ, IHn; auto using zero_le.
      + destruct excluded_middle_informative; try congruence; ring.
      + destruct H as [c H].
        rewrite <-H in H0.
        assert (c ≠ 0%N) as H1 by (contradict H0; ring [H0]).
        apply succ_0 in H1 as [d H1].
        exists d.
        rewrite H1, add_succ_r in H.
        now apply PA5.
  Qed.

  Definition swap (X Y : Type) (a b : X) (f : X → Y) : X → Y.
  Proof.
    intros x.
    destruct (excluded_middle_informative (x = a)).
    - exact (f b).
    - destruct (excluded_middle_informative (x = b)).
      + exact (f a).
      + exact (f x).
  Defined.

  Theorem swap_refl : ∀ X Y (a : X) f, swap X Y a a f = f.
  Proof.
    intros X Y a f.
    extensionality x.
    unfold swap.
    destruct excluded_middle_informative; auto; now subst.
  Qed.

  Theorem swap_sym : ∀ X Y (a b : X) f, swap X Y a b f = swap X Y b a f.
  Proof.
    intros X Y a b f.
    extensionality x.
    unfold swap.
    destruct excluded_middle_informative; auto; subst.
    destruct excluded_middle_informative; auto; now subst.
  Qed.

  Lemma product_swap_upper_two : ∀ m f,
      prod f 0 (S (S m)) = prod (swap _ _ (S m) (S (S m)) f) 0 (S (S m)).
  Proof.
    intros m f.
    rewrite ? prod_succ, <-M2, (M1 _ (f (S m))), M2; auto using zero_le.
    do 2 f_equal; unfold swap;
      try (repeat destruct excluded_middle_informative; subst; congruence).
    apply iterate_extensionality.
    intros k [H H0].
    repeat destruct excluded_middle_informative; auto; subst.
    - now apply not_succ_le in H0.
    - contradiction (not_succ_le (S m)).
      eauto using naturals.le_trans, le_succ.
  Qed.

  Lemma product_swap_upper_one : ∀ n f i,
      0 ≤ i ≤ n → prod (swap _ _ i n f) 0 n = prod f 0 n.
  Proof.
    induction n using Induction.
    { intros f i [H H0].
      unfold prod.
      replace i with 0%N by eauto using naturals.le_antisymm.
      now rewrite ? iterate_0, swap_refl. }
    intros f i [H H0].
    apply le_lt_or_eq in H0 as [H0 | H0]; try now rewrite H0, swap_refl.
    destruct (classic (1 = S n)%N) as [H1 | H1].
    { rewrite <-H1 in *.
      apply squeeze_lower in H; auto.
      subst.
      unfold naturals.one, prod, swap.
      rewrite ? iterate_succ, ? iterate_0; auto using zero_le.
      repeat destruct excluded_middle_informative;
        try now contradiction (PA4 0).
      ring. }
    assert (n ≠ 0)%N as H2 by (contradict H1; now apply f_equal).
    apply succ_0 in H2 as [m H2].
    subst.
    symmetry.
    destruct (classic (i = (S m))) as [H2 | H2];
      try now rewrite H2, product_swap_upper_two.
    rewrite product_swap_upper_two, prod_succ, <-(IHn _ i), ? prod_succ,
    <-? M2; repeat split; auto using zero_le, le_refl.
    2: { now apply le_lt_succ. }
    f_equal.
    - apply iterate_extensionality.
      intros k H3.
      unfold swap.
      repeat destruct excluded_middle_informative; subst; try tauto;
        destruct H3.
      + now apply not_succ_le in H4.
      + contradiction (not_succ_le (S m)).
        eauto using le_trans, le_succ.
    - rewrite M1.
      f_equal; unfold swap; repeat destruct excluded_middle_informative;
        subst; try tauto; try now contradiction (neq_succ (S m)).
      now apply lt_irrefl in H0.
  Qed.

  Theorem product_swap_0 : ∀ n f i j,
      0 ≤ i ≤ n → 0 ≤ j ≤ n → prod (swap _ _ i j f) 0 n = prod f 0 n.
  Proof.
    induction n using Induction.
    { intros f i j [H H0] [H1 H2].
      unfold prod.
      rewrite ? iterate_0, (le_antisymm i 0),
      (le_antisymm j 0), swap_refl; auto. }
    intros f i j [H H0] [H1 H2].
    apply le_lt_or_eq in H0 as [H0 | H0];
      apply le_lt_or_eq in H2 as [H2 | H2]; subst.
    - rewrite <-le_lt_succ, ? prod_succ, ? IHn in *;
        repeat split; auto using zero_le.
      repeat f_equal.
      unfold swap.
      destruct excluded_middle_informative; subst;
        try now apply not_succ_le in H0.
      destruct excluded_middle_informative; subst; auto.
      now apply not_succ_le in H2.
    - rewrite product_swap_upper_one; split; auto.
      rewrite le_lt_or_eq; tauto.
    - rewrite swap_sym, product_swap_upper_one; split; auto.
      rewrite le_lt_or_eq; tauto.
    - now rewrite swap_refl.
  Qed.

  Theorem product_swap : ∀ a b f i j,
      a ≤ i ≤ b → a ≤ j ≤ b → prod (swap _ _ i j f) a b = prod f a b.
  Proof.
    intros a b f i j [H H0] [H1 H2].
    unfold prod.
    destruct (classic (a ≤ b)) as [[c H3] | H3]; subst.
    2: { unfold iterate_with_bounds.
         destruct excluded_middle_informative; tauto. }
    rewrite ? iterate_shift.
    fold (prod (λ n : N, f (n + a)%N) 0 c).
    destruct H as [x H]; subst.
    destruct H1 as [y H1]; subst.
    rewrite ? (add_comm a) in *.
    apply O1_le_iff in H0, H2.
    erewrite <-product_swap_0.
    instantiate (2 := x).
    instantiate (1 := y).
    2: { split; eauto using zero_le. }
    2: { split; eauto using zero_le. }
    apply iterate_extensionality.
    intros k H.
    unfold swap.
    repeat destruct excluded_middle_informative; auto; try (now subst);
      [ contradict n | contradict n | contradict n1 ];
      rewrite ? (add_comm _ a) in e; now apply naturals.cancellation_add in e.
  Qed.

  Theorem product_bijection_0 : ∀ n f g,
      (∀ j, 0 ≤ j ≤ n → exists ! i, 0 ≤ i ≤ n ∧ f i = g j) →
      (∀ i, 0 ≤ i ≤ n → exists ! j, 0 ≤ j ≤ n ∧ f i = g j) →
      prod f 0 n = prod g 0 n.
  Proof.
    induction n using Induction.
    { intros f g H H0.
      unfold prod.
      rewrite ? iterate_0.
      destruct (H 0%N) as [j [[[H1 H2] H3] H4]]; try split; auto using le_refl.
      now replace 0%N with j at 1 by now apply le_antisymm. }
    intros f g H H0.
    assert (∀ i1 i2 j, 0 ≤ i1 ≤ S n → 0 ≤ i2 ≤ S n → 0 ≤ j ≤ S n →
                       f i1 = g j → f i2 = g j → i1 = i2) as E1.
    { intros i1 i2 j H1 H2 H3 H4 H5.
      destruct (H j) as [k [[[H6 H7] H8] H9]]; auto.
      replace i1 with k; replace i2 with k; try (apply H9; split); auto. }
    assert (∀ i j1 j2, 0 ≤ i ≤ S n → 0 ≤ j1 ≤ S n → 0 ≤ j2 ≤ S n →
                       f i = g j1 → f i = g j2 → j1 = j2) as E2.
    { intros i j1 j2 H1 H2 H3 H4 H5.
      destruct (H0 i) as [k [[[H6 H7] H8] H9]]; auto.
      replace j1 with k; replace j2 with k; try (apply H9, split); auto. }
    destruct (H (S n)) as [k [[H1 H2] H3]].
    { split; auto using le_refl, zero_le. }
    destruct (classic (k = S n)) as [H4 | H4]; subst.
    { rewrite ? prod_succ; auto using zero_le.
      f_equal; auto.
      apply IHn.
      - intros j [H4 H5].
        destruct (H j) as [k [[[H6 H7] H8] H9]]; eauto using le_trans, le_succ.
        exists k.
        repeat split; auto using zero_le.
        + rewrite le_lt_succ.
          apply le_lt_or_eq in H7 as [H7 | H7]; auto.
          subst.
          replace (S n) with j at 1 by eauto using le_trans, le_succ.
          now apply le_lt_succ.
        + intros x' [[H10 H11] H12].
          eauto using le_trans, le_succ.
      - intros i [H4 H5].
        destruct (H0 i) as [k [[[H6 H7] H8] H9]]; eauto using le_trans, le_succ.
        exists k.
        repeat split; auto using zero_le.
        + rewrite le_lt_succ.
          apply le_lt_or_eq in H7 as [H7 | H7]; auto.
          subst.
          replace (S n) with i at 1 by eauto using le_trans, le_succ.
          now apply le_lt_succ.
        + intros x' [[H10 H11] H12].
          eauto using le_trans, le_succ. }
    destruct H1 as [H1 H5].
    apply le_lt_or_eq in H5 as [H5 | H5]; try tauto.
    rewrite <-(product_swap _ _ f k (S n)); repeat split;
      eauto using le_refl, zero_le.
    2: { eapply lt_le_trans; eauto using le_refl. }
    rewrite ? prod_succ; auto using zero_le.
    f_equal.
    2: { unfold swap.
         repeat destruct excluded_middle_informative; subst; tauto. }
    apply IHn.
    - intros j [H6 H7].
      destruct (H j) as [l [[[H8 H9] H10] H11]]; eauto using le_trans, le_succ.
      apply le_lt_or_eq in H9 as [H9 | H9].
      + exists l.
        repeat split; auto using zero_le.
        * now apply le_lt_succ.
        * rewrite <-H10.
          unfold swap.
          repeat destruct excluded_middle_informative; auto; subst;
            try now apply lt_irrefl in H9.
          replace j with (S n) in H7; try now apply not_succ_le in H7.
          eapply (E2 k); repeat split;
            eauto using zero_le, le_refl, le_trans, le_succ.
          eapply lt_le_trans; eauto using le_refl.
        * intros x' [[H12 H13] H14].
          unfold swap in H14.
          repeat destruct excluded_middle_informative; subst.
          2: { now apply not_succ_le in H13. }
          2: { eapply (E1 _ _ j); repeat split;
               eauto using zero_le, le_refl, le_trans, le_succ.
               eapply lt_le_trans; eauto using le_refl. }
          replace l with (S n) in H9; try now contradiction (lt_irrefl (S n)).
          eapply (E1 _ _ j); repeat split;
            eauto using zero_le, le_refl, le_trans, le_succ.
          eapply lt_le_trans; eauto using le_refl.
      + subst.
        exists k.
        repeat split; auto using zero_le.
        * now apply le_lt_succ.
        * unfold swap.
          destruct excluded_middle_informative; tauto.
        * intros x' [[H9 H12] H13].
          unfold swap in H13.
          repeat destruct excluded_middle_informative; subst; auto;
            try now apply not_succ_le in H12.
          contradict n1.
          eapply (E1 _ _ j); repeat split;
            eauto using zero_le, le_refl, le_trans, le_succ.
    - intros i [H6 H7].
      destruct (classic (i = k)) as [H8 | H8]; subst; unfold swap.
      + destruct (H0 (S n)) as [l [[[H8 H9] H10] H11]];
          eauto using zero_le, le_refl.
        exists l.
        repeat split; auto using zero_le.
        * apply le_lt_succ.
          apply le_lt_or_eq in H9 as [H9 | H9]; auto.
          subst.
          contradict H4.
          eapply (E1 _ _ (S n)); repeat split; auto using zero_le, le_refl.
          eapply lt_le_trans; eauto using le_refl.
        * destruct excluded_middle_informative; tauto.
        * intros x' [[H12 H13] H14].
          apply H11.
          repeat split; eauto using le_trans, le_succ.
          repeat destruct excluded_middle_informative; tauto.
      + destruct (H0 i) as [l [[[H9 H10] H11] H12]];
          eauto using le_trans, le_succ.
        exists l.
        repeat split; auto.
        * apply le_lt_succ.
          apply le_lt_or_eq in H10 as [H10 | H10]; auto.
          subst.
          contradict H8.
          eapply (E1 _ _ (S n)); repeat split;
            eauto using zero_le, le_refl, le_trans, le_succ.
          eapply lt_le_trans; eauto using le_refl.
        * repeat destruct excluded_middle_informative; subst; try tauto.
          now apply not_succ_le in H7.
        * intros x' [[H13 H14] H15].
          apply H12.
          repeat split; eauto using le_trans, le_succ.
          repeat destruct excluded_middle_informative; subst; try tauto.
          now apply not_succ_le in H7.
  Qed.

  Theorem product_bijection : ∀ a b f g,
      (∀ j, a ≤ j ≤ b → exists ! i, a ≤ i ≤ b ∧ f i = g j) →
      (∀ i, a ≤ i ≤ b → exists ! j, a ≤ j ≤ b ∧ f i = g j) →
      prod f a b = prod g a b.
  Proof.
    intros a b f g H H0.
    unfold prod.
    destruct (classic (a ≤ b)) as [[c H1] | H1]; subst.
    2: { unfold iterate_with_bounds.
         destruct excluded_middle_informative; tauto. }
    rewrite ? iterate_shift.
    apply product_bijection_0.
    - intros j [H1 H2].
      destruct (H (j + a)%N) as [y [[[[z H3] H4] H5] H6]]; subst.
      split.
      + rewrite <-(add_0_l a) at 1.
        auto using O1_le.
      + rewrite (add_comm a).
        auto using O1_le.
      + exists z; rewrite ? (add_comm a) in *.
        repeat split; auto using zero_le.
        * now apply O1_le_iff in H4.
        * intros x' [[H3 H7] H8].
          apply (naturals.cancellation_add a).
          rewrite ? (add_comm a) in *.
          apply H6.
          repeat split; auto using O1_le.
          exists x'.
          now rewrite add_comm.
    - intros i [H1 H2].
      destruct (H0 (i + a)%N) as [y [[[[z H3] H4] H5] H6]]; subst.
      split.
      + rewrite <-(add_0_l a) at 1.
        auto using O1_le.
      + rewrite (add_comm a).
        auto using O1_le.
      + exists z; rewrite ? (add_comm a) in *.
        repeat split; auto using zero_le.
        * now apply O1_le_iff in H4.
        * intros x' [[H3 H7] H8].
          apply (naturals.cancellation_add a).
          rewrite ? (add_comm a) in *.
          apply H6.
          repeat split; auto using O1_le.
          exists x'.
          now rewrite add_comm.
  Qed.

  Theorem prod_sum_0 :
    ∀ k x f, prod (λ n, x^(f n)) 0 k = x^(sum_N (λ n, f n) 0 k).
  Proof.
    intros k x f.
    induction k using Induction.
    - unfold prod, sum_N.
      now rewrite ? iterate_0.
    - rewrite prod_succ, sum_N_succ, IHk, pow_add_r; auto using zero_le.
  Qed.

  Theorem prod_sum :
    ∀ a b x f, prod (λ n, x^(f n)) a b = x^(sum_N (λ n, f n) a b).
  Proof.
    intros a b x f.
    destruct (classic (a ≤ b)%N) as [[c H] | H]; subst.
    2: { unfold prod, sum_N, iterate_with_bounds.
         destruct excluded_middle_informative; try tauto.
         now rewrite pow_0_r. }
    unfold prod, sum_N.
    rewrite ? iterate_shift.
    now apply prod_sum_0.
  Qed.

  Theorem pow_neg_1_l : ∀ n, (-(1))^n = 1 ∨ (-(1))^n = -(1).
  Proof.
    induction n using Induction.
    - left.
      now rewrite pow_0_r.
    - destruct IHn as [H | H]; [ right | left ]; rewrite pow_succ_r, H; ring.
  Qed.

End Ring_theorems.
