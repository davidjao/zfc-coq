Require Export naturals Ring.

Record ring :=
  mkRing {
      set_R : set;
      zero_R : elts set_R (*where "0" := zero_R*);
      one_R : elts set_R (*where "1" := one_R*);
      add_R : elts set_R → elts set_R → elts set_R where "a + b" := (add_R a b);
      mul_R : elts set_R → elts set_R → elts set_R where "a * b" := (mul_R a b);
      neg_R : elts set_R → elts set_R where "- a" := (neg_R a);
      A3_R : ∀ a, zero_R + a = a;
      A1_R : ∀ a b, a + b = b + a;
      A2_R : ∀ a b c, a + (b + c) = (a + b) + c;
      M3_R : ∀ a, one_R * a = a;
      M1_R : ∀ a b, a * b = b * a;
      M2_R : ∀ a b c, a * (b * c) = (a * b) * c;
      D1_R : ∀ a b c, (a + b) * c = a * c + b * c;
      A4_R : ∀ a, a + (-a) = zero_R;
    }.

(* Definition integers := mkRing _ zero one add mul neg A3 A1 A2 M3 M1 M2 D1 A4. *)

Section Ring_theorems.
  Variable R : ring.

  Notation "0" := (zero_R R).
  Notation "1" := (one_R R).

  Infix "+" := (add_R R).
  Infix "*" := (mul_R R).

  Notation "- a" := (neg_R R a).

  Definition sub_R a b := a + (-b).

  Infix "-" := sub_R.

  Lemma sub_neg_R : ∀ a b, a - b = a + -b.
  Proof.
    auto.
  Qed.

  Add Ring generic_ring :
    (mk_rt 0 1 (add_R R) (mul_R R) sub_R (neg_R R) eq (A3_R R) (A1_R R)
           (A2_R R) (M3_R R) (M1_R R) (M2_R R) (D1_R R) sub_neg_R (A4_R R)).

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

  Definition divide x y := exists z, y = z * x.

  Notation "x ｜ y" := (divide x y) (at level 60, format "x '｜' y").

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
  Infix "~" := assoc (at level 70).
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

  Theorem cancellation_0_add : ∀ a b, a + b = 0 → b = -a.
  Proof.
    intros a b H.
    rewrite <-(A3_R _ (-a)), <-H.
    ring.
  Qed.

  Theorem cancellation_add : ∀ a b c, a + b = a + c → b = c.
  Proof.
    intros a b c H.
    rewrite <-(A3_R _ b), <-(A4_l a), <-A2_R, H.
    ring.
  Qed.

  Lemma cancellation_ne0 : ∀ a b, a * b ≠ 0 → a ≠ 0 ∧ b ≠ 0.
  Proof.
    intros a b H; split; contradict H; subst; ring.
  Qed.

  Definition mul_right : elts (set_R R) → set → set.
  Proof.
    intros a x.
    destruct (excluded_middle_informative (x ∈ (set_R R))).
    - exact (proj1_sig (mul_R _ (exist _ _ i : elts (set_R R)) a)).
    - exact ∅.
  Defined.

  Theorem mul_right_lemma :
    ∀ a b : elts (set_R R), mul_right a (proj1_sig b) = proj1_sig (b * a).
  Proof.
    intros a b.
    unfold mul_right.
    destruct excluded_middle_informative.
    - replace (exist _ (proj1_sig b) i) with b;
        auto; now apply set_proj_injective.
    - now destruct b.
  Qed.

  Definition pow : (elts (set_R R)) → N → (elts (set_R R)).
  Proof.
    intros a b.
    assert (∀ x : set, x ∈ (set_R R) → mul_right a x ∈ (set_R R)) as H.
    { intros x H.
      unfold mul_right.
      destruct excluded_middle_informative; intuition.
      apply proj2_sig. }
    destruct (constructive_indefinite_description
                _ (function_construction (set_R R) (set_R R) (mul_right a) H))
      as [add_a [H0 [H1 H2]]].
    destruct (constructive_indefinite_description
                _ (recursion add_a _ _ (proj2_sig 1) H0 H1))
      as [pow_b [H3 [H4 [H5 H6]]]].
    assert (pow_b b ∈ (set_R R)) as H7.
    { rewrite <-H4.
      apply function_maps_domain_to_range.
      rewrite H3.
      unfold INS.
      apply proj2_sig. }
    exact (exist _ (pow_b b) H7).
  Defined.

  Infix "^" := pow.

  Theorem pow_0_r : ∀ x, x^0 = 1.
  Proof.
    intros x.
    unfold pow.
    repeat (destruct constructive_indefinite_description; repeat destruct a).
    now apply set_proj_injective.
  Qed.

  Theorem pow_succ_r : ∀ x y, x^(S y) = x^y * x.
  Proof.
    intros x y.
    unfold pow.
    repeat (destruct constructive_indefinite_description; repeat destruct a).
    apply set_proj_injective.
    simpl.
    rewrite <-S_is_succ, e5, e1, <-mul_right_lemma; unfold INS;
      try now simpl; try now apply proj2_sig.
    rewrite <-e3.
    apply function_maps_domain_to_range.
    rewrite e2.
    apply proj2_sig.
  Qed.

  Theorem pow_1_r : ∀ x, x^1 = x.
  Proof.
    intros x.
    now rewrite pow_succ_r, pow_0_r, M3_R.
  Qed.

  Theorem pow_1_l : ∀ x, 1^x = 1.
  Proof.
    induction x using Induction.
    - now rewrite pow_0_r.
    - now rewrite pow_succ_r, IHx, M3_R.
  Qed.

  Theorem pow_0_l : ∀ x, x ≠ 0%N → 0^x = 0.
  Proof.
    induction x using Induction; intros H; try tauto.
    now rewrite pow_succ_r, mul_0_r.
  Qed.

  Theorem pow_add_r : ∀ a b c, a^(b+c) = a^b * a^c.
  Proof.
    induction c using Induction.
    - now rewrite add_0_r, pow_0_r, M3_r.
    - now rewrite add_succ_r, ? pow_succ_r, IHc, M2_R.
  Qed.

  Theorem pow_mul_l : ∀ a b c, (a*b)^c = a^c * b^c.
  Proof.
    induction c using Induction.
    - now rewrite ? pow_0_r, M3_R.
    - now rewrite ? pow_succ_r, <-? M2_R, (M2_R _ a),
      (M1_R _ _ (b^c)), IHc, ? M2_R.
  Qed.

  Theorem pow_mul_r : ∀ a b c, a^(b*c) = (a^b)^c.
  Proof.
    induction c using Induction.
    - now rewrite naturals.mul_0_r, ? pow_0_r.
    - now rewrite mul_succ_r, pow_succ_r, pow_add_r, IHc.
  Qed.

End Ring_theorems.
