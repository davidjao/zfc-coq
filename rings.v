Require Export naturals Ring.
Set Warnings "-notation-bound-to-variable,-notation-overridden".

Record ring :=
  mkRing {
      set_R : set;
      zero_R : elts set_R where "0" := zero_R;
      one_R : elts set_R where "1" := one_R;
      add_R : elts set_R → elts set_R → elts set_R where "a + b" := (add_R a b);
      mul_R : elts set_R → elts set_R → elts set_R where "a * b" := (mul_R a b);
      neg_R : elts set_R → elts set_R where "- a" := (neg_R a);
      A3_R : ∀ a, 0 + a = a;
      A1_R : ∀ a b, a + b = b + a;
      A2_R : ∀ a b c, a + (b + c) = (a + b) + c;
      M3_R : ∀ a, 1 * a = a;
      M1_R : ∀ a b, a * b = b * a;
      M2_R : ∀ a b c, a * (b * c) = (a * b) * c;
      D1_R : ∀ a b c, (a + b) * c = a * c + b * c;
      A4_R : ∀ a, a + (-a) = 0;
    }.

Section Ring_theorems.

  Variable Ring : ring.
  Definition R := elts (set_R Ring).
  Definition zero := zero_R Ring : R.
  Definition one := one_R Ring : R.
  Definition add (a b : R) := (add_R Ring a b) : R.
  Definition mul (a b : R) := (mul_R Ring a b) : R.
  Definition neg (a : R) := (neg_R Ring a) : R.
  Delimit Scope Ring_scope with ring.
  Open Scope Ring_scope.
  Bind Scope Ring_Scope with R.
  Notation "0" := zero : Ring_scope.
  Notation "1" := one : Ring_scope.
  Infix "+" := add : Ring_scope.
  Infix "*" := mul : Ring_scope.
  Notation "- a" := (neg a) : Ring_scope.
  Definition A1 := (A1_R Ring) : ∀ a b, a + b = b + a.
  Definition A2 := (A2_R Ring) : ∀ a b c, a + (b + c) = (a + b) + c.
  Definition A3 := (A3_R Ring) : ∀ a, 0 + a = a.
  Definition A4 := (A4_R Ring) : ∀ a, a + -a = 0.
  Definition M1 := (M1_R Ring) : ∀ a b, a * b = b * a.
  Definition M2 := (M2_R Ring) : ∀ a b c, a * (b * c) = (a * b) * c.
  Definition M3 := (M3_R Ring) : ∀ a, 1 * a = a.
  Definition D1 := (D1_R Ring) : ∀ a b c, (a + b) * c = a * c + b * c.

  Definition IRS : R → set.
  Proof.
    intros a.
    exact (proj1_sig a).
  Defined.

  Coercion IRS : R >-> set.

  Definition sub (a b : R) := a + (-b) : R.

  Infix "-" := sub : Ring_scope.

  Lemma sub_is_neg : ∀ a b, a - b = a + -b.
  Proof.
    auto.
  Qed.

  Definition ringify :=
    (mk_rt 0 1 add mul sub neg eq A3 A1 A2 M3 M1 M2 D1 sub_is_neg A4).
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
    rewrite <-(A3 (-a)), <-H.
    ring.
  Qed.

  Theorem cancellation_add : ∀ a b c, a + b = a + c → b = c.
  Proof.
    intros a b c H.
    rewrite <-(A3 b), <-(A4 a), (A1 a), <-A2, H.
    ring.
  Qed.

  Lemma cancellation_ne0 : ∀ a b, a * b ≠ 0 → a ≠ 0 ∧ b ≠ 0.
  Proof.
    intros a b H; split; contradict H; subst; ring.
  Qed.

  Definition mul_right : R → set → set.
  Proof.
    intros a x.
    destruct (excluded_middle_informative (x ∈ (set_R Ring))).
    - exact (proj1_sig (mul_R _ (exist _ _ i : R) a)).
    - exact ∅.
  Defined.

  Lemma mul_right_lem : ∀ a b, mul_right a (proj1_sig b) = proj1_sig (b * a).
  Proof.
    intros a b.
    unfold mul_right.
    destruct excluded_middle_informative.
    - replace (exist _ (proj1_sig b) i) with b;
        auto; now apply set_proj_injective.
    - now destruct b.
  Qed.

  Definition pow : R → N → R.
  Proof.
    intros a b.
    assert (∀ x : set, x ∈ (set_R Ring) → mul_right a x ∈ (set_R Ring)) as H.
    { intros x H.
      unfold mul_right.
      destruct excluded_middle_informative; intuition.
      apply proj2_sig. }
    destruct
    (constructive_indefinite_description
       _ (function_construction (set_R Ring) (set_R Ring) (mul_right a) H))
      as [add_a [H0 [H1 H2]]].
    destruct (constructive_indefinite_description
                _ (recursion add_a _ _ (proj2_sig 1) H0 H1))
      as [pow_b [H3 [H4 [H5 H6]]]].
    assert (pow_b b ∈ (set_R Ring)) as H7.
    { rewrite <-H4.
      apply function_maps_domain_to_range.
      rewrite H3.
      unfold INS.
      apply proj2_sig. }
    exact (exist _ (pow_b b) H7).
  Defined.

  Infix "^" := pow : Ring_scope.

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
    rewrite <-S_is_succ, e5, e1, <-mul_right_lem; unfold INS;
      try now simpl; try now apply proj2_sig.
    rewrite <-e3.
    apply function_maps_domain_to_range.
    rewrite e2.
    apply proj2_sig.
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
    - now rewrite ? pow_succ_r, <-? M2, (M2 a), (M1 _ (b^c)), IHc, ? M2.
  Qed.

  Theorem pow_mul_r : ∀ a b c, a^(b*c) = (a^b)^c.
  Proof.
    induction c using Induction.
    - now rewrite naturals.mul_0_r, ? pow_0_r.
    - now rewrite mul_succ_r, pow_succ_r, pow_add_r, IHc.
  Qed.

  Section Iterated_op_construction.

    Variable op : R → R → R.
    Variable start : R.

    Variable f : function.
    Variable n : N.

    Infix "·" := op (at level 40, left associativity) : Ring_scope.

    Hypothesis dom_f : domain f = n.
    Hypothesis ran_f : range f = (set_R Ring).

    Theorem proto_iterop_exists :
      ∃ g, domain g = S n ∧ range g = (set_R Ring) ∧ (g 0%N) = start ∧
           ∀ m : N, m < n → ∃ r s t : R,
               (g (S m)) = r ∧ (g m) = s ∧ (f m) = t ∧ r = s · t.
    Proof.
      revert f dom_f ran_f.
      induction n using Induction; try now intuition.
      { destruct (function_construction 1%N (set_R Ring) (λ x, start))
          as [g [H [H0 H1]]].
        { intros a H.
          apply (proj2_sig start). }
        exists g.
        repeat split; eauto.
        - apply H1.
          apply lt_is_in, lt_succ.
        - intros m H2.
          apply lt_is_in in H2.
          unfold INS in H2.
          simpl in H2.
          contradiction (Empty_set_classification m). }
      intros f dom_f ran_f.
      clear n; rename n0 into n; rename IHn0 into IHn.
      destruct (function_construction n (range f) (λ x, (f x)))
        as [f_n [H [H0 H1]]].
      { intros a H.
        apply function_maps_domain_to_range.
        rewrite dom_f.
        pose proof succ_lt n as [H0 _].
        rewrite le_is_subset in H0.
        eauto. }
      destruct (IHn f_n) as [g_n [H2 [H3 [H4 H5]]]]; try congruence.
      assert (g_n n ∈ set_R Ring) as H6.
      { rewrite <-H3.
        apply function_maps_domain_to_range.
        rewrite H2.
        apply lt_is_in, succ_lt. }
      assert (f n ∈ set_R Ring) as H7.
      { rewrite <-ran_f.
        apply function_maps_domain_to_range.
        rewrite dom_f.
        apply lt_is_in, succ_lt. }
      destruct
      (function_construction
         (S (S n)) (set_R Ring)
         (λ x, if (excluded_middle_informative (x = S n))
               then (((exist _ _ H6) · (exist _ _ H7)) : R) else (g_n x)))
        as [g [H8 [H9 H10]]].
      { intros a H8.
        rewrite <-S_is_succ in H8.
        apply Pairwise_union_classification in H8 as [H8 | H8];
          destruct excluded_middle_informative.
        - subst.
          contradiction (no_quines (S n)).
        - rewrite <-H3.
          apply function_maps_domain_to_range.
          congruence.
        - apply (proj2_sig (((exist _ _ H6) · (exist _ _ H7)) : R)).
        - contradict n0.
          now apply Singleton_classification in H8. }
      exists g.
      repeat split; auto.
      { rewrite H10.
        - destruct excluded_middle_informative; auto.
          apply set_proj_injective in e.
          contradiction (PA4 n).
        - apply lt_is_in, lt_succ. }
      intros m H11.
      rewrite lt_is_in, <-S_is_succ in H11.
      apply Pairwise_union_classification in H11 as [H11 | H11].
      - apply lt_is_in in H11.
        pose proof H11 as H12.
        apply H5 in H12 as [r [s [t [H12 [H13 [H14 H15]]]]]].
        exists r, s, t.
        repeat split; auto.
        + rewrite H10.
          * destruct excluded_middle_informative; auto.
            apply set_proj_injective, PA5 in e.
            subst.
            contradiction (lt_irrefl n).
          * rewrite <-lt_is_in, <-S_lt.
            apply (lt_trans _ n); auto using succ_lt.
        + rewrite H10.
          * destruct excluded_middle_informative; auto.
            apply set_proj_injective in e.
            subst.
            contradiction (lt_antisym n (S n)).
            apply succ_lt.
          * rewrite <-lt_is_in.
            apply (lt_trans _ n); auto.
            apply (lt_trans _ (S n)); auto using succ_lt.
        + rewrite <-H1; auto.
          now apply lt_is_in.
      - rewrite Singleton_classification in H11.
        apply set_proj_injective in H11.
        subst.
        exists (((exist _ _ H6) · (exist _ _ H7)) : R), (exist _ _ H6 : R),
        (exist _ _ H7 : R).
        repeat split; auto.
        + rewrite H10.
          * now destruct excluded_middle_informative.
          * rewrite <-lt_is_in, <-S_lt.
            apply succ_lt.
        + rewrite H10.
          * destruct excluded_middle_informative; auto.
            apply set_proj_injective in e.
            contradiction (lt_irrefl n).
            rewrite e at 2.
            apply succ_lt.
          * rewrite <-lt_is_in.
            apply (lt_trans _ (S n)); auto using succ_lt.
    Qed.

    Definition proto_iterop : R.
    Proof.
      destruct (constructive_indefinite_description _ proto_iterop_exists)
        as [g [H [H0 [H1 H2]]]].
      assert (n ∈ domain g) as H3.
      { rewrite H, <-lt_is_in.
      apply succ_lt. }
      assert (∃ r : R, g n = r) as H4.
      { assert (g n ∈ (set_R Ring)).
        { rewrite <-H0.
          now apply function_maps_domain_to_range. }
        now exists (exist _ _ H4 : R). }
      destruct (constructive_indefinite_description _ H4) as [r H5].
      exact r.
    Defined.

  End Iterated_op_construction.

  Section Iterated_op.

    Variable op : R → R → R.
    Variable start : R.

    Variable f : N → R.

    Infix "·" := op (at level 40, left associativity) : Ring_scope.

    Definition iterated_op : N → R.
    Proof.
      intros n.
      assert (∀ a, a ∈ n → (λ x : set, (functionify _ _ f x))
                             a ∈ set_R Ring) as H.
      { intros a H.
        unfold functionify.
        destruct constructive_indefinite_description as [f' [H0 [H1 H2]]].
        rewrite <-H1.
        apply function_maps_domain_to_range.
        rewrite H0.
        eapply elements_of_naturals_are_naturals; eauto; apply (proj2_sig n). }
      destruct (constructive_indefinite_description
                  _ (function_construction n (set_R Ring)
                                           (λ x, (functionify _ _ f x)) H))
        as [h [H0 [H1 H2]]].
      destruct (constructive_indefinite_description
                  _ (proto_iterop_exists op start h n H0 H1))
        as [g [H3 [H4 [H5 H6]]]].
      assert (∃ r : R, g n = r) as H7.
      { assert (g n ∈ (set_R Ring)).
        { rewrite <-H4.
          apply function_maps_domain_to_range.
          rewrite H3.
          apply lt_is_in, succ_lt. }
        now exists (exist _ _ H7 : R). }
      destruct (constructive_indefinite_description _ H7) as [r H8].
      exact r.
    Defined.

    Theorem iterated_op_0 : iterated_op 0 = start.
    Proof.
      unfold iterated_op.
      repeat (destruct constructive_indefinite_description;
              repeat destruct a).
      unfold IRS in *.
      apply set_proj_injective.
      congruence.
    Qed.

    Theorem iterated_op_succ : ∀ n, iterated_op (S n) = iterated_op n · (f n).
    Proof.
      induction n using Induction.
      - unfold iterated_op.
        repeat (destruct constructive_indefinite_description;
                repeat destruct a).
        destruct (e5 0%N) as [r [s [t [H [H0 [H1 H2]]]]]]; auto using succ_lt.
        unfold IRS in *.
        replace x1 with r.
        2: { apply set_proj_injective.
             now rewrite <-H, e6. }
        replace x4 with s.
        2: { apply set_proj_injective.
             now rewrite <-H0, e4, <-e12, e14. }
        replace (f 0) with t; auto.
        apply set_proj_injective.
        rewrite <-H1, e1.
        + unfold functionify.
          destruct constructive_indefinite_description.
          destruct a as [H3 [H4 H5]].
          now rewrite H5.
        + apply lt_is_in, succ_lt.
      - rewrite IHn.
        unfold iterated_op.
        repeat (destruct constructive_indefinite_description;
                repeat destruct a).
        assert (∀ m, m < n → x m = x2 m) as E.
        { intros m H.
          rewrite e1, e9; auto.
          - now apply lt_is_in.
          - apply lt_is_in.
            eauto using lt_is_in, lt_trans, succ_lt. }
        assert (∀ m, m < n → x0 m = x3 m) as E0.
        { induction m using Induction; intros H0; try congruence.
          assert (m < n) by eauto using lt_trans, succ_lt.
          apply IHm in H as H1.
          apply E in H as H2.
          assert (m < S (S n)) by eauto using lt_trans, succ_lt.
          apply e13 in H as [r [s [t [H4 [H5 [H6 H7]]]]]].
          apply e5 in H3 as [r' [s' [t' [H8 [H9 [H10 H11]]]]]].
          rewrite H4, H8, H7, H11.
          f_equal.
          unfold IRS in *.
          replace s with s'.
          replace t with t'; auto.
          - apply set_proj_injective.
            congruence.
          - apply set_proj_injective.
            congruence. }
        destruct (e5 (S n)) as [r [s [t [H [H0 [H1 H2]]]]]]; auto using succ_lt.
        unfold IRS in *.
        assert (t = (f (S n))).
        { apply set_proj_injective.
          rewrite <-H1, e1.
          - unfold functionify.
            destruct constructive_indefinite_description.
            destruct a as [H3 [H4 H5]].
            now rewrite H5.
          - rewrite <-lt_is_in, <-S_lt.
            apply succ_lt. }
        destruct (e5 n)
          as [r' [s' [t' [H4 [H5 [H6 H7]]]]]]; eauto using lt_trans, succ_lt.
        assert (r' = s).
        { apply set_proj_injective.
          congruence. }
        subst.
        assert (t' = f n).
        { apply set_proj_injective.
          rewrite <-H6, e1.
          - unfold functionify.
            destruct constructive_indefinite_description.
            destruct a as [H7 [H8 H9]].
            now rewrite H9.
          - rewrite <-lt_is_in.
            eauto using lt_trans, succ_lt. }
        assert (s' = x4).
        { apply set_proj_injective.
          rewrite <-e14.
          destruct (classic (n = 0%N)).
          { subst.
            congruence. }
          apply succ_0 in H3 as [k H3].
          subst.
          destruct (e13 k) as [r'' [s'' [t'' [H7 [H8 [H9 H10]]]]]];
            auto using succ_lt.
          rewrite H7, H10, <-H5.
          rewrite <-E0 in H8; auto using succ_lt.
          rewrite <-E in H9; auto using succ_lt.
          destruct (e5 k) as [r''' [s''' [t''' [H11 [H12 [H13 H14]]]]]];
            eauto using lt_trans, succ_lt.
          rewrite H11, H14.
          replace s'' with s'''; replace t'' with t''';
            auto; apply set_proj_injective; congruence. }
        apply set_proj_injective.
        rewrite <-e6, H.
        congruence.
    Qed.

  End Iterated_op.

  Definition iterate_with_bounds : (R → R → R) → (N → R) → R → N → N → R.
  Proof.
    intros op f start a b.
    destruct (excluded_middle_informative (a ≤ b)).
    - destruct (constructive_indefinite_description _ l) as [c H].
      exact (iterated_op op (f a) (λ x, f (a + x + 1)%N) c).
    - exact start.
  Defined.

  Theorem iterate_0 : ∀ op f start a, iterate_with_bounds op f start a a = f a.
  Proof.
    intros op f start a.
    unfold iterate_with_bounds.
    destruct excluded_middle_informative.
    - destruct constructive_indefinite_description.
      rewrite <-(add_0_r a) in e at 2.
      apply naturals.cancellation_add in e.
      subst.
      now rewrite iterated_op_0.
    - contradiction n.
      exists 0%N.
      now rewrite add_0_r.
  Qed.

  Theorem iterate_succ : ∀ op f start a b,
      a ≤ b → iterate_with_bounds op f start a (S b)
              = op (iterate_with_bounds op f start a b) (f (S b)).
  Proof.
    intros op f start a b H.
    unfold iterate_with_bounds.
    destruct excluded_middle_informative.
    - destruct constructive_indefinite_description.
      destruct excluded_middle_informative; try tauto.
      destruct constructive_indefinite_description.
      replace x with (S x0).
      + now rewrite iterated_op_succ, e0, add_1_r.
      + apply (naturals.cancellation_add a).
        now rewrite add_succ_r, e0, e.
    - contradict n.
      destruct H as [c H].
      exists (S c).
      now rewrite add_succ_r, H.
  Qed.

  Theorem iterate_extensionality : ∀ op f g start a b,
      (∀ k, a ≤ k ≤ b → f k = g k) →
      iterate_with_bounds op f start a b =
      iterate_with_bounds op g start a b.
  Proof.
    intros op f g start a b H.
    destruct (classic (a ≤ b)) as [[c H0] | H0].
    2: { unfold iterate_with_bounds.
         destruct excluded_middle_informative; tauto. }
    subst.
    induction c using Induction.
    - rewrite add_0_r, ? iterate_0.
      apply H.
      rewrite add_0_r.
      split; auto using le_refl.
    - rewrite add_succ_r, ? iterate_succ; try now (exists c).
      rewrite IHc, H; auto.
      + split.
        * exists (S c).
          now rewrite add_succ_r.
        * exists 0%N.
          now rewrite add_0_r, add_succ_r.
      + intros k [H0 [d H1]].
        rewrite H; auto.
        split; auto.
        exists (S d).
        rewrite ? add_succ_r.
        now f_equal.
  Qed.

  Theorem iterate_lower : ∀ op f start a c,
      (∀ x y z, op x (op y z) = op (op x y) z) →
      iterate_with_bounds op f start a (S a+c) =
      op (f a) (iterate_with_bounds op f start (S a) (S a+c)).
  Proof.
    intros op f start a c H.
    induction c using Induction.
    - rewrite ? add_0_r, iterate_succ, ? iterate_0; auto using le_refl.
    - rewrite ? add_succ_r, ? iterate_succ, IHc, H; auto.
      + now (exists c).
      + exists (c+1)%N.
        now rewrite add_assoc, (add_comm a), add_1_r, <-add_succ_r, add_comm.
  Qed.

  Theorem iterate_shift : ∀ op f start a c,
      iterate_with_bounds op f start a (a+c) =
      iterate_with_bounds op (λ n, (f (n+a)%N)) start 0 c.
  Proof.
    intros op f start a c.
    induction c using Induction.
    - now rewrite add_0_r, ? iterate_0, add_0_l.
    - rewrite add_succ_r, ? iterate_succ, IHc, <-add_succ_r; auto using zero_le.
      + do 2 f_equal.
        now rewrite add_comm.
      + now (exists c).
  Qed.

  Theorem iterate_1 : ∀ op f start,
      iterate_with_bounds op f start 0 1 = op (f 0%N) (f 1%N).
  Proof.
    intros op f start.
    unfold naturals.one.
    rewrite iterate_succ, iterate_0; auto using zero_le.
  Qed.

  Theorem iterate_2 : ∀ op f start,
      iterate_with_bounds op f start 0 2 = op (op (f 0%N) (f 1%N)) (f 2).
  Proof.
    intros op f start.
    rewrite iterate_succ, iterate_1; auto using zero_le.
  Qed.

  Definition sum f a b := iterate_with_bounds add f 0 a b.
  Definition prod f a b := iterate_with_bounds mul f 1 a b.

  Theorem iterate_succ_lower_limit : ∀ op f start a b,
      a ≤ S b → op start (f (S b)) = f (S b) →
      iterate_with_bounds op f start a (S b) =
      op (iterate_with_bounds op f start a b) (f (S b)).
  Proof.
    intros op f start a b H H0.
    destruct (classic (a ≤ b)) as [H1 | H1]; auto using iterate_succ.
    assert (a = S b).
    { destruct H as [c H].
      apply NNPP.
      contradict H1.
      assert (c ≠ 0%N).
      { contradict H0.
        subst.
        now rewrite add_0_r in H. }
      apply succ_0 in H2 as [d H2].
      subst.
      rewrite add_succ_r in H.
      apply PA5 in H.
      now exists d. }
    subst.
    rewrite iterate_0.
    unfold iterate_with_bounds.
    destruct excluded_middle_informative; auto.
    exfalso.
    rewrite le_not_gt in l.
    contradict l.
    apply succ_lt.
  Qed.

  Theorem sum_succ : ∀ f a b,
      a ≤ S b → (sum f a (S b)) = (sum f a b) + (f (S b)).
  Proof.
    intros f a b H.
    apply iterate_succ_lower_limit; auto.
    now rewrite A3.
  Qed.

  Theorem prod_succ : ∀ f a b,
      a ≤ S b → (prod f a (S b)) = (prod f a b) * (f (S b)).
  Proof.
    intros f a b H.
    apply iterate_succ_lower_limit; auto.
    now rewrite M3.
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
         repeat destruct excluded_middle_informative; try tauto.
         now rewrite mul_0_r. }
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
         repeat destruct excluded_middle_informative; try tauto.
         now rewrite M3. }
    subst.
    induction c using Induction.
    - rewrite add_0_r.
      unfold prod.
      now rewrite ? iterate_0.
    - rewrite add_succ_r, ? prod_succ, IHc; try ring;
        exists (c+1)%N; now rewrite add_1_r, add_succ_r.
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
    - rewrite ? (add_comm a), sub_abba, ? pow_succ_r in *.
      rewrite ? (add_comm _ a), add_succ_r.
      rewrite ? prod_succ;
        try (exists (d+1)%N; rewrite <-? add_1_r; ring).
      rewrite (add_comm a), <-IHd.
      ring.
  Qed.

  Theorem sum_of_0 : ∀ d, (sum (λ n, 0) 0 d) = 0.
  Proof.
    induction d using Induction.
    - unfold sum.
      now rewrite iterate_0.
    - rewrite sum_succ, IHd; auto using zero_le.
      ring.
  Qed.

  Definition INR (n : N) := sum (λ n, 1) 1 n.
  Coercion INR : N >-> R.

  Theorem INR_add : ∀ a b : N, ((a + b)%N : R) = (a : R) + (b : R).
  Proof.
    intros a b.
    unfold INR.
    induction b using Induction.
    { unfold sum at 3.
      unfold iterate_with_bounds.
      destruct excluded_middle_informative.
      - exfalso.
        apply le_not_gt in l.
        eauto using succ_lt.
      - now rewrite A1, A3, naturals.add_0_r. }
    rewrite add_succ_r, ? sum_succ, IHb; try ring;
      [ exists b | exists (a+b)%N ];
      now rewrite <-add_1_r, naturals.add_comm.
  Qed.

  Section Subring_construction.

    Variable S : set.
    Hypothesis subset : S ⊂ (set_R Ring).
    Definition is_subring S := (∀ a b : R, a ∈ S → b ∈ S → a + b ∈ S) ∧
                               (∀ a b : R, a ∈ S → b ∈ S → a * b ∈ S) ∧
                               (∀ a : R, a ∈ S → -a ∈ S) ∧
                               (1 ∈ S).
    Hypothesis SR : is_subring S.
    Definition sub_R := elts S.

    Definition ISR : sub_R → R.
    Proof.
      intros x.
      pose proof (proj2_sig x) as H; simpl in H.
      apply subset in H.
      exact (exist _ _ H).
    Defined.

    Coercion ISR : sub_R >-> R.

    Definition sub_add : sub_R → sub_R → sub_R.
    Proof.
      intros a b.
      assert (a + b ∈ S) as H.
      { destruct SR as [H [H0 [H1 H2]]].
        apply H; try apply (proj2_sig a); apply (proj2_sig b). }
      exact (exist _ _ H).
    Defined.

    Definition sub_mul : sub_R → sub_R → sub_R.
    Proof.
      intros a b.
      assert (a * b ∈ S) as H.
      { destruct SR as [H [H0 [H1 H2]]].
        apply H0; try apply (proj2_sig a); apply (proj2_sig b). }
      exact (exist _ _ H).
    Defined.

    Definition sub_neg : sub_R → sub_R.
    Proof.
      intros a.
      assert (-a ∈ S) as H.
      { destruct SR as [H [H0 [H1 H2]]].
        apply H1; try apply (proj2_sig a); apply (proj2_sig b). }
      exact (exist _ _ H).
    Defined.

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

    Theorem ISR_eq : ∀ a b, ISR a = ISR b → a = b.
    Proof.
      intros [a A] [b B] H.
      unfold ISR in H.
      simpl in *.
      apply set_proj_injective.
      now assert (proj1_sig (exist (λ x : set, x ∈ set_R Ring) a (subset a A)) =
                  proj1_sig (exist (λ x : set, x ∈ set_R Ring) b (subset b B)))
        as H0 by now rewrite H.
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
      rewrite <-(A4 (1%ring)).
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

  Definition subring_of_arbitrary_set (S : set) : ring.
  Proof.
    destruct (excluded_middle_informative (S ⊂ set_R Ring)).
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

    Hypothesis subset : S ⊂ (set_R Ring).

    Definition subset_generated_by S :=
      ⋂ {s in P (set_R Ring) | S ⊂ s ∧ is_subring s}.

    Lemma generated_nonempty : {s in P (set_R Ring) | S ⊂ s ∧ is_subring s} ≠ ∅.
    Proof.
      apply Nonempty_classification.
      exists (set_R Ring).
      rewrite Specify_classification, Powerset_classification.
      repeat split; auto using Set_is_subset.
      - intros a b H H0.
        apply (proj2_sig (a + b)).
      - intros a b H H0.
        apply (proj2_sig (a * b)).
      - intros a H.
        apply (proj2_sig (-a)).
      - apply (proj2_sig 1).
    Qed.

    Lemma generated_subset : subset_generated_by S ⊂ (set_R Ring).
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
        assert (S ∈ {s in P (set_R Ring) | S ⊂ s ∧ is_subring s}) as H1; auto.
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
    Hypothesis subset_S : S ⊂ set_R Ring.
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
    Hypothesis subset_S : S ⊂ set_R Ring.
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
      rewrite sum_succ; auto using zero_le.
      rewrite <-(A3 a) at 1.
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
      + destruct excluded_middle_informative.
        * contradict H0.
          congruence.
        * ring.
      + destruct H as [c H].
        rewrite <-H in H0.
        assert (c ≠ 0%N) as H1.
        { contradict H0.
          ring [H0]. }
        apply succ_0 in H1 as [d H1].
        exists d.
        rewrite H1, add_succ_r in H.
        now apply PA5.
  Qed.

End Ring_theorems.
