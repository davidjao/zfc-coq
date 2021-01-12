Require Export naturals Ring.
Set Warnings "-notation-bound-to-variable".

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
  Notation "0" := zero.
  Notation "1" := one.
  Infix "+" := add.
  Infix "*" := mul.
  Notation "- a" := (neg a).
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

  Infix "-" := sub.

  Lemma sub_neg : ∀ a b, a - b = a + -b.
  Proof.
    auto.
  Qed.

  Add Ring generic_ring :
    (mk_rt 0 1 add mul sub neg eq A3 A1 A2 M3 M1 M2 D1 sub_neg A4).

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

  Definition pow : (elts (set_R Ring)) → N → (elts (set_R Ring)).
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

    Infix "·" := op (at level 40, left associativity).

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
        + apply H1.
          apply lt_is_in, lt_succ.
        + intros m H2.
          apply lt_is_in in H2.
          unfold INS in H2.
          simpl in H2.
          contradiction (Empty_set_classification m). }
      intros f dom_f ran_f.
      clear n; rename n0 into n; rename IHn0 into IHn.
      destruct (function_construction n (range f) (λ x, (f x))) as [f_n [H [H0 H1]]].
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
      - rewrite H10.
        + destruct excluded_middle_informative; auto.
          apply set_proj_injective in e.
          contradiction (PA4 n).
        + apply lt_is_in, lt_succ.
      - intros m H11.
        rewrite lt_is_in, <-S_is_succ in H11.
        apply Pairwise_union_classification in H11 as [H11 | H11].
        + apply lt_is_in in H11.
          pose proof H11 as H12.
          apply H5 in H12 as [r [s [t [H12 [H13 [H14 H15]]]]]].
          exists r, s, t.
          repeat split; auto.
          * rewrite H10.
            -- destruct excluded_middle_informative; auto.
               apply set_proj_injective, PA5 in e.
               subst.
               contradiction (lt_irrefl n).
            -- rewrite <-lt_is_in, <-S_lt.
               apply (lt_trans _ n); auto using succ_lt.
          * rewrite H10.
            -- destruct excluded_middle_informative; auto.
               apply set_proj_injective in e.
               subst.
               contradiction (lt_antisym n (S n)).
               apply succ_lt.
            -- rewrite <-lt_is_in.
               apply (lt_trans _ n); auto.
               apply (lt_trans _ (S n)); auto using succ_lt.
          * rewrite <-H1; auto.
            now apply lt_is_in.
        + rewrite Singleton_classification in H11.
          apply set_proj_injective in H11.
          subst.
          exists (((exist _ _ H6) · (exist _ _ H7)) : R), (exist _ _ H6 : R),
          (exist _ _ H7 : R).
          repeat split; auto.
          * rewrite H10.
            -- now destruct excluded_middle_informative.
            -- rewrite <-lt_is_in, <-S_lt.
               apply succ_lt.
          * rewrite H10.
            -- destruct excluded_middle_informative; auto.
               apply set_proj_injective in e.
               contradiction (lt_irrefl n).
               rewrite e at 2.
               apply succ_lt.
            -- rewrite <-lt_is_in.
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

    Infix "·" := op (at level 40, left associativity).

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
        replace x4 with s.
        replace (f 0) with t; auto.
        + apply set_proj_injective.
          rewrite <-H1, e1.
          * unfold functionify.
            destruct constructive_indefinite_description.
            destruct a as [H3 [H4 H5]].
            now rewrite H5.
          * apply lt_is_in, succ_lt.
        + apply set_proj_injective.
          now rewrite <-H0, e4, <-e12, e14.
        + apply set_proj_injective.
          now rewrite <-H, e6.
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

  Definition sum f a b := iterate_with_bounds add f 0 a b.
  Definition prod f a b := iterate_with_bounds mul f 1 a b.

End Ring_theorems.
