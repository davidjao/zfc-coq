Require Export ordered_rings fields.
Set Warnings "-notation-overridden".

Record ordered_field :=
  mkOfield {
      field_OF : field where
      "a + b" :=
        (add_F field_OF a b)
          and "a * b" :=
        (mul_F field_OF a b)
          and "0" :=
          (zero_F field_OF)
          and "1" :=
            (one_F field_OF);
      lt_OF : elts (set_F field_OF) → elts (set_F field_OF) → Prop
      where "a < b" := (lt_OF a b);
      lt_trans_OF : ∀ a b c, a < b → b < c → a < c;
      T_OF : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ b < a) ∨
                    (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
                    (¬ a < b ∧ a ≠ b ∧ b < a);
      O1_OF : ∀ a b c, b < c → a + b < a + c;
      O2_OF : ∀ a b, 0 < a → 0 < b → 0 < a * b;
    }.

Section Ordered_field_theorems.

  Variable OF : ordered_field.

  Definition F := (field_OF OF).
  Notation "0" := (zero F).
  Notation "1" := (one F).
  Infix "+" := (add F).
  Infix "*" := (mul F).
  Notation "- a" := (neg a).
  Infix "-" := (sub F).
  Infix "^" := (pow F).
  Infix "/" := (div F).
  Definition lt := lt_OF OF : fields.F F → fields.F F → Prop.
  Infix "<" := lt.
  Definition lt_trans := lt_trans_OF OF : ∀ a b c, a < b → b < c → a < c.
  Definition O1 := O1_OF OF : ∀ a b c, b < c → a + b < a + c.
  Definition O2 := O2_OF OF : ∀ a b, 0 < a → 0 < b → 0 < a * b.
  Definition T := T_OF OF : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ b < a) ∨
                                   (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
                                   (¬ a < b ∧ a ≠ b ∧ b < a).
  Notation "a > b" := (b < a) (only parsing).
  Definition le a b := a < b ∨ a = b.
  Infix "≤" := le.
  Notation "x < y < z" := (x < y ∧ y < z).
  Notation "a ≥ b" := (b ≤ a) (only parsing).
  Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level).
  Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level).
  Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level).
  Notation "a '^-1' " := (inv F a) (at level 30, format "a '^-1'").

  Add Field generic_ordered_field :
    (mk_field (div F) (inv F)
              (mk_rt 0 1 (add F) (mul F) (sub F) (neg F) eq (A3 F) (A1 F) (A2 F)
                     (M3 F) (M1 F) (M2 F) (D1 F) (sub_neg F) (A4 F))
              (one_ne_0 F) (div_inv F) (M4 F)).

  Definition ordered_ring_from_field :=
    (mkOring (ring_from_field F) lt lt_trans T O1 O2 (one_ne_0_F F)).

  Theorem O4 : ∀ a, 0 < a → 0 < a^-1.
  Proof.
    intros x H.
    destruct (T 0 (x^-1)) as [[H0 _] | [[_ [H0 _]] | [_ [_ H0]]]];
      try tauto.
    - contradiction (one_ne_0 F).
      rewrite <-(inv_r _ x);
        auto using (ordered_rings.lt_neq ordered_ring_from_field).
      replace 0 with (x*0) by ring.
      now apply f_equal.
    - eapply (mul_neg_pos ordered_ring_from_field) in H0; eauto; simpl in *.
      rewrite inv_l in H0;
        auto using (ordered_rings.lt_neq ordered_ring_from_field).
      contradiction (lt_antisym ordered_ring_from_field 0 1).
      apply (ordered_rings.zero_lt_1 ordered_ring_from_field).
  Qed.

  Definition inv_lt := O4.

  Theorem lt_cross_inv : ∀ a b, 0 < a → 0 < b → a < b ↔ b^-1 < a^-1.
  Proof.
    intros a b H H0.
    split; intros H1.
    - apply (ordered_rings.O3 ordered_ring_from_field (a^-1 * b^-1)) in H1;
        simpl in *.
      + rewrite <-? M2_F, inv_l, (M1_F _ _ 1), M3_F, M1_F, <-M2_F, (M1_F _ a),
        inv_l, M1_F, M3_F in H1;
          auto using (ordered_rings.lt_neq ordered_ring_from_field).
      + apply (ordered_rings.O2_OR ordered_ring_from_field); now apply inv_lt.
    - apply (ordered_rings.O3 ordered_ring_from_field (a*b)) in H1; simpl in *;
        try now apply (ordered_rings.O2_OR ordered_ring_from_field).
      rewrite <-M2_F, (M1_F _ b), inv_l, M1_F, M3_F, M1_F, M2_F, inv_l, M3_F in H1;
        auto using (ordered_rings.lt_neq ordered_ring_from_field).
  Qed.

  Theorem lt_div : ∀ a b, 0 < a → a < b → 1 < b * a^-1.
  Proof.
    intros a b H H0.
    apply (ordered_rings.O3 ordered_ring_from_field (a^-1)) in H0; simpl in *.
    + rewrite inv_l, M1_F in H0;
        auto using (ordered_rings.lt_neq ordered_ring_from_field).
    + now apply inv_lt.
  Qed.

  Theorem pow_pos : ∀ a n, 0 < a → 0 < a^n.
  Proof.
    intros a n H.
    unfold pow.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description;
      try destruct a0.
    - rewrite integers.A3 in *.
      subst.
      now apply (pow_pos ordered_ring_from_field).
    - apply inv_lt in H.
      now apply (pow_pos ordered_ring_from_field).
    - exact (ordered_rings.zero_lt_1 ordered_ring_from_field).
  Qed.

  Theorem inv_lt_1 : ∀ a, 0 < a → 1 < a ↔ a^-1 < 1.
  Proof.
    split; intros H0.
    - destruct (T_OF _ 1 (a^-1))
        as [[H1 [H2 H3]] | [[H1 [H2 H3]] | [H1 [H2 H3]]]]; auto.
      + apply (lt_cross_mul ordered_ring_from_field 1 (a^-1) 1 a) in H1;
          auto using (ordered_rings.zero_lt_1 ordered_ring_from_field);
          simpl in *.
        rewrite inv_l, M3_F in H1;
          auto using (ordered_rings.lt_neq ordered_ring_from_field).
        contradiction (ordered_rings.lt_irrefl ordered_ring_from_field 1).
      + rewrite <-inv_inv, <-H2, inv_one in H0;
          auto using (ordered_rings.lt_neq ordered_ring_from_field).
        contradiction (ordered_rings.lt_irrefl ordered_ring_from_field 1).
    - destruct (T_OF _ 1 a)
        as [[H1 [H2 H3]] | [[H1 [H2 H3]] | [H1 [H2 H3]]]]; auto.
      + subst.
        rewrite inv_one in H0.
        contradiction (ordered_rings.lt_irrefl ordered_ring_from_field 1).
      + apply (lt_cross_mul ordered_ring_from_field (a^-1) 1 a 1) in H0;
          simpl in *; auto.
        * rewrite inv_l, M3_F in H0;
            auto using (ordered_rings.lt_neq ordered_ring_from_field).
          contradiction (ordered_rings.lt_irrefl ordered_ring_from_field 1).
        * now apply inv_lt.
  Qed.

  Theorem pow_gt_1 : ∀ a n, 1 < a → (0 < n)%Z → 1 < a^n.
  Proof.
    intros a n H H0.
    pose proof H0 as H1.
    apply lt_def in H1 as [c [H1 H2]].
    subst.
    rewrite integers.A3, <-pow_wf in *.
    assert (0 < c)%N as H2 by now rewrite <-INZ_lt.
    now apply (ordered_rings.pow_gt_1 ordered_ring_from_field).
  Qed.

  Theorem pow_lt_1 : ∀ a n, 1 < a → (n < 0)%Z → a^n < 1.
  Proof.
    intros a n H H0.
    assert (0 < a) as H1.
    { eapply (ordered_rings.lt_trans_OR ordered_ring_from_field); eauto.
        apply (ordered_rings.zero_lt_1 ordered_ring_from_field). }
    replace n with (--n)%Z by ring.
    rewrite neg_pow, <-inv_lt_1; simpl.
    - apply pow_gt_1; auto.
      now rewrite <-(ordered_rings.lt_neg_0 ℤ_order).
    - now apply pow_pos.
    - auto using (ordered_rings.lt_neq ordered_ring_from_field).
  Qed.

End Ordered_field_theorems.
