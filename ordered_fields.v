Set Warnings "-notation-overridden,-ambiguous-paths".
Require Export ordered_rings fields.

Record ordered_field :=
  mkOF {
      field : field where
      "a + b" :=
        (rings.add (fields.ring field) a b)
          and "a * b" :=
        (rings.mul (fields.ring field) a b)
          and "0" :=
          (rings.zero (fields.ring field))
          and "1" :=
            (rings.one (fields.ring field));
      lt : elts (Rset (fields.ring field)) → elts (Rset (fields.ring field))
              → Prop
      where "a < b" := (lt a b);
      lt_trans : ∀ a b c, a < b → b < c → a < c;
      T : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ b < a) ∨
                    (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
                    (¬ a < b ∧ a ≠ b ∧ b < a);
      O1 : ∀ a b c, b < c → a + b < a + c;
      O2 : ∀ a b, 0 < a → 0 < b → 0 < a * b;
    }.

Section Ordered_field_theorems.

  Variable OF : ordered_field.

  Notation Field := (field OF).
  Notation F := (elts (Rset (fields.ring Field))).
  Notation "0" := (rings.zero (fields.ring Field)).
  Notation "1" := (rings.one (fields.ring Field)).
  Infix "+" := (rings.add (fields.ring Field)).
  Infix "*" := (rings.mul (fields.ring Field)).
  Infix "-" := (rings.sub (fields.ring Field)).
  Notation "- a" := (rings.neg (fields.ring Field) a).
  Infix "^" := (fields.pow Field).
  Infix "/" := (fields.inv Field).
  Infix "<" := (lt OF).
  Notation "a > b" := (b < a) (only parsing).
  Definition le a b := a < b ∨ a = b.
  Infix "≤" := le.
  Notation "x < y < z" := (x < y ∧ y < z).
  Notation "a ≥ b" := (b ≤ a) (only parsing).
  Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level).
  Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level).
  Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level).
  Notation "a '^-1' " := (inv (field OF) a) (at level 30, format "a '^-1'").

  Add Field generic_ordered_field : (fieldify Field).

  Definition ordered_ring_from_field :=
    (mkOR (ring_from_field Field) (lt _) (lt_trans _)
          (T _) (O1 _) (O2 _) (one_ne_0 _)).

  Theorem O4 : ∀ a, 0 < a → 0 < a^-1.
  Proof.
    intros x H.
    destruct (T _ 0 (x^-1)) as [[H0 _] | [[_ [H0 _]] | [_ [_ H0]]]];
      try tauto.
    - contradiction (one_ne_0 Field).
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
      + rewrite <-? rings.M2, inv_l, (rings.M1 _ _ 1), rings.M3, rings.M1,
        <-rings.M2, inv_r, rings.M1, rings.M3 in H1;
          auto using (ordered_rings.lt_neq ordered_ring_from_field).
      + apply (ordered_rings.O2 ordered_ring_from_field); now apply inv_lt.
    - apply (ordered_rings.O3 ordered_ring_from_field (a*b)) in H1; simpl in *;
        try now apply (ordered_rings.O2 ordered_ring_from_field).
      rewrite <-rings.M2, inv_r, rings.M3_r, rings.M1, rings.M2, inv_l, rings.M3
        in H1; auto using (ordered_rings.lt_neq ordered_ring_from_field).
  Qed.

  Theorem lt_div : ∀ a b, 0 < a → a < b → 1 < b * a^-1.
  Proof.
    intros a b H H0.
    apply (ordered_rings.O3 ordered_ring_from_field (a^-1)) in H0; simpl in *.
    + rewrite inv_l, rings.M1 in H0;
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
    - destruct (T _ 1 (a^-1)) as [[H1 _] | [[_ [H1 _]] | [_ [_ H1]]]]; auto.
      + apply (lt_cross_mul ordered_ring_from_field 1 (a^-1) 1 a) in H1;
          auto using (ordered_rings.zero_lt_1 ordered_ring_from_field);
          simpl in *.
        rewrite inv_l, rings.M3 in H1;
          auto using (ordered_rings.lt_neq ordered_ring_from_field).
        contradiction (ordered_rings.lt_irrefl ordered_ring_from_field 1).
      + rewrite <-inv_inv, <-H1, inv_one in H0;
          auto using (ordered_rings.lt_neq ordered_ring_from_field).
        now apply (lt_irrefl ordered_ring_from_field) in H0.
    - destruct (T _ 1 a) as [[H1 [H2 H3]] | [[_ [H1 _]] | [_ [_ H1]]]]; auto.
      + subst.
        rewrite inv_one in H0.
        contradiction (ordered_rings.lt_irrefl ordered_ring_from_field 1).
      + apply (lt_cross_mul ordered_ring_from_field (a^-1) 1 a 1) in H0;
          simpl in *; auto.
        * rewrite inv_l, rings.M3 in H0;
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
    { eapply (ordered_rings.lt_trans ordered_ring_from_field); eauto.
        apply (ordered_rings.zero_lt_1 ordered_ring_from_field). }
    replace n with (--n)%Z by ring.
    rewrite neg_pow, <-inv_lt_1; simpl.
    - apply pow_gt_1; auto.
      now rewrite <-(ordered_rings.lt_neg_0 ℤ_order).
    - now apply pow_pos.
    - auto using (ordered_rings.lt_neq ordered_ring_from_field).
  Qed.

  Theorem mul_denom_l : ∀ a b c, 0 < b → a * b^-1 < c ↔ a < b * c.
  Proof.
    intros a b c H.
    split; intros H0.
    - rewrite <-(rings.M3 _ a), <-(inv_r _ b), <-rings.M2, (rings.M1 _ _ a);
        auto using (pos_ne_0 ordered_ring_from_field).
      apply (O3 ordered_ring_from_field); simpl; auto.
    - rewrite <-(rings.M3_r _ c), <-(inv_r _ b), rings.M2, (rings.M1 _ c);
        auto using (pos_ne_0 ordered_ring_from_field).
      apply (O3_r ordered_ring_from_field); simpl; auto using inv_lt.
  Qed.

End Ordered_field_theorems.
