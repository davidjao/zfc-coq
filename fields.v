Require Export integers Field.

Record field :=
  mkField {
      set_F : set;
      zero_F : elts set_F (*where "0" := zero_F*);
      one_F : elts set_F (*where "1" := one_F*);
      add_F : elts set_F → elts set_F → elts set_F where "a + b" := (add_F a b);
      mul_F : elts set_F → elts set_F → elts set_F where "a * b" := (mul_F a b);
      neg_F : elts set_F → elts set_F where "- a" := (neg_F a);
      inv_F : elts set_F → elts set_F;
      A3_F : ∀ a, zero_F + a = a;
      A1_F : ∀ a b, a + b = b + a;
      A2_F : ∀ a b c, a + (b + c) = (a + b) + c;
      M3_F : ∀ a, one_F * a = a;
      M1_F : ∀ a b, a * b = b * a;
      M2_F : ∀ a b c, a * (b * c) = (a * b) * c;
      D1_F : ∀ a b c, (a + b) * c = a * c + b * c;
      A4_F : ∀ a, a + (-a) = zero_F;
      M4_F : ∀ a, a ≠ zero_F → (inv_F a) * a = one_F;
      one_ne_0_F : one_F ≠ zero_F;
    }.

(*
Definition rationals :=
mkField _ zero one add mul neg inv A3 A1 A2 M3 M1 M2 D1 A4 inv_l zero_ne_1.
*)

Section Field_theorems.
  Variable F : field.

  Notation "0" := (zero_F F).
  Notation "1" := (one_F F).

  Infix "+" := (add_F F).
  Infix "*" := (mul_F F).

  Notation "- a" := (neg_F _ a).
  Notation "a '^-1' " := (inv_F _ a) (at level 30, format "a '^-1'").

  Definition sub_F a b := a + (-b).
  Definition inv_l := M4_F.

  Infix "-" := sub_F.

  Lemma sub_neg_F : ∀ a b, a - b = a + -b.
  Proof.
    auto.
  Qed.

  Definition div_F a b := a * (inv_F _ b).

  Infix "/" := div_F.

  Theorem div_inv : ∀ a b, a / b = a * b^-1.
  Proof.
    auto.
  Qed.

  Add Field generic_field :
    (mk_field div_F
              (inv_F F)
              (mk_rt 0 1 (add_F F) (mul_F F) sub_F (neg_F F) eq (A3_F F)
                     (A1_F F) (A2_F F) (M3_F F) (M1_F F) (M2_F F) (D1_F F)
                     sub_neg_F (A4_F F))
              (one_ne_0_F F) div_inv (M4_F F)).

  Definition ring_from_field :=
    mkRing _ 0 1 (add_F F) (mul_F F) (neg_F F) (A3_F F) (A1_F F) (A2_F F)
           (M3_F F) (M1_F F) (M2_F F) (D1_F F) (A4_F F).

  Theorem inv_r : ∀ a, a ≠ 0 → a * a^-1 = 1.
  Proof.
    intros a H.
    now field.
  Qed.
  Definition M4_R := inv_r.

  Theorem cancellation : ∀ a b, a * b = 0 → a = 0 ∨ b = 0.
  Proof.
    intros a b H.
    destruct (classic (a = 0)) as [H0 | H0]; try tauto.
    assert (a^-1 * (a * b) = a^-1 * 0) by now rewrite H.
    right.
    rewrite M2_F, M4_F, M3_F in H1; auto.
    ring [H1].
  Qed.

  Definition integral_domain_from_field :=
    mkID ring_from_field cancellation (one_ne_0_F F).

  Theorem inv_unique : ∀ a, (∀ b, a * b = 1 → b = a^-1).
  Proof.
    intros a b H.
    destruct (classic (a = 0)).
    - subst.
      replace (0*b) with 0 in H by ring.
      now contradiction (one_ne_0_F F).
    - rewrite <-(inv_r a) in H; auto.
      assert (a^-1 * (a*b) = a^-1 * (a*a^-1)) as H1 by congruence.
      now rewrite ? (M2_F F), inv_l, ? (M3_F F) in H1.
  Qed.

  Theorem inv_one : 1^-1 = 1.
  Proof.
    symmetry.
    apply inv_unique.
    now rewrite (M3_F F).
  Qed.

  Theorem inv_neg : ∀ a, a ≠ 0 → -a^-1 = (-a)^-1.
  Proof.
    intros a H.
    field.
    split; auto.
    contradict H.
    ring [H].
  Qed.

  Theorem inv_ne_0 : ∀ a, a ≠ 0 → a^-1 ≠ 0.
  Proof.
    intros a H H0.
    pose proof (inv_r a H) as H1.
    rewrite H0 in H1.
    replace (a*0) with 0 in H1 by ring.
    now contradiction (one_ne_0_F F).
  Qed.

  Theorem inv_inv : ∀ a, a ≠ 0 → a^-1^-1 = a.
  Proof.
    intros a H.
    assert (a * a^-1 * a = a * a^-1 * a^-1^-1) as H0.
    { rewrite <-? M2_F, inv_l,  (M1_F _ (a^-1)), inv_l; auto using inv_ne_0. }
      now rewrite ? (M1_F _ a), inv_l, ? M3_F in H0.
  Qed.

  Definition pow_N := (pow ring_from_field) : elts (set_F F) → N → elts (set_F F).
  
  Infix "@" := pow_N (at level 35).

  Definition pow : elts (set_F F) → Z → elts (set_F F).
  Proof.
    intros a b.
    destruct (excluded_middle_informative (0 < b)%Z).
    - apply lt_def in l.
      destruct (constructive_indefinite_description _ l) as [c [H H0]].
      rewrite integers.A3 in H0.
      exact (a@c).
    - destruct (excluded_middle_informative (b < 0)%Z).
      + rewrite (ordered_rings.lt_neg_0 integer_order), lt_def in l.
        destruct (constructive_indefinite_description _ l) as [c [H H0]].
        rewrite integers.A3 in H0.
        exact ((a^-1@c)).
      + exact 1.
  Defined.

  Infix "^" := pow.

  Theorem pow_0_r : ∀ a, a^0 = 1.
  Proof.
    intros a.
    unfold pow.
    destruct excluded_middle_informative; auto;
      contradiction (ordered_rings.lt_irrefl integer_order 0%Z).
  Qed.

  Theorem pow_0_l : ∀ a : Z, a > 0%Z → 0^a = 0.
  Proof.
    intros a H.
    unfold pow.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description;
      try destruct a0; try tauto.
    rewrite (pow_0_l ring_from_field); auto.
    contradict n.
    now subst.
  Qed.

  Theorem pow_1_r : ∀ a, a^1 = a.
  Proof.
    intros a.
    unfold pow.
    repeat destruct excluded_middle_informative; auto;
      repeat destruct constructive_indefinite_description;
      try destruct a0.
    - unfold integers.one in e.
      rewrite integers.A3 in e.
      assert (x = 1%N).
      { apply INZ_eq.
        now rewrite <-e. }
      subst.
      now apply (pow_1_r ring_from_field).
    - contradiction n.
      apply integers.zero_lt_1.
    - contradiction n.
      apply integers.zero_lt_1.
  Qed.

  Theorem pow_1_l : ∀ a, 1^a = 1.
  Proof.
    intros a.
    unfold pow.
    repeat destruct excluded_middle_informative; auto;
      repeat destruct constructive_indefinite_description;
      try destruct a0.
    - now rewrite (pow_1_l ring_from_field).
    - now rewrite inv_one, (pow_1_l ring_from_field).
  Qed.

  Theorem pow_neg : ∀ a b, a ≠ 0 → a^(-b) = (a^-1)^b.
  Proof.
    intros a b H.
    unfold pow.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description;
      try destruct a0; try destruct a1; auto; simpl in *.
    - contradiction (ordered_rings.lt_antisym integer_order 0%Z b); auto.
      now rewrite (ordered_rings.lt_neg_0 integer_order).
    - rewrite integers.A3 in *; simpl in *.
      assert ((x : Z) = (x0 : Z)) as H0 by congruence.
      subst.
      apply INZ_eq in H0.
      now rewrite inv_inv, H0.
    - contradiction n0.
      now rewrite (ordered_rings.lt_neg_0 integer_order).
    - replace (--b)%Z with b in e by ring.
      rewrite integers.A3 in *.
      subst.
      apply INZ_eq in e0.
      now subst.
    - contradiction n0.
      now rewrite (ordered_rings.neg_lt_0 integer_order).
    - contradiction n0.
      now rewrite (ordered_rings.neg_lt_0 integer_order).
    - contradiction n0.
      now rewrite <-(ordered_rings.neg_lt_0 integer_order).
    - contradiction n.
      now rewrite <-(ordered_rings.lt_neg_0 integer_order).
  Qed.

  Theorem inv_pow : ∀ a, a ≠ 0 → a^(-(1)) = a^-1.
  Proof.
    intros a H.
    apply inv_unique; auto.
    now rewrite pow_neg, pow_1_r, M1_F, inv_l.
  Qed.

  Lemma pow_add_r_pos_pos :
    ∀ a b c, (0 < b)%Z → (0 < c)%Z → a^(b+c) = a^b * a^c.
  Proof.
    intros a b c H H0.
    unfold pow.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description;
      try destruct a0; try destruct a1; try destruct a2; try tauto.
    - rewrite integers.A3 in *.
      subst.
      rewrite INZ_add, INZ_eq in e.
      subst.
      apply (pow_add_r ring_from_field).
    - contradiction (ordered_rings.lt_antisym integer_order 0%Z (b+c)%Z).
      now apply integers.O0.
    - assert (b + c = 0)%Z as H1.
      { pose proof (integers.T (b+c) 0).
        tauto. }
      contradiction (ordered_rings.lt_irrefl integer_order 0%Z).
      rewrite <-H1 at 2.
      now apply integers.O0.
  Qed.

  Theorem pow_ne_0 : ∀ a b, a ≠ 0 → a^b ≠ 0.
  Proof.
    intros a b H.
    unfold pow.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description; try destruct a0;
        auto using (pow_ne_0 integral_domain_from_field), inv_ne_0, one_ne_0_F.
  Qed.

  Theorem pow_mul_l : ∀ a b c, a ≠ 0 → b ≠ 0 → (a*b)^c = a^c * b^c.
  Proof.
    intros a b c H H0.
    unfold pow.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description;
      try destruct a0; try destruct a1; try tauto; try now rewrite M3_F.
    - apply (pow_mul_l ring_from_field).
    - replace ((a*b)^-1) with (a^-1*b^-1) by now field.
      apply (pow_mul_l ring_from_field).
  Qed.

  Theorem neg_pow : ∀ a b, a ≠ 0 → a^(-b) = (a^b)^-1.
  Proof.
    intros a b H.
    destruct (classic (b = 0%Z)); try subst.
    - replace (-0)%Z with 0%Z by ring.
      now rewrite pow_0_r, inv_one.
    - apply inv_unique.
      rewrite pow_neg, <-pow_mul_l, M1_F, inv_l, pow_1_l; auto using inv_ne_0.
  Qed.

  Theorem pow_mul_r_pos : ∀ a b c, a ≠ 0 → (0 < c)%Z → a^(b*c) = (a^b)^c.
  Proof.
    intros a b c H H0.
    unfold pow at 2.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description;
      try destruct a0; try tauto; try rewrite e, integers.A3.
    unfold pow.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description; try destruct a0;
        try destruct a1; try rewrite integers.A3 in *; simpl in *; subst.
    - rewrite INZ_mul, INZ_eq in e0.
      subst.
      apply (pow_mul_r ring_from_field).
    - contradiction (ordered_rings.lt_antisym integer_order 0%Z (b*x)%Z).
      now apply mul_neg_pos.
    - assert (b = 0%Z) by (pose proof (integers.T b 0); tauto).
      subst.
      replace (0*x)%Z with 0%Z in * by ring.
      contradiction (ordered_rings.lt_irrefl integer_order 0%Z).
    - contradiction (ordered_rings.lt_antisym integer_order 0%Z (x1*x)%Z).
      now apply mul_pos_pos.
    - replace (-(b*x))%Z with ((-b)*x)%Z in e0 by ring.
      rewrite e1, INZ_mul, INZ_eq in e0.
      subst.
      apply (pow_mul_r ring_from_field).
    - assert (b = 0%Z) by (pose proof (integers.T b 0); tauto).
      subst.
      replace (0*x)%Z with 0%Z in * by ring.
      contradiction (ordered_rings.lt_irrefl integer_order 0%Z).
    - contradiction n0.
      now apply mul_pos_pos.
    - contradiction n1.
      now apply (mul_neg_pos integer_order).
    - now rewrite (rings.pow_1_l ring_from_field).
  Qed.

  Theorem pow_mul_r : ∀ a b c, a ≠ 0 → a^(b*c) = (a^b)^c.
  Proof.
    intros a b c H.
    destruct (integers.T 0 c) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]].
    - now apply pow_mul_r_pos.
    - subst.
      replace (b*0)%Z with 0%Z by ring.
      now rewrite ? pow_0_r.
    - unfold pow at 2.
      repeat destruct excluded_middle_informative;
        repeat destruct constructive_indefinite_description;
        try destruct a0; try tauto; try rewrite e, integers.A3.
      replace ((a ^ b)^-1 @ x) with ((a ^ b)^-1 ^ (-c)).
      + replace (b*c)%Z with ((-b)*(-c))%Z by ring.
        rewrite <-neg_pow; auto.
        now apply pow_mul_r_pos, (ordered_rings.lt_neg_0 integer_order).
      + unfold pow at 1.
        repeat destruct excluded_middle_informative;
          repeat destruct constructive_indefinite_description;
          try destruct a0; try tauto; try rewrite e, integers.A3; simpl in *.
        * rewrite integers.A3 in *.
          assert ((x : Z) = (x0 : Z)) as H3 by congruence.
          apply INZ_eq in H3.
          now subst.
        * contradiction n1.
          now apply (ordered_rings.lt_neg_0 integer_order).
        * contradiction n1.
          now apply (ordered_rings.lt_neg_0 integer_order).
  Qed.

  Theorem pow_div_distr : ∀ a b c, a ≠ 0 → b ≠ 0 → (a*b^-1)^c = a^c * (b^c)^-1.
  Proof.
    intros a b c H H0.
    rewrite pow_mul_l, <-neg_pow, pow_neg; auto using inv_ne_0.
  Qed.

  Lemma pow_add_r_opp : ∀ a b, a ≠ 0 → a^b * a^(-b) = 1.
  Proof.
    intros a b H.
    rewrite pow_neg, <-pow_mul_l, M1_F, inv_l, pow_1_l; auto using inv_ne_0.
  Qed.

  Lemma pow_add_r_pos_neg :
    ∀ a b c, a ≠ 0 → (0 < b)%Z → (c < 0)%Z → a^(b+c) = a^b * a^c.
  Proof.
    intros a b c H H0 H1.
    eapply (cancellation_mul_l integral_domain_from_field (a^(-c)));
      auto using pow_ne_0; simpl.
    rewrite ? (M1_F _ (a^(-c))), <-M2_F, pow_add_r_opp, (M1_F _ _ 1), M3_F;
      auto using pow_ne_0.
    destruct (integers.T 0 (b+c))
      as [[H2 [H3 H4]] | [[H2 [H3 H4]] | [H2 [H3 H4]]]].
    - rewrite (ordered_rings.lt_neg_0 integer_order) in H1.
      rewrite <-pow_add_r_pos_pos, <-integers.A2, integers.A4, integers.(A3_r);
        auto.
    - rewrite <-(integers.A3 b) at 2.
      now rewrite <-(integers.A4 c), (integers.A1 _ b),
      integers.A2, <-H3, integers.A3, pow_0_r, M3_F.
    - eapply (cancellation_mul_l integral_domain_from_field (a^(-(b+c))));
        auto using pow_ne_0; simpl.
      rewrite (ordered_rings.lt_neg_0 integer_order) in H4.
      rewrite ? M2_F, ? (M1_F _ (a^(-(b+c)))), pow_add_r_opp, M3_F,
      <-pow_add_r_pos_pos; auto.
      now replace (b+-(b+c))%Z with (-c)%Z by ring.
  Qed.

  Theorem pow_add_r : ∀ a b c, a ≠ 0 → a^(b+c) = a^b * a^c.
  Proof.
    intros a b c H.
    destruct (integers.T 0 b)
      as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]], (integers.T 0 c)
        as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]]; subst;
      rewrite ? (integers.A1 _ 0), ? integers.A3, ? pow_0_r, ? (M1_F _ _ 1),
      ? M3_F; auto using pow_add_r_pos_pos, pow_add_r_pos_neg.
    - rewrite integers.A1, M1_F.
      auto using pow_add_r_pos_neg.
    - replace b with (--b)%Z; replace c with (--c)%Z;
        replace (--b+--c)%Z with (-(-b+-c))%Z; try ring.
      rewrite ? (pow_neg a); auto.
      apply inv_ne_0 in H.
      apply pow_add_r_pos_pos; now apply (ordered_rings.lt_neg_0 integer_order).
  Qed.

  Theorem pow_wf : ∀ a b, a@b = a^b.
  Proof.
    intros a b.
    destruct (N_ge_0 b) as [H | H]; simpl in *.
    - unfold pow.
      repeat destruct excluded_middle_informative;
        repeat destruct constructive_indefinite_description;
        try destruct a0; try tauto.
      rewrite integers.A3 in e.
      apply INZ_eq in e.
      now subst.
    - apply INZ_eq in H.
      subst.
      now rewrite pow_0_r, (rings.pow_0_r ring_from_field).
  Qed.

End Field_theorems.
