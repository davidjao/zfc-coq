Set Warnings "-notation-overridden,-ambiguous-paths".
Require Export ordered_rings fields.

Record ordered_field :=
  mkOF {
      field :> field where
      "a + b" :=
        (rings.add (fields.ring field) a b)
          and "a * b" :=
        (rings.mul (fields.ring field) a b)
          and "0" :=
          (rings.zero (fields.ring field))
          and "1" :=
            (rings.one (fields.ring field));
      lt : elts (fields.ring field) → elts (fields.ring field)
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
  Notation F := (elts (fields.ring Field)).
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
    destruct (T _ 0 (x^-1)) as [[H0 _] | [[_ [H0 _]] | [_ [_ H0]]]]; try tauto.
    - contradiction (one_ne_0 Field).
      rewrite <-(inv_r _ x), <-H0, mul_0_r;
        auto using (ordered_rings.lt_neq ordered_ring_from_field).
    - do 2 eapply (O3 ordered_ring_from_field x) in H0; auto; simpl in *.
      rewrite -> ? mul_0_r, inv_r, rings.M1, rings.M3 in H0;
        auto using (ordered_rings.lt_neq ordered_ring_from_field).
      contradiction (lt_antisym ordered_ring_from_field 0 x).
  Qed.

  Definition inv_lt := O4.

  Theorem lt_cross_inv : ∀ a b, 0 < a → 0 < b → a < b ↔ b^-1 < a^-1.
  Proof.
    intros a b H H0.
    split; intros H1.
    - apply (O3 ordered_ring_from_field (a^-1 * b^-1)) in H1; simpl in *.
      + rewrite <-? rings.M2, inv_l, (rings.M1 _ _ 1), rings.M3, rings.M1,
        <-rings.M2, inv_r, rings.M1, rings.M3 in H1;
          auto using (lt_neq ordered_ring_from_field).
      + apply (ordered_rings.O2 ordered_ring_from_field); now apply inv_lt.
    - apply (O3 ordered_ring_from_field (a*b)) in H1; simpl in *;
        try now apply (ordered_rings.O2 ordered_ring_from_field).
      rewrite <-rings.M2, inv_r, rings.M3_r, rings.M1, rings.M2, inv_l,
      rings.M3 in H1; auto using (lt_neq ordered_ring_from_field).
  Qed.

  Theorem lt_div : ∀ a b, 0 < a → a < b → 1 < b * a^-1.
  Proof.
    intros a b H H0.
    apply (O3_r ordered_ring_from_field (a^-1)) in H0; simpl in *.
    - rewrite inv_r in H0; auto using (lt_neq ordered_ring_from_field).
    - now apply inv_lt.
  Qed.

  Theorem unit_pos : ∀ a, 0 < a → rings.unit a.
  Proof.
    intros a H.
    apply unit_nonzero.
    intros H0; subst.
    contradiction (lt_irrefl ordered_ring_from_field 0).
  Qed.

  Theorem pow_pos : ∀ a n, 0 < a → 0 < a^n.
  Proof.
    intros a n H.
    unfold pow, integer_powers.pow, eq_rect_r, eq_rect, eq_sym.
    repeat destruct excluded_middle_informative; try destruct A3;
      repeat destruct constructive_indefinite_description;
      try destruct a0.
    - rewrite -> integers.A3, e in *.
      now apply (pow_pos ordered_ring_from_field).
    - rewrite inv_ring_to_field; auto using (lt_neq ordered_ring_from_field).
      now apply (pow_pos ordered_ring_from_field), O4.
    - contradict n1.
      now apply unit_pos.
  Qed.

  Theorem inv_lt_1 : ∀ a, 0 < a → 1 < a ↔ a^-1 < 1.
  Proof.
    split; intros H0.
    - destruct (T _ 1 (a^-1)) as [[H1 _] | [[_ [H1 _]] | [_ [_ H1]]]]; auto.
      + apply (O3_r ordered_ring_from_field a) in H1; simpl in *; auto.
        rewrite -> inv_l, rings.M3 in H1;
          auto using (lt_neq ordered_ring_from_field).
        contradiction (lt_antisym ordered_ring_from_field a 1).
      + rewrite <-inv_inv, <-H1, inv_one in H0;
          auto using (ordered_rings.lt_neq ordered_ring_from_field).
        now apply (lt_irrefl ordered_ring_from_field) in H0.
    - destruct (T _ 1 a) as [[H1 [H2 H3]] | [[_ [H1 _]] | [_ [_ H1]]]]; auto.
      + rewrite <-H1, inv_one in H0.
        contradiction (ordered_rings.lt_irrefl ordered_ring_from_field 1).
      + apply (O3_r ordered_ring_from_field a) in H0; simpl in *; auto.
        rewrite -> inv_l, rings.M3 in H0;
          auto using (lt_neq ordered_ring_from_field).
  Qed.

  Theorem pow_gt_1 : ∀ a n, 1 < a → (0 < n)%Z → 1 < a^n.
  Proof.
    intros a n H H0.
    apply lt_def in H0 as H1.
    destruct H1 as [c [H1 H2]].
    rewrite -> H2, integers.A3, <-pow_wf, (INZ_lt 0 c) in *.
    now apply (ordered_rings.pow_gt_1 ordered_ring_from_field).
  Qed.

  Theorem pow_lt_1 : ∀ a n, 1 < a → (n < 0)%Z → a^n < 1.
  Proof.
    intros a n H H0.
    apply (one_lt ordered_ring_from_field) in H as H1; simpl in *.
    rewrite <-(neg_neg ℤ n), neg_pow, <-inv_lt_1; simpl.
    - apply pow_gt_1, (lt_neg_0 ℤ_order); auto.
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
