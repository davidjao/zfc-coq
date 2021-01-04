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

  Notation F := (field_OF OF).
  Notation "0" := (zero_F F).
  Notation "1" := (one_F F).
  Infix "+" := (add_F F).
  Infix "*" := (mul_F F).
  Notation "- a" := (neg_F F a).
  Infix "-" := (sub_F F).
  Infix "<" := (lt_OF OF).
  Notation "a > b" := (b < a) (only parsing).
  Definition le a b := a < b ∨ a = b.
  Infix "≤" := le.
  Notation "x < y < z" := (x < y ∧ y < z).
  Notation "a ≥ b" := (b ≤ a) (only parsing).
  Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level).
  Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level).
  Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level).
  Notation "a '^-1' " := (inv_F _ a) (at level 30, format "a '^-1'").

  Add Field generic_ordered_field :
    (mk_field (div_F F) (inv_F F)
              (mk_rt 0 1 (add_F F) (mul_F F) (sub_F F) (neg_F F) eq (A3_F F)
                     (A1_F F) (A2_F F) (M3_F F) (M1_F F) (M2_F F) (D1_F F)
                     (sub_neg_F F) (A4_F F))
              (one_ne_0_F F) (div_inv F) (M4_F F)).

  Definition ordered_ring_from_field :=
    (mkOring (ring_from_field F) (lt_OF OF) (lt_trans_OF OF)
             (T_OF OF) (O1_OF OF) (O2_OF OF) (one_ne_0_F F)).

  Theorem O4 : ∀ a, 0 < a → 0 < a^-1.
  Proof.
    intros x H.
    destruct (T_OF _ 0 (x^-1)) as [[H0 _] | [[_ [H0 _]] | [_ [_ H0]]]];
      try tauto.
    - contradiction (one_ne_0_F F).
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

End Ordered_field_theorems.
