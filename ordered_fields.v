Set Warnings "-notation-overridden,-ambiguous-paths,-non-reference-hint-using".
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
    move: T => /[swap] x /[swap] H /(_ _ 0 (x^-1)) =>
    [[[? _] | [[_ [H0 _]] | [_ [_ /(O3 ordered_ring_from_field x _ _ H)
                                 /(O3 ordered_ring_from_field x _ _ H)]]]]] //.
    - contradiction (one_ne_0 Field).
      rewrite -(inv_r _ x) -? H0 ? mul_0_r;
        auto using (lt_neq ordered_ring_from_field).
    - by rewrite inv_r ? mul_0_r ? rings.M3_r;
        auto using (lt_neq ordered_ring_from_field) => /lt_antisym.
  Qed.

  Definition inv_lt := O4.

  Theorem lt_cross_inv : ∀ a b, 0 < a → 0 < b → a < b ↔ b^-1 < a^-1.
  Proof.
    move=> a b /[dup] H /(lt_neq ordered_ring_from_field) H0
             /[dup] H1 /(lt_neq ordered_ring_from_field) H2.
    split => [/(O3 ordered_ring_from_field (a^-1 * b^-1)) |
              /(O3 ordered_ring_from_field (a * b))] /=.
    - move: H1 H => /inv_lt /[swap] /inv_lt /= /O2 /[apply] /[swap] /[apply].
      rewrite -? rings.M2 inv_l ? M3_r // rings.M1 -rings.M2 inv_r // M3_r //.
    - move: H H1 => /O2 /[apply] /[swap] /[apply].
      rewrite -rings.M2 inv_r // M3_r rings.M1 rings.M2 inv_l // rings.M3 //.
  Qed.

  Theorem lt_div : ∀ a b, 0 < a → a < b → 1 < b * a^-1.
  Proof.
    move=> a b /[dup] H /inv_lt H0 /(O3_r ordered_ring_from_field (a^-1)) /=.
    rewrite inv_r; auto using (lt_neq ordered_ring_from_field).
  Qed.

  Theorem unit_pos : ∀ a, 0 < a → rings.unit a.
  Proof.
    move=> a /(lt_neq ordered_ring_from_field) /unit_nonzero //.
  Qed.

  Theorem pow_pos : ∀ a n, 0 < a → 0 < a^n.
  Proof.
    rewrite /pow /integer_powers.pow /eq_rect_r /eq_rect /eq_sym =>
    a n /[dup] H /[dup] /inv_lt H0 /(lt_neq ordered_ring_from_field) H1.
    ((repeat elim excluded_middle_informative) =>
     [H2 | H2 H3 | H2]; try destruct A3;
     try elim constructive_indefinite_description) =>
    [x _ | x _ | ]; rewrite ? inv_ring_to_field //;
                            try by apply /(pow_pos ordered_ring_from_field).
    move: H H2 => /unit_pos //.
  Qed.

  Theorem inv_lt_1 : ∀ a, 0 < a → 1 < a ↔ a^-1 < 1.
  Proof.
    move=> a /[dup] H /[dup] /inv_lt H0 /(lt_neq ordered_ring_from_field) H1.
    split =>
    [/(O3 ordered_ring_from_field _ _ _ H0) |
     /(O3 ordered_ring_from_field _ _ _ H)]; rewrite M3_r ? inv_l ? inv_r //.
  Qed.

  Theorem pow_gt_1 : ∀ a n, 1 < a → (0 < n)%Z → 1 < a^n.
  Proof.
    move=> a n H /[dup] /lt_def [c [H0 ->]].
    rewrite A3 -pow_wf INZ_lt => /(pow_gt_1 ordered_ring_from_field a _ H) //.
  Qed.

  Theorem pow_lt_1 : ∀ a n, 1 < a → (n < 0)%Z → a^n < 1.
  Proof.
    move=> a n /[dup] H /(one_lt ordered_ring_from_field) /= /[dup] H0
             /(lt_neq ordered_ring_from_field) H1 /[dup] H2
             /(lt_neg_0 ℤ_order) /= H3.
    rewrite -(neg_neg ℤ n) neg_pow // -inv_lt_1; auto using pow_gt_1, pow_pos.
  Qed.

  Theorem mul_denom_l : ∀ a b c, 0 < b → a * b^-1 < c ↔ a < b * c.
  Proof.
    move=> a b c /[dup] H /[dup] /inv_lt H0 /(lt_neq ordered_ring_from_field) ?.
    split => [/(O3 ordered_ring_from_field _ _ _ H) |
              /(O3 ordered_ring_from_field _ _ _ H0)] /=.
    - rewrite rings.M1 -rings.M2 inv_l // M3_r //.
    - rewrite rings.M1 rings.M2 inv_l // rings.M3 //.
  Qed.

End Ordered_field_theorems.
