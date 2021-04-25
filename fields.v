Set Warnings "-notation-overridden,-notation-bound-to-variable".
Set Warnings "-ambiguous-paths".
Require Export integer_powers Field.

Record field :=
  mkField {
      ring :> rings.ring where
      "a * b" :=
        (rings.mul ring a b)
          and "0" :=
        (rings.zero ring)
          and "1" :=
          (rings.one ring);
      inv : elts ring → elts ring;
      M4 : ∀ a, a ≠ 0 → (inv a) * a = 1;
      one_ne_0 : 1 ≠ 0;
    }.

Section Field_theorems.

  Variable Field : field.
  Notation F := (elts (ring Field)).
  Notation "0" := (rings.zero (ring Field)).
  Notation "1" := (rings.one (ring Field)).
  Infix "+" := (rings.add (ring Field)).
  Infix "*" := (rings.mul (ring Field)).
  Notation "- a" := (rings.neg (ring Field) a).
  Notation "- 1" := (rings.neg (ring Field) 1).
  Notation "a '^-1' " := (inv Field a) (at level 30, format "a '^-1'").

  Definition inv_l := (M4 Field).

  Infix "-" := (rings.sub (ring Field)).

  Definition div a b := a * b^-1.

  Infix "/" := div.

  Theorem div_inv : ∀ a b, a / b = a * b^-1.
  Proof.
    auto.
  Qed.

  Definition fieldify :=
    (mk_field div (inv _) (ringify (ring Field)) (one_ne_0 _) div_inv (M4 _)).

  Add Field generic_field : fieldify.

  Definition ring_from_field := (ring Field).

  Theorem inv_r : ∀ a, a ≠ 0 → a * a^-1 = 1.
  Proof.
    move=> a H.
      by field.
  Qed.
  Definition M4_r := inv_r.

  Theorem cancellation : ∀ a b, a * b = 0 → a = 0 ∨ b = 0.
  Proof.
    move: classic => /[swap] a /(_ (a = 0)) [/or_introl | H]
                      b /(f_equal (rings.mul _ (a^-1))) //.
    rewrite rings.M2 M4 // rings.M3 mul_0_r => /or_intror //.
  Qed.

  Definition integral_domain_from_field :=
    mkID ring_from_field cancellation (one_ne_0 _).

  Theorem inv_one : 1^-1 = 1.
  Proof.
    field.
    apply /one_ne_0.
  Qed.

  Theorem inv_unique : ∀ a, (∀ b, a * b = 1 → b = a^-1).
  Proof.
    move: classic => /[swap] a /(_ (a = 0)) [-> b | H b H0].
    - move: mul_0_l (one_ne_0 Field) -> => /neq_sym //.
    - by field [H0].
  Qed.

  Theorem inv_neg : ∀ a, a ≠ 0 → -a^-1 = (-a)^-1.
  Proof.
    move=> a H.
    field.
    split; auto.
    contradict H.
    ring [H].
  Qed.

  Theorem inv_ne_0 : ∀ a, a ≠ 0 → a^-1 ≠ 0.
  Proof.
    move: (one_ne_0 Field) => /[swap] a /[swap] H0 /[swap] H1 [].
    rewrite -(inv_r a) // H1 mul_0_r //.
  Qed.

  Theorem inv_inv : ∀ a, a ≠ 0 → a^-1^-1 = a.
  Proof.
    auto using eq_sym, inv_unique, inv_l.
  Qed.

  Theorem unit_nonzero : ∀ a, rings.unit a ↔ a ≠ 0.
  Proof.
    split => [/[swap] -> [x] | ].
    - move: mul_0_r (one_ne_0 Field) -> => //.
    - exists (a^-1).
      rewrite inv_l //.
  Qed.

  Theorem inv_ring_to_field : ∀ a, a ≠ 0 → integer_powers.inv _ a = a^-1.
  Proof.
    move=> a /unit_nonzero H.
    apply /inv_unique.
    rewrite integer_powers.inv_r //.
  Qed.

  Definition pow_N := (rings.pow (ring Field)) : F → N → F.

  (* Temporarily use ** to denote natural number exponentiation, as is done in
     some programming languages, to distinguish from integer exponentiation,
     which we will define shortly, and denote with ^ as usual. *)
  Infix "**" := pow_N (at level 35).

  Definition pow := integer_powers.pow ring_from_field : F → Z → F.

  Infix "^" := pow.

  Theorem pow_0_r : ∀ a, a^0 = 1.
  Proof.
    move=> a.
      apply /pow_0_r.
  Qed.

  Theorem pow_0_l : ∀ a : Z, a ≠ 0%Z → 0^a = 0.
  Proof.
    move=> a H.
      by apply /pow_0_l.
  Qed.

  Theorem pow_1_r : ∀ a, a^1 = a.
  Proof.
    move=> a.
    apply /pow_1_r.
  Qed.

  Theorem pow_1_l : ∀ a, 1^a = 1.
  Proof.
    move=> a.
    apply /pow_1_l.
  Qed.

  Theorem pow_neg : ∀ a b, a ≠ 0 → a^(-b) = (a^-1)^b.
  Proof.
    move=> a b /[dup] H /unit_nonzero H0.
    rewrite /pow pow_neg /ring_from_field // inv_ring_to_field //.
  Qed.

  Theorem inv_pow : ∀ a, a ≠ 0 → a^(-1) = a^-1.
  Proof.
    move=> a H.
    rewrite pow_neg // pow_1_r //.
  Qed.

  Theorem pow_add_r : ∀ a b c, a ≠ 0 → a^(b+c) = a^b * a^c.
  Proof.
    move=> a b c /unit_nonzero /pow_add_r //.
  Qed.

  Theorem pow_ne_0 : ∀ a b, a ≠ 0 → a^b ≠ 0.
  Proof.
    move=> a b H.
      by apply /unit_nonzero /unit_pow /unit_nonzero.
  Qed.

  Theorem pow_mul_l : ∀ a b c, a ≠ 0 → b ≠ 0 → (a*b)^c = a^c * b^c.
  Proof.
    move=> a b c /unit_nonzero H /unit_nonzero H0.
      by apply /pow_mul_l.
  Qed.

  Theorem neg_pow : ∀ a b, a ≠ 0 → a^(-b) = (a^b)^-1.
  Proof.
    move=> a b /[dup] H /unit_nonzero H0.
    rewrite /pow (neg_pow (ring Field)) //.
      by apply /inv_ring_to_field /pow_ne_0.
  Qed.

  Theorem pow_mul_r : ∀ a b c, a ≠ 0 → a^(b*c) = (a^b)^c.
  Proof.
    move=> a b c H.
      by apply /pow_mul_r /unit_nonzero.
  Qed.

  Theorem pow_div_distr : ∀ a b c, a ≠ 0 → b ≠ 0 → (a*b^-1)^c = a^c * (b^c)^-1.
  Proof.
    move=> a b c H /[dup] H0 /inv_ne_0 H1.
    rewrite pow_mul_l // -neg_pow // pow_neg //.
  Qed.

  Lemma pow_add_r_opp : ∀ a b, a ≠ 0 → a^b * a^(-b) = 1.
  Proof.
    move=> a b H.
      by apply /pow_add_r_opp /unit_nonzero.
  Qed.

  Theorem pow_wf : ∀ a b, a**b = a^b.
  Proof.
    move=> a b.
      by apply /eq_sym /pow_nonneg.
  Qed.

  Theorem minus_one_nonzero : -1 ≠ 0.
  Proof.
    move: (one_ne_0 Field) =>/[swap] /(f_equal (rings.neg (ring Field))) H [].
    ring_simplify in H => //.
  Qed.

End Field_theorems.
