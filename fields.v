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

End Field_theorems.
