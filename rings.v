Require Export integers.
Set Warnings "-notation-overridden".

Record ring :=
  mkRing {
      set_R : set;
      zero_R : elts set_R (*where "0" := zero_R*);
      one_R : elts set_R (*where "1" := one_R*);
      add_R : elts set_R → elts set_R → elts set_R where "a + b" := (add_R a b);
      mul_R : elts set_R → elts set_R → elts set_R where "a * b" := (mul_R a b);
      neg_R : elts set_R → elts set_R where "- a" := (neg_R a);
      A3_R : ∀ a, zero_R + a = a;
      A1_R : ∀ a b, a + b = b + a;
      A2_R : ∀ a b c, a + (b + c) = (a + b) + c;
      M3_R : ∀ a, one_R * a = a;
      M1_R : ∀ a b, a * b = b * a;
      M2_R : ∀ a b c, a * (b * c) = (a * b) * c;
      D1_R : ∀ a b c, (a + b) * c = a * c + b * c;
      A4_R : ∀ a, a + (-a) = zero_R;
    }.

Definition integers := mkRing _ zero one add mul neg A3 A1 A2 M3 M1 M2 D1 A4.

Section Ring_test.
  Variable R : ring.

  Notation "0" := (zero_R R).
  Notation "1" := (one_R R).

  Infix "+" := (add_R R).
  Infix "*" := (mul_R R).

  Notation "- a" := (neg_R R a).

  Definition sub_R a b := a + (-b).

  Infix "-" := sub_R.

  Lemma sub_neg_R : ∀ a b, a - b = a + -b.
  Proof.
    auto.
  Qed.

  Add Ring R_ring :
    (mk_rt 0 1 (add_R R) (mul_R R) sub_R (neg_R R) eq (A3_R R) (A1_R R)
           (A2_R R) (M3_R R) (M1_R R) (M2_R R) (D1_R R) sub_neg_R (A4_R R)).

  Theorem A1P6 : ∀ a, a * 0 = 0.
  Proof.
    intros a.
    ring.
  Qed.
End Ring_test.

Theorem mul_test : ∀ a, a * 0 = 0.
Proof.
  intros a.
  now rewrite (A1P6 integers).
Qed.
