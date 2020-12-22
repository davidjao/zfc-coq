Require Export peano_axioms.
  
Record ring :=
  mkRing {
      set_R : set;
      add_R : elts set_R → elts set_R → elts set_R where "a + b" := (add_R a b);
      mul_R : elts set_R → elts set_R → elts set_R where "a * b" := (mul_R a b);
      zero_R : elts set_R (*where "0" := zero_R*);
      one_R : elts set_R (*where "1" := one_R*);
      neg_R : elts set_R → elts set_R where "- a" := (neg_R a);
      A1_R : ∀ a b, a + b = b + a;
      A2_R : ∀ a b c, a + (b + c) = (a + b) + c;
      A3_R : ∀ a, a + zero_R = a;
      A4_R : ∀ a, a + (-a) = zero_R;
      M1_R : ∀ a b, a * b = b * a;
      M2_R : ∀ a b c, a * (b * c) = (a * b) * c;
      M3_R : ∀ a, a * one_R = a;
      D1_R : ∀ a b c, a * (b + c) = a * b + a * c;
    }.

Definition integer_relation :=
  {z in (ω × ω) × (ω × ω) | ∃ a b c d : N,
     z = ((value ω a, value ω b), (value ω c, value ω d)) ∧
     a + d = b + c}.

Theorem integer_equivalence : is_equivalence (ω × ω) integer_relation.
Proof.
  repeat split.
  - intros a H.
    apply Specify_classification.
    split.
    + apply Product_classification.
      now exists a, a.
    + apply Product_classification in H as [x [y [H [H0 H1]]]].
      exists (mkSet ω x H), (mkSet ω y H0), (mkSet ω x H), (mkSet ω y H0).
      split; simpl.
      * congruence.
      * now rewrite add_comm.
  - intros x y H H0 H1.
    unfold integer_relation in *.
    rewrite Specify_classification in *.
    destruct H1 as [H1 [a [b [c [d [H2 H3]]]]]].
    split.
    + apply Product_classification.
      now exists y, x.
    + exists c, d, a, b.
      split.
      * rewrite Ordered_pair_iff in *.
        intuition.
      * now rewrite add_comm, (add_comm d).
  - intros x y z H H0 H1 H2 H3.
    unfold integer_relation in *.
    rewrite Specify_classification in *.
    destruct H2 as [H2 [a [b [c [d [H4 H5]]]]]],
                   H3 as [H3 [e [f [g [h [H6 H7]]]]]].
    split.
    + apply Product_classification.
      now exists x, z.
    + exists a, b, g, h.
      split; rewrite Ordered_pair_iff in *; intuition.
      subst.
      apply Ordered_pair_iff in H4 as [H4 H6].
      replace c with e in *; try now apply set_proj_injective.
      replace d with f in *; try now apply set_proj_injective.
      apply (cancellation_add _ _ e).
      now rewrite <-? add_assoc, (add_comm h),
      H7, (add_comm g), ? add_assoc, H5.
Qed.

Definition Z := elts ((ω × ω) / integer_relation).

Definition embed : N → N → Z.
Proof.
  intros [_ a A] [_ b B].
  assert ((a, b) ∈ ω × ω).
  { apply Product_classification.
    exists a, b.
    auto. }
  exact (quotient_map (ω × ω) integer_relation (mkSet (ω × ω) (a,b) H)).
Defined.

Theorem embed_surj : ∀ z, ∃ a b, embed a b = z.
Proof.
  intros z.
  destruct (quotient_lift _ _ z) as [y H].
  destruct (unique_set_element _ y) as [x [[H0 H1] H2]].
  apply Product_classification in H0 as [a [b [H3 [H4 H5]]]].
  exists (mkSet _ _ H3), (mkSet _ _ H4).
  apply set_proj_injective.
  simpl in *.
  rewrite <-H, <-H5, <-H1.
  auto using quotient_image. (* alternative direct proof: now destruct y. *)
Qed.

Theorem embed_kernel : ∀ a b c d, embed a b = embed c d ↔ a+d = b+c.
Proof.
  intros [_ a A] [_ b B] [_ c C] [_ d D].
  split; intros H; unfold embed in *.
  - apply quotient_wf in H; auto using integer_equivalence.
    simpl in *.
    apply Specify_classification in H as [H [a0 [b0 [c0 [d0 [H0 H1]]]]]].
    rewrite ? Ordered_pair_iff in *; intuition; subst.
    replace {| value := value ω a0; in_set := A |} with a0;
    replace {| value := value ω b0; in_set := B |} with b0;
    replace {| value := value ω c0; in_set := C |} with c0;
    replace {| value := value ω d0; in_set := D |} with d0;
    auto; now apply set_proj_injective.
  - apply quotient_wf; auto using integer_equivalence.
    simpl.
    apply Specify_classification; split.
    + apply Product_classification.
      exists (a,b), (c,d).
      repeat split; auto; apply Product_classification;
        [ exists a, b | exists c, d ]; auto.
    + exists {| value := a; in_set := A |}, {| value := b; in_set := B |},
      {| value := c; in_set := C |}, {| value := d; in_set := D |}.
      split; auto.
Qed.

Definition INZ a := embed a 0.

Coercion INZ : N >-> Z.

Definition add : Z → Z → Z.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (embed_surj x)) as [a H].
  destruct (constructive_indefinite_description _ H) as [b H0].
  destruct (constructive_indefinite_description _ (embed_surj y)) as [c H1].
  destruct (constructive_indefinite_description _ H1) as [d H2].
  exact (embed (a+c) (b+d)).
Defined.

Definition mul : Z → Z → Z.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (embed_surj x)) as [m H].
  destruct (constructive_indefinite_description _ H) as [n H0].
  destruct (constructive_indefinite_description _ (embed_surj y)) as [p H1].
  destruct (constructive_indefinite_description _ H1) as [q H2].
  exact (embed (m*p+n*q) (n*p+m*q)).
Defined.

Definition neg : Z → Z.
Proof.
  intros x.
  destruct (constructive_indefinite_description _ (embed_surj x)) as [a H].
  destruct (constructive_indefinite_description _ H) as [b H0].
  exact (embed b a).
Defined.

Definition zero := INZ 0.
Definition one := INZ 1.

Notation "0" := zero.
Notation "1" := one.
Infix "+" := add.
Infix "*" := mul.
Notation "- a" := (neg a).

Theorem add_Z_wf : ∀ a b c d, (embed a b) + (embed c d) = embed (a+c) (b+d).
Proof.
  intros a b c d.
  unfold add.
  repeat destruct constructive_indefinite_description.
  rewrite embed_kernel in *.
  now rewrite (add_comm b), ? add_assoc, <-(add_assoc x), e2, (add_comm x),
  <-? add_assoc, e0, 2 (add_comm x0), (add_assoc c), (add_comm c),
  ? add_assoc.
Qed.

Theorem A1 : ∀ a b, a + b = b + a.
Proof.
  intros a b.
  unfold add.
  repeat destruct constructive_indefinite_description.
  now rewrite embed_kernel, (add_comm (x+x1)), (add_comm x2), (add_comm x).
Qed.

Theorem A2 : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  intros a b c.
  unfold add.
  repeat destruct constructive_indefinite_description.
  rewrite embed_kernel in *.
  rewrite add_assoc, (add_comm x6) in e6.
  rewrite (add_comm x7), (add_comm x8) in e8.
  apply (cancellation_add _ _ x2).
  now rewrite (add_comm _ x2), 3 add_assoc, (add_comm _ x8), ? add_assoc,
  (add_comm _ x), (add_comm x8), ? add_assoc, <-e8, (add_comm _ x2),
  ? add_assoc, (add_comm _ x4), ? add_assoc, (add_comm x4), (add_comm _ x6),
  ? add_assoc, <-(add_assoc x6), (add_comm x6), <-e6, (add_comm _ x1),
  <-? (add_assoc), (add_comm _ x5), (add_assoc x3), (add_comm x0),
  <-? add_assoc, (add_comm x7).
Qed.

Theorem A3 : ∀ a, a + 0 = a.
Proof.
  intros a.
  unfold add.
  repeat destruct constructive_indefinite_description.
  unfold zero, INZ in e2.
  now rewrite <-e0, embed_kernel, ? add_0_r, e2,
  add_comm, (add_comm x), add_assoc in *.
Qed.

Theorem neg_Z_wf : ∀ a b, - embed a b = embed b a.
Proof.
  intros a b.
  unfold neg.
  repeat destruct constructive_indefinite_description.
  now rewrite embed_kernel in *.
Qed.

Theorem A4 : ∀ a, a + -a = 0.
Proof.
  intros a.
  unfold add, neg.
  repeat destruct constructive_indefinite_description.
  unfold zero, INZ.
  now rewrite embed_kernel, ? add_0_r, (add_comm x), (add_comm x0) in *.
Qed.

Theorem M1 : ∀ a b, a * b = b * a.
Proof.
  intros a b.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  now rewrite embed_kernel, add_comm, (add_comm (x0*x1)),
  (mul_comm x), (mul_comm x0), (mul_comm x1), (mul_comm x2).
Qed.

Theorem mul_Z_wf : ∀ a b c d,
    (embed a b) * (embed c d) = embed (a*c+b*d) (b*c+a*d).
Proof.
  intros a b c d.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  rewrite embed_kernel in *.
  apply (cancellation_add _ _ (b*x1)), (cancellation_add _ _ (b*x2)).
  rewrite <-? add_assoc, (add_comm (b*x1)), ? add_assoc,
  (add_comm _ (b*x1)), (add_comm (x0 * x1 + x * x2 + a * c + b * d + b * x1)),
  (add_comm _ (x*x2)), ? add_assoc, <-? mul_distr_r at 1.
  rewrite (add_comm b), e0.
  replace ((x0 + a) * x1 + x0 * x2 + b * c + a * d + b * x2)%N
    with (a * (x1 + d) + b * (x2 + c) + x0 * (x1 + x2))%N.
  - now rewrite e2, (add_comm (a*(x2+c))), <-e2, ? mul_distr_l, ? mul_distr_r,
    (add_comm _ (b*x1)), (add_comm (x0*x2 + a*x2 + x0*x1 + a*c)),
    (add_comm (x0*x2)), <-? add_assoc, (add_assoc (x0*x2)), (add_comm _ (a*c)),
    (add_comm (x0*x2)) at 1.
  - now rewrite ? mul_distr_l, ? mul_distr_r, (add_comm _ (a*x1)), <-add_assoc,
    (add_comm _ (x0*x1 + x0*x2)), <-? add_assoc, (add_assoc (x0*x1)),
    (add_assoc (a*d)), (add_comm (a*d)), (add_comm (b*c)), ? add_assoc.
Qed.

Theorem M2 : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  intros a b c.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  rewrite <-? mul_Z_wf, e6, e8, ? mul_Z_wf.
  rewrite embed_kernel, ? mul_distr_r, ? mul_distr_l, ? add_assoc, ? mul_assoc,
  (add_comm (x*x2*x4)), ? add_assoc, (add_comm _ (x*x3*x5)), <-? add_assoc.
  apply f_equal.
  rewrite ? add_assoc, <-(add_assoc (x*x2*x4)), (add_comm (x*x2*x4)),
  (add_comm (x0*x3*x4)), (add_comm _ (x0*x2*x5)), ? add_assoc,
  (add_comm _ (x0*x3*x4)), ? add_assoc, (add_comm _ (x0*x3*x4)), <-? add_assoc.
  repeat apply f_equal.
  now rewrite ? add_assoc, (add_comm _ (x*x2*x4)), <-? add_assoc,
  (add_comm (x0*x3*x5)), ? add_assoc.
Qed.

Theorem M3 : ∀ a, a * 1 = a.
Proof.
  intros a.
  unfold mul.
  repeat destruct constructive_indefinite_description.
  replace 1 with (embed 1 0) in *; auto.
  rewrite <-e0, embed_kernel in *.
  rewrite add_0_r in e2.
  subst.
  now rewrite ? mul_distr_l, ? mul_1_r, <-add_assoc,
  (add_comm (x*x2+x)), ? add_assoc.
Qed.

Theorem D1 : ∀ a b c, a * (b + c) = a * b + a * c.
Proof.
  intros a b c.
  unfold mul, add.
  repeat destruct constructive_indefinite_description.
  now rewrite <-mul_Z_wf, <-add_Z_wf, e6, e8, e10, ? mul_Z_wf, ? add_Z_wf,
  ? mul_Z_wf, embed_kernel, ? mul_distr_l, ? add_assoc, <-3 add_assoc,
  add_comm, (add_assoc (x*x3)), (add_comm (x*x3)), <-(add_assoc (x*x2)),
  (add_comm (x*x4)), ? add_assoc.
Qed.

Definition integers := mkRing _ add mul zero one neg A1 A2 A3 A4 M1 M2 M3 D1.

