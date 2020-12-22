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

Theorem INZ_add : ∀ a b : N, a+b = (a+b)%N.
Proof.
  intros a b.
  unfold add, INZ.
  repeat destruct constructive_indefinite_description.
  now rewrite embed_kernel, add_0_r, e0, e2, add_assoc,
  <-(add_assoc x0), (add_comm a), ? add_assoc in *.
Qed.

Theorem INZ_mul : ∀ a b : N, a*b = (a*b)%N.
Proof.
  intros a b.
  unfold mul, INZ.
  repeat destruct constructive_indefinite_description.
  rewrite embed_kernel, add_0_r, e0, e2 in *.
  rewrite ? mul_distr_r, <-? add_assoc.
  apply f_equal.
  now rewrite ? mul_distr_l, add_comm.
Qed.

Theorem INZ_inj : ∀ a b : N, INZ a = INZ b ↔ a = b.
Proof.
  intros a b.
  split; intros H; try now subst.
  apply embed_kernel in H.
  now rewrite ? add_0_l, ? add_0_r in H.
Qed.

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

Definition lt : Z → Z → Prop.
Proof.
  intros x y.
  destruct (constructive_indefinite_description _ (embed_surj x)) as [a H].
  destruct (constructive_indefinite_description _ H) as [b H0].
  destruct (constructive_indefinite_description _ (embed_surj y)) as [c H1].
  destruct (constructive_indefinite_description _ H1) as [d H2].
  exact (a+d < b+c).
Defined.

Infix "<" := lt.
Notation "a > b" := (b < a) (only parsing).
Notation "x < y < z" := (x < y ∧ y < z).

Theorem T : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ (a > b)) ∨
                   (¬ (a < b) ∧ a = b ∧ ¬ (a > b)) ∨
                   (¬ (a < b) ∧ a ≠ b ∧ a > b).
Proof.
  intros a b.
  unfold lt.
  repeat destruct constructive_indefinite_description.
  subst.
  unfold not.
  rewrite embed_kernel, ? (add_comm x1), ? (add_comm x2).
  eauto using trichotomy.
Qed.

Theorem lt_def : ∀ a b, a < b ↔ ∃ c : N, 0 ≠ c ∧ b = a + c.
Proof.
  intros a b.
  split; intros H; unfold lt, INZ in *;
    repeat destruct constructive_indefinite_description; rewrite lt_def in *;
      replace 0 with (embed 0 0) in *; auto.
  - destruct H as [z [H H0]].
    exists z.
    subst.
    split.
    + contradict H.
      now rewrite embed_kernel, ? add_0_r, ? add_0_l in H.
    + now rewrite add_Z_wf, embed_kernel, add_0_r,
      add_comm, add_assoc, (add_comm x2).
  - destruct H as [c [H H0]].
    exists c.
    split.
    + contradict H.
      now subst.
    + subst.
      rewrite add_Z_wf, embed_kernel, add_0_r in e2.
      now rewrite (add_comm x0), e2, ? add_assoc, (add_comm x).
Qed.

Theorem lt_trans : ∀ a b c, a < b → b < c → a < c.
Proof.
  intros a b c H H0.
  rewrite lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  exists (x+y)%N.
  split.
  - intros H3.
    apply INZ_inj, eq_sym, cancellation_0_add in H3 as [H3 H4]; subst; auto.
  - subst.
    now rewrite <-A2, INZ_add.
Qed.

Theorem O1 : ∀ a b c, a < b → a + c < b + c.
Proof.
  intros a b c H.
  rewrite lt_def in *.
  destruct H as [x [H H0]].
  exists x.
  split; auto.
  now rewrite H0, <-A2, (A1 _ c), A2.
Qed.

Theorem O2 : ∀ a b, 0 < a → 0 < b → 0 < a * b.
Proof.
  intros a b H H0.
  rewrite lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  exists (x*y)%N.
  split.
  - intros H3.
    unfold lt in *.
    repeat destruct constructive_indefinite_description.
    subst.
    apply INZ_inj, eq_sym, cancellation_0_mul in H3 as [H3 | H3]; subst; auto.
  - subst.
    now rewrite ? (A1 0), ? A3, INZ_mul.
Qed.

Theorem O3 : ∀ a b c, a < b → 0 < c → a * c < b * c.
Proof.
  intros a b c H H0.
  rewrite lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  rewrite (A1 0), A3 in *.
  subst.
  exists (x*y)%N.
  split.
  - intros H1.
    apply INZ_inj, eq_sym, cancellation_0_mul in H1 as [H1 | H1]; subst; auto.
  - now rewrite M1, D1, ? (M1 y), INZ_mul.
Qed.

Theorem INZ_lt : ∀ a b : N, INZ a < INZ b ↔ (a < b)%N.
Proof.
  intros a b.
  Set Printing Coercions.
  split; intros H; rewrite lt_def, peano_axioms.lt_def in *;
    destruct H as [c [H H0]]; exists c; split.
  - contradict H.
    now subst.
  - now rewrite INZ_add, INZ_inj in H0.
  - contradict H.
    now apply INZ_inj in H.
  - subst.
    now rewrite INZ_add.
Qed.

Theorem lt_0_1 : ∀ a, ¬ (0 < a < 1).
Proof.
  intros a [H H0].
  rewrite lt_def in *.
  destruct H as [x [H H1]], H0 as [y [H0 H2]].
  contradiction (peano_axioms.lt_0_1 x).
  split; rewrite peano_axioms.lt_def.
  - exists x; rewrite (A1 0), A3, add_0_l in *; subst.
    split; auto.
    contradict H.
    now subst.
  - exists y.
    split.
    + contradict H0.
      now subst.
    + rewrite (A1 0), A3 in *.
      subst.
      now rewrite <-INZ_inj, <-INZ_add.
Qed.

Theorem lt_n_Sn : ∀ x n, 0 < x < S n → x < n ∨ x = n.
Proof.
  intros x n H.
  destruct (T x n); intuition; try tauto.
  rewrite lt_def in *.
  destruct H1 as [a [H1 H3]], H2 as [b [H2 H5]], H4 as [c [H4 H6]].
  subst.
  rewrite ? (A1 0), ? A3 in *.
  rewrite H6, <-add_1_r, ? INZ_add, INZ_inj, <-? add_assoc,
  ? (add_comm n) in H5.
  apply cancellation_add, eq_sym, cancellation_1_add in H5 as [H5 | H5];
    subst; [ contradiction H4 | contradiction H2 ]; auto.
Qed.

Theorem strong_induction : ∀ P : Z → Prop,
    (∀ x : Z, (∀ y : Z, 0 < y < x → P y) → P x) → ∀ a : Z, P a.
Proof.
  intros P H x.
  destruct (T x 0) as [[H0 [H1 H2]] | [[H0 [H1 H2]] | [H0 [H1 H2]]]];
    try now (apply H; intros y [H3 H4]; contradict H2; eauto using lt_trans).
  rewrite lt_def in H2.
  destruct H2 as [c [H2 H3]].
  subst.
  rewrite (A1 0), A3 in *.
  apply (Induction (λ x : N, P x ∧ ∀ y : N, 0 < y ∧ y < x → P y))%N.
  - split.
    + apply H.
      intros y [H3 H4].
      contradiction (lt_irrefl 0).
      eapply INZ_lt, lt_trans; eauto.
    + intros y [H3 H4].
      contradiction (lt_irrefl 0).
      eapply peano_axioms.lt_trans; eauto.
  - intros n [H3 H4].
    split.
    + apply H.
      intros y [H5 H6].
      pose proof lt_n_Sn _ _ (conj H5 H6) as [H7 | H7].
      * apply H.
        intros z [H8 H9].
        rewrite lt_def in H8.
        destruct H8 as [d [H8 H10]].
        rewrite H10, A1, A3 in *.
        subst.
        apply H4.
        split.
        -- split.
           ++ exists d.
              now rewrite add_0_l.
           ++ contradict H8.
              now subst.
        -- apply INZ_lt.
           eauto using lt_trans.
      * now subst.
    + intros y H5.
      assert (0 < y < S n) as H6 by (split; apply INZ_lt; intuition).
      apply lt_n_Sn in H6 as [H6 | H6].
      * apply H4.
        split; intuition.
        now apply INZ_lt.
      * now rewrite H6.
Qed.

Definition integers := mkRing _ add mul zero one neg A1 A2 A3 A4 M1 M2 M3 D1.
