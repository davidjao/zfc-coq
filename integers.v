Require Export peano_axioms.

Record ring := mkRing {
                   set_R : set;
                   add_R : elts set_R → elts set_R → elts set_R;
                   mul_R : elts set_R → elts set_R → elts set_R;
                   A1_R : ∀ a b, add_R a b = add_R b a;
                   A2_R : ∀ a b c, add_R a (add_R b c) = add_R (add_R a b) c;
                   A3_R : ∃ zero_R, ∀ a, add_R a zero_R = a;
                   A4_R : ∀ a,
                       ∃ b, add_R a b =
                            (let s :=
                                 (constructive_indefinite_description
                                    (λ a : elts set_R, ∀ x, add_R x a = x) A3_R)
                             in let (z, _) := s in z);
                   M1_R : ∀ a b, mul_R a b = mul_R b a;
                   M2_R : ∀ a b c, mul_R a (mul_R b c) = mul_R (mul_R a b) c;
                   M3_R : ∃ one_R, ∀ a, mul_R a one_R = a;
                   D1_R : ∀ a b c, mul_R a (add_R b c) = add_R (mul_R a c) (mul_R b c);
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
    destruct H2 as [H2 [a [b [c [d [H4 H5]]]]]].
    destruct H3 as [H3 [e [f [g [h [H6 H7]]]]]].
    split.
    + apply Product_classification.
      now exists x, z.
    + exists a, b, g, h.
      split; rewrite Ordered_pair_iff in *; intuition.
      assert ((value ω c, value ω d) = (value ω e, value ω f)) by congruence.
      apply Ordered_pair_iff in H6 as [H6 H11].
      assert (c = e) as H12 by now apply set_proj_injective.
      assert (d = f) as H13 by now apply set_proj_injective.
      rewrite H12, H13 in H5.
      assert (a + f + g = b + e + g) as H14 by congruence.
      rewrite <-? add_assoc, <-H7, ? (add_comm e), ? add_assoc in H14.
      now apply cancellation_add in H14.
Qed.

Definition Zset := ω × ω.

Definition proto_Z := elts Zset.

Definition Z := elts (Zset / integer_relation).

Definition cl : proto_Z → Z := (quotient_map Zset integer_relation).

Coercion cl : proto_Z >-> Z.

Definition Zequiv a b := cl a = cl b.

Infix "~" := Zequiv (at level 60).

Definition INZ : N → Z.
Proof.
  intros [_ a H].
  assert ((a,∅) ∈ ω × ω) as H0 by
        (apply Product_classification; eauto using PA1_ω).
  exact (quotient_map (ω × ω) integer_relation (mkSet (ω × ω) (a,∅) H0)).
Defined.

Coercion INZ : N >-> Z.

Definition proto_add : proto_Z → proto_Z → proto_Z.
Proof.
  intros [_ a A] [_ b B].
  apply Product_classification in A.
  apply Product_classification in B.
  destruct (constructive_indefinite_description _ A) as [a1 A1].
  destruct (constructive_indefinite_description _ A1) as [a2 [A2 [A3 A4]]].
  destruct (constructive_indefinite_description _ B) as [b1 B1].
  destruct (constructive_indefinite_description _ B1) as [b2 [B2 [B3 B4]]].
  set (c1 := mkSet ω a1 A2).
  set (c2 := mkSet ω a2 A3).
  set (d1 := mkSet ω b1 B2).
  set (d2 := mkSet ω b2 B3).
  assert ((value ω (c1+d1), value ω (c2+d2)) ∈ ω × ω) as H.
  { apply Product_classification.
    exists (value ω (c1 + d1)), (value ω (c2 + d2)).
    auto using in_set. }
  exact (mkSet (ω × ω) (value ω (c1+d1), value ω (c2+d2)) H).
Defined.

Infix "(+)" := proto_add (at level 50).

Theorem proto_add_comm : ∀ a b, a (+) b = b (+) a.
Proof.
  intros [_ a A] [_ b B].
  unfold proto_Z, proto_add, Zset in *.
  repeat destruct constructive_indefinite_description.
  destruct a0 as [H [H0 H1]].
  destruct a1 as [H2 [H3 H4]].
  destruct e as [y [H5 [H6 H7]]].
  destruct e0 as [z [H8 [H9 H10]]].
  rewrite Product_classification in *.
  destruct A as [a1 [a2 [H11 [H12 H13]]]].
  destruct B as [b1 [b2 [H14 [H15 H16]]]].
  apply set_proj_injective.
  simpl.
  now rewrite add_comm, (add_comm {| value := x0; in_set := H0 |}).
Qed.

Theorem proto_add_assoc : ∀ a b c, a (+) (b (+) c) = (a (+) b) (+) c.
Proof.
  intros [_ a A] [_ b B] [_ c C].
  unfold proto_Z, proto_add, Zset in *.
  repeat destruct constructive_indefinite_description.
  destruct a0 as [H [H0 H1]].
  destruct a1 as [H2 [H3 H4]].
  destruct a2 as [H5 [H6 H7]].
  destruct e as [d [H8 [H9 H10]]].
  destruct e0 as [e [H11 [H12 H13]]].
  destruct e1 as [f [H14 [H15 H16]]].
  rewrite Product_classification in *.
  destruct A as [a1 [a2 [H17 [H18 H19]]]].
  destruct B as [b1 [b2 [H20 [H21 H22]]]].
  repeat destruct constructive_indefinite_description.
  destruct e0 as [g [H23 [H24 H25]]].
  destruct a0 as [H26 [H27 H28]].
  destruct e1 as [h [H29 [H30 H31]]].
  destruct a3 as [H32 [H33 H34]].
  destruct e2 as [i [H35 [H36 H37]]].
  destruct a4 as [H38 [H39 H40]].
  rewrite Product_classification in *.
  destruct C as [c1 [c2 [H41 [H42 H43]]]].
  apply set_proj_injective.
  simpl.
  assert ((x1, e) = (x9, i)) by congruence.
  assert ((x1, x2) = (x9, x10)) by congruence.
  rewrite Ordered_pair_iff in *.
  set (X := {| value := x; in_set := H |}) in *.
  set (X0 := {| value := x0; in_set := H0 |}) in *.
  set (X1 := {| value := x1; in_set := H2 |}) in *.
  set (X2 := {| value := x2; in_set := H3 |}) in *.
  set (X3 := {| value := x3; in_set := H5 |}) in *.
  set (X4 := {| value := x4; in_set := H6 |}) in *.
  set (X5 := {| value := x5; in_set := H26 |}) in *.
  set (X6 := {| value := x6; in_set := H27 |}) in *.
  set (X7 := {| value := x7; in_set := H32 |}) in *.
  set (X8 := {| value := x8; in_set := H33 |}) in *.
  set (X9 := {| value := x9; in_set := H38 |}) in *.
  set (X10 := {| value := x10; in_set := H39 |}) in *.
  intuition.
  - replace X5 with (X + X1)%N; replace X7 with (X3 + X)%N;
      replace X9 with X1; try now apply set_proj_injective.
    now rewrite add_assoc.
  - replace X6 with (X0 + X2)%N; replace X8 with (X4 + X0)%N;
      replace X10 with X2; try now apply set_proj_injective.
    now rewrite add_assoc.
Qed.

Definition add : Z → Z → Z.
Proof.
  intros a b.
  destruct (constructive_indefinite_description _ (quotient_lift _ _ a)) as [x].
  destruct (constructive_indefinite_description _ (quotient_lift _ _ b)) as [y].
  exact (quotient_map _ _ (x (+) y)).
Defined.

Infix "+" := add.

Theorem add_wf_lr : ∀ a b c,
    cl a = cl b →
    value (Zset / integer_relation) (cl (a (+) c)) ⊂
    value (Zset / integer_relation) (cl (b (+) c)).
Proof.
  intros [_ a A] [_ b B] [_ c C] H.
  unfold proto_Z, proto_add, Zset in *.
  repeat destruct constructive_indefinite_description.
  destruct a0 as [H0 [H1 H2]].
  destruct a1 as [H3 [H4 H5]].
  destruct a2 as [H6 [H7 H8]].
  destruct e as [d [H9 [H10 H11]]].
  destruct e0 as [e [H12 [H13 H14]]].
  destruct e1 as [f [H15 [H16 H17]]].
  simpl.
  apply quotient_wf in H; auto using integer_equivalence.
  assert (d = x0).
  { eapply Ordered_pair_iff; eauto; eapply eq_trans; symmetry; eauto. }
  assert (e = x2).
  { eapply Ordered_pair_iff; eauto; eapply eq_trans; symmetry; eauto. }
  assert (f = x4).
  { eapply Ordered_pair_iff; eauto; eapply eq_trans; symmetry; eauto. }
  subst.
  set (X := {| value := x; in_set := H0 |}) in *.
  set (X0 := {| value := x0; in_set := H1 |}) in *.
  set (X1 := {| value := x1; in_set := H3 |}) in *.
  set (X2 := {| value := x2; in_set := H4 |}) in *.
  set (X3 := {| value := x3; in_set := H6 |}) in *.
  set (X4 := {| value := x4; in_set := H7 |}) in *.
  intros z H11; rewrite Specify_classification in *;
    unfold Zset, integer_relation in *; split; try tauto; destruct H11;
      rewrite Specify_classification in *.
  destruct H14 as [H14 [a [b [c [d [H17 H18]]]]]].
  split; auto.
  destruct H as [H [a0 [b0 [c0 [d0 [H21 H22]]]]]].
  simpl in *.
  - apply Product_classification.
    exists ((value ω (X3 + X1)), (value ω (X4 + X2)))%N, z.
    repeat split; auto.
    apply Product_classification.
    eauto using in_set.
  - apply Product_classification in H11 as [z1 [z2 [H11 [H19 H20]]]].
    destruct H as [H [a0 [b0 [c0 [d0 [H21 H22]]]]]].
    subst.
    simpl in *.
    exists (X3+X1)%N, (X4+X2)%N, c, d.
    repeat rewrite Ordered_pair_iff in H17, H21.
    destruct H17 as [[H20 H23] [H24 H25]].
    destruct H21 as [[H26 H27] [H28 H29]].
    replace a with (X + X1)%N in *; replace b with (X0 + X2)%N in *;
      replace a0 with X in *; replace b0 with X0 in *;
        replace c0 with X3 in *; replace d0 with X4 in *;
          try now apply set_proj_injective.
    split; try congruence.
    eapply (cancellation_add _ _ (X+X4)%N).
    rewrite H22 at 2.
    now rewrite ? add_assoc, <-2 (add_assoc X3), (add_comm _ X), (add_assoc X),
    H18, 2 (add_assoc X3), <-2 (add_assoc (X3 + X0)), (add_comm (X3 + X0)),
    (add_comm X3), (add_comm _ X4), ? add_assoc.
Qed.

Theorem add_wf : ∀ a b c, cl a = cl b → cl (a (+) c) = cl (b (+) c).
Proof.
  intros a b c H.
  apply set_proj_injective, Subset_equality_iff.
  eauto using add_wf_lr.
Qed.

Theorem A1 : ∀ a b, a + b = b + a.
Proof.
  intros a b.
  unfold add.
  repeat destruct constructive_indefinite_description.
  now rewrite proto_add_comm.
Qed.

Theorem A2 : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  intros a b c.
  unfold add.
  repeat destruct constructive_indefinite_description.
  rewrite proto_add_comm, (add_wf x3 (x (+) x1)), (add_wf x0 (x1 (+) x2)),
  proto_add_comm, proto_add_assoc; auto.
Qed.

Theorem proto_zero : ∃ z, ∀ a, a (+) z = a.
Proof.
  assert ((∅, ∅) ∈ ω × ω).
  { apply Product_classification.
    exists ∅, ∅.
    split; auto using PA1_ω. }
  exists (mkSet (ω × ω) (∅, ∅) H).
  intros [a A].
  unfold proto_Z, proto_add, Zset in *.
  repeat destruct constructive_indefinite_description.
  destruct e as [b [H0 [H1 H2]]].
  destruct e0 as [c [H3 [H4 H5]]].
  destruct a0 as [H6 [H7 H8]].
  destruct a1 as [H9 [H10 H11]].
  apply set_proj_injective.
  simpl.
  set (X := {| value := x; in_set := H6 |}) in *.
  set (X0 := {| value := x0; in_set := H7 |}) in *.
  set (X1 := {| value := x1; in_set := H9 |}) in *.
  set (X2 := {| value := x2; in_set := H10 |}) in *.
  rewrite Ordered_pair_iff in *; intuition.
  replace X1 with 0; replace X2 with 0;
    try now apply set_proj_injective.
  now rewrite ? add_0_r.
Qed.

Theorem A3 : ∃ z, ∀ a, a + z = a.
Proof.
  destruct proto_zero as [z H].
  exists (quotient_map (ω × ω) integer_relation z).
  intros a.
  unfold add.
  repeat destruct constructive_indefinite_description.
  rewrite proto_add_comm, (add_wf _ z); auto.
  now rewrite proto_add_comm, H.
Qed.
