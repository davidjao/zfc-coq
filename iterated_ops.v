Require Export naturals.

Section Iterated_op_construction.

  Variable X : set.
  Definition R := (elts X).
  Variable op : R → R → R.
  Variable start : R.
  Definition IRS (r : R) := (elt_to_set _ r) : set.
  Coercion IRS : R >-> set.

  Variable f : function.
  Variable n : N.

  Infix "·" := op (at level 40, left associativity).

  Hypothesis dom_f : domain f = n.
  Hypothesis ran_f : range f = X.

  Theorem proto_iterop_exists :
    ∃ g, domain g = S n ∧ range g = X ∧ (g 0%N) = start ∧
         ∀ m : N, m < n → ∃ r s t : R,
             (g (S m)) = r ∧ (g m) = s ∧ (f m) = t ∧ r = s · t.
  Proof.
    revert f dom_f ran_f.
    induction n using Induction; try now intuition.
    { destruct (function_construction 1%N X (λ x, start))
        as [g [H [H0 H1]]].
      { intros a H.
        apply (proj2_sig start). }
      exists g.
      repeat split; eauto.
      - apply H1.
        apply lt_is_in, lt_succ.
      - intros m H2.
        apply lt_is_in in H2.
        unfold INS in H2.
        simpl in H2.
        contradiction (Empty_set_classification m). }
    intros f dom_f ran_f.
    clear n; rename n0 into n; rename IHn0 into IHn.
    destruct (function_construction n (range f) (λ x, (f x)))
      as [f_n [H [H0 H1]]].
    { intros a H.
      apply function_maps_domain_to_range.
      rewrite dom_f.
      pose proof succ_lt n as [H0 _].
      rewrite le_is_subset in H0.
      eauto. }
    destruct (IHn f_n) as [g_n [H2 [H3 [H4 H5]]]]; try congruence.
    assert (g_n n ∈ X) as H6.
    { rewrite <-H3.
      apply function_maps_domain_to_range.
      rewrite H2.
      apply lt_is_in, succ_lt. }
    assert (f n ∈ X) as H7.
    { rewrite <-ran_f.
      apply function_maps_domain_to_range.
      rewrite dom_f.
      apply lt_is_in, succ_lt. }
    destruct
    (function_construction
       (S (S n)) X
       (λ x, if (excluded_middle_informative (x = S n))
             then (((exist _ _ H6) · (exist _ _ H7)) : R) else (g_n x)))
      as [g [H8 [H9 H10]]].
    { intros a H8.
      rewrite <-S_is_succ in H8.
      apply Pairwise_union_classification in H8 as [H8 | H8];
        destruct excluded_middle_informative.
      - rewrite e in H8.
        contradiction (no_quines (S n)).
      - rewrite <-H3.
        apply function_maps_domain_to_range.
        congruence.
      - apply (proj2_sig (((exist _ _ H6) · (exist _ _ H7)) : R)).
      - contradict n0.
        now apply Singleton_classification in H8. }
    exists g.
    repeat split; auto.
    { rewrite H10.
      - destruct excluded_middle_informative; auto.
        apply set_proj_injective in e.
        contradiction (PA4 n).
      - apply lt_is_in, lt_succ. }
    intros m H11.
    rewrite lt_is_in, <-S_is_succ in H11.
    apply Pairwise_union_classification in H11 as [H11 | H11].
    - apply lt_is_in in H11.
      pose proof H11 as H12.
      apply H5 in H12 as [r [s [t [H12 [H13 [H14 H15]]]]]].
      exists r, s, t.
      repeat split; auto.
      + rewrite H10.
        * destruct excluded_middle_informative; auto.
          apply set_proj_injective, PA5 in e.
          rewrite e in H11.
          contradiction (lt_irrefl n).
        * rewrite <-lt_is_in, <-S_lt.
          apply (lt_trans _ n); auto using succ_lt.
      + rewrite H10.
        * destruct excluded_middle_informative; auto.
          apply set_proj_injective in e.
          rewrite e in H11.
          contradiction (lt_antisym n (S n)).
          apply succ_lt.
        * rewrite <-lt_is_in.
          apply (lt_trans _ n); auto.
          apply (lt_trans _ (S n)); auto using succ_lt.
      + rewrite <-H1; auto.
        now apply lt_is_in.
    - rewrite Singleton_classification in H11.
      apply set_proj_injective in H11.
      rewrite H11.
      exists (((exist _ _ H6) · (exist _ _ H7)) : R), (exist _ _ H6 : R),
      (exist _ _ H7 : R).
      repeat split; auto.
      + rewrite H10.
        * now destruct excluded_middle_informative.
        * rewrite <-lt_is_in, <-S_lt.
          apply succ_lt.
      + rewrite H10.
        * destruct excluded_middle_informative; auto.
          apply set_proj_injective in e.
          contradiction (lt_irrefl n).
          rewrite e at 2.
          apply succ_lt.
        * rewrite <-lt_is_in.
          apply (lt_trans _ (S n)); auto using succ_lt.
  Qed.

  Definition proto_iterop : R.
  Proof.
    destruct (constructive_indefinite_description _ proto_iterop_exists)
      as [g [H [H0 [H1 H2]]]].
    assert (n ∈ domain g) as H3.
    { rewrite H, <-lt_is_in.
      apply succ_lt. }
    assert (∃ r : R, g n = r) as H4.
    { assert (g n ∈ X).
      { rewrite <-H0.
        now apply function_maps_domain_to_range. }
      now exists (exist _ _ H4 : R). }
    destruct (constructive_indefinite_description _ H4) as [r H5].
    exact r.
  Defined.

End Iterated_op_construction.

Section Iterated_op.
  Variable X : set.
  Notation R := (elts X).
  Variable op : R → R → R.
  Variable start : R.

  Variable f : N → R.

  Infix "·" := op (at level 40, left associativity).

  Definition iterated_op : N → R.
  Proof.
    intros n.
    assert (∀ a, a ∈ n → (λ x : set, (functionify _ _ f x)) a ∈ X) as H.
    { intros a H.
      unfold functionify.
      destruct constructive_indefinite_description as [f' [H0 [H1 H2]]].
      rewrite <-H1.
      apply function_maps_domain_to_range.
      rewrite H0.
      eapply elements_of_naturals_are_naturals; eauto; apply (proj2_sig n). }
    destruct (constructive_indefinite_description
                _ (function_construction n X (λ x, (functionify _ _ f x)) H))
      as [h [H0 [H1 H2]]].
    destruct (constructive_indefinite_description
                _ (proto_iterop_exists X op start h n H0 H1))
      as [g [H3 [H4 [H5 H6]]]].
    assert (∃ r : R, g n = IRS X r) as H7.
    { assert (g n ∈ X).
      { rewrite <-H4.
        apply function_maps_domain_to_range.
        rewrite H3.
        apply lt_is_in, succ_lt. }
      now exists (exist _ _ H7 : R). }
    destruct (constructive_indefinite_description _ H7) as [r H8].
    exact r.
  Defined.

  Theorem iterated_op_0 : iterated_op 0 = start.
  Proof.
    unfold iterated_op.
    repeat (destruct constructive_indefinite_description;
            repeat destruct a).
    unfold IRS in *.
    apply set_proj_injective.
    congruence.
  Qed.

  Theorem iterated_op_succ : ∀ n, iterated_op (S n) = iterated_op n · (f n).
  Proof.
    induction n using Induction.
    - unfold iterated_op.
      repeat (destruct constructive_indefinite_description;
              repeat destruct a).
      destruct (e5 0%N) as [r [s [t [H [H0 [H1 H2]]]]]]; auto using succ_lt.
      unfold IRS in *.
      replace x1 with r.
      2: { apply set_proj_injective.
           now rewrite <-H, e6. }
      replace x4 with s.
      2: { apply set_proj_injective.
           now rewrite <-H0, e4, <-e12, e14. }
      replace (f 0) with t; auto.
      apply set_proj_injective.
      rewrite <-H1, e1.
      + unfold functionify.
        destruct constructive_indefinite_description.
        destruct a as [H3 [H4 H5]].
        now rewrite H5.
      + apply lt_is_in, succ_lt.
    - rewrite IHn.
      unfold iterated_op.
      repeat (destruct constructive_indefinite_description;
              repeat destruct a).
      assert (∀ m, m < n → x m = x2 m) as E.
      { intros m H.
        rewrite e1, e9; auto.
        - now apply lt_is_in.
        - apply lt_is_in.
          eauto using lt_is_in, lt_trans, succ_lt. }
      assert (∀ m, m < n → x0 m = x3 m) as E0.
      { induction m using Induction; intros H0; try congruence.
        assert (m < n) by eauto using lt_trans, succ_lt.
        apply IHm in H as H1.
        apply E in H as H2.
        assert (m < S (S n)) by eauto using lt_trans, succ_lt.
        apply e13 in H as [r [s [t [H4 [H5 [H6 H7]]]]]].
        apply e5 in H3 as [r' [s' [t' [H8 [H9 [H10 H11]]]]]].
        rewrite H4, H8, H7, H11.
        f_equal.
        unfold IRS in *.
        replace s with s'.
        replace t with t'; auto.
        - apply set_proj_injective.
          congruence.
        - apply set_proj_injective.
          congruence. }
      destruct (e5 (S n)) as [r [s [t [H [H0 [H1 H2]]]]]]; auto using succ_lt.
      unfold IRS in *.
      assert (t = (f (S n))).
      { apply set_proj_injective.
        rewrite <-H1, e1.
        - unfold functionify.
          destruct constructive_indefinite_description.
          destruct a as [H3 [H4 H5]].
          now rewrite H5.
        - rewrite <-lt_is_in, <-S_lt.
          apply succ_lt. }
      destruct (e5 n)
        as [r' [s' [t' [H4 [H5 [H6 H7]]]]]]; eauto using lt_trans, succ_lt.
      assert (r' = s).
      { apply set_proj_injective.
        congruence. }
      rewrite H8 in *.
      assert (t' = f n).
      { apply set_proj_injective.
        rewrite <-H6, e1.
        - unfold functionify.
          destruct constructive_indefinite_description.
          destruct a as [H9 [H10 H11]].
          now rewrite H11.
        - rewrite <-lt_is_in.
          eauto using lt_trans, succ_lt. }
      assert (s' = x4) as H10.
      { apply set_proj_injective.
        rewrite <-e14.
        destruct (classic (n = 0%N)) as [H10 | H10].
        { rewrite H10 in *.
          congruence. }
        apply succ_0 in H10 as [k H10].
        rewrite H10 in *.
        destruct (e13 k) as [r'' [s'' [t'' [H11 [H12 [H13 H14]]]]]];
          auto using succ_lt.
        rewrite <-H5, H11, H14.
        rewrite <-E0 in H12; auto using succ_lt.
        rewrite <-E in H13; auto using succ_lt.
        destruct (e5 k) as [r''' [s''' [t''' [H15 [H16 [H17 H18]]]]]];
          eauto using lt_trans, succ_lt.
        rewrite H15, H18.
        replace s'' with s'''; replace t'' with t''';
          auto; apply set_proj_injective; congruence. }
      apply set_proj_injective.
      rewrite <-e6, H.
      congruence.
  Qed.

End Iterated_op.

Section Iterated_op_theorems.

  Variable X : set.
  Notation R := (elts X).

  Definition iterate_with_bounds : (R → R → R) → (N → R) → R → N → N → R.
  Proof.
    intros op f start a b.
    destruct (excluded_middle_informative (a ≤ b)).
    - destruct (constructive_indefinite_description _ l) as [c H].
      exact (iterated_op X op (f a) (λ x, f (a + x + 1)%N) c).
    - exact start.
  Defined.

  Theorem iterate_0 : ∀ op f start a, iterate_with_bounds op f start a a = f a.
  Proof.
    intros op f start a.
    unfold iterate_with_bounds.
    destruct excluded_middle_informative.
    - destruct constructive_indefinite_description.
      rewrite <-(add_0_r a) in e at 2.
      apply naturals.cancellation_add in e.
      subst.
      now rewrite iterated_op_0.
    - contradiction n.
      exists 0%N.
      now rewrite add_0_r.
  Qed.

  Theorem iterate_succ : ∀ op f start a b,
      a ≤ b → iterate_with_bounds op f start a (S b)
              = op (iterate_with_bounds op f start a b) (f (S b)).
  Proof.
    intros op f start a b H.
    unfold iterate_with_bounds.
    destruct excluded_middle_informative.
    - destruct constructive_indefinite_description.
      destruct excluded_middle_informative; try tauto.
      destruct constructive_indefinite_description.
      replace x with (S x0).
      + now rewrite iterated_op_succ, e0, add_1_r.
      + apply (naturals.cancellation_add a).
        now rewrite add_succ_r, e0, e.
    - contradict n.
      destruct H as [c H].
      exists (S c).
      now rewrite add_succ_r, H.
  Qed.

  Theorem iterate_extensionality : ∀ op f g start a b,
      (∀ k, a ≤ k ≤ b → f k = g k) →
      iterate_with_bounds op f start a b =
      iterate_with_bounds op g start a b.
  Proof.
    intros op f g start a b H.
    destruct (classic (a ≤ b)) as [[c H0] | H0].
    2: { unfold iterate_with_bounds.
         destruct excluded_middle_informative; tauto. }
    subst.
    induction c using Induction.
    - rewrite add_0_r, ? iterate_0.
      apply H.
      rewrite add_0_r.
      split; auto using le_refl.
    - rewrite add_succ_r, ? iterate_succ; try now (exists c).
      rewrite IHc, H; auto.
      + split.
        * exists (S c).
          now rewrite add_succ_r.
        * exists 0%N.
          now rewrite add_0_r, add_succ_r.
      + intros k [H0 [d H1]].
        rewrite H; auto.
        split; auto.
        exists (S d).
        rewrite ? add_succ_r.
        now f_equal.
  Qed.

  Theorem iterate_lower : ∀ op f start a c,
      (∀ x y z, op x (op y z) = op (op x y) z) →
      iterate_with_bounds op f start a (S a+c) =
      op (f a) (iterate_with_bounds op f start (S a) (S a+c)).
  Proof.
    intros op f start a c H.
    induction c using Induction.
    - rewrite ? add_0_r, iterate_succ, ? iterate_0; auto using le_refl.
    - rewrite ? add_succ_r, ? iterate_succ, IHc, H; auto.
      + now (exists c).
      + exists (c+1)%N.
        now rewrite add_assoc, (add_comm a), add_1_r, <-add_succ_r, add_comm.
  Qed.

  Theorem iterate_shift : ∀ op f start a c,
      iterate_with_bounds op f start a (a+c) =
      iterate_with_bounds op (λ n, (f (n+a)%N)) start 0 c.
  Proof.
    intros op f start a c.
    induction c using Induction.
    - now rewrite add_0_r, ? iterate_0, add_0_l.
    - rewrite add_succ_r, ? iterate_succ, IHc, <-add_succ_r; auto using zero_le.
      + do 2 f_equal.
        now rewrite add_comm.
      + now (exists c).
  Qed.

  Theorem iterate_1 : ∀ op f start,
      iterate_with_bounds op f start 0 1 = op (f 0%N) (f 1%N).
  Proof.
    intros op f start.
    unfold naturals.one.
    rewrite iterate_succ, iterate_0; auto using zero_le.
  Qed.

  Theorem iterate_2 : ∀ op f start,
      iterate_with_bounds op f start 0 2 = op (op (f 0%N) (f 1%N)) (f 2).
  Proof.
    intros op f start.
    rewrite iterate_succ, iterate_1; auto using zero_le.
  Qed.

  Theorem iterate_succ_lower_limit : ∀ op f start a b,
      a ≤ S b → op start (f (S b)) = f (S b) →
      iterate_with_bounds op f start a (S b) =
      op (iterate_with_bounds op f start a b) (f (S b)).
  Proof.
    intros op f start a b H H0.
    destruct (classic (a ≤ b)) as [H1 | H1]; auto using iterate_succ.
    assert (a = S b).
    { destruct H as [c H].
      apply NNPP.
      contradict H1.
      assert (c ≠ 0%N).
      { contradict H0.
        subst.
        now rewrite add_0_r in H. }
      apply succ_0 in H2 as [d H2].
      subst.
      rewrite add_succ_r in H.
      apply PA5 in H.
      now exists d. }
    subst.
    rewrite iterate_0.
    unfold iterate_with_bounds.
    destruct excluded_middle_informative; auto.
    exfalso.
    rewrite le_not_gt in l.
    contradict l.
    apply succ_lt.
  Qed.

End Iterated_op_theorems.
