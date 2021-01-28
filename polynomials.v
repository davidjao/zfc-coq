Require Export power_series.
Set Warnings "-notation-overridden,-uniform-inheritance".

Section Polynomial_construction.

  Variable R : ring.

  Delimit Scope R_scope with R.
  Bind Scope R_scope with R.
  Delimit Scope Series_scope with series.
  Bind Scope Series_scope with power_series.
  Open Scope R_scope.
  Notation Rset := (set_R R).
  Notation Rring := (rings.R R).
  Infix "+" := (add R) : R_scope.
  Infix "*" := (mul R) : R_scope.
  Notation "0" := (rings.zero R) : R_scope.
  Notation "1" := (rings.one R) : R_scope.
  Notation "0" := (zero R) : Series_scope.
  Notation "1" := (one R) : Series_scope.
  Notation "- a" := (neg R a) : R_scope.

  Add Ring generic_ring :
    (mk_rt 0 1 (rings.add R) (rings.mul R) (sub R) (rings.neg R) eq (A3 R)
           (A1 R) (A2 R) (M3 R) (M1 R) (M2 R) (D1 R) (sub_is_neg R) (A4 R)).

  Definition polynomial_set :=
    {f in power_series_set R |
      ∃ f' : power_series R,
       f = f' ∧ ∃ n : N, ∀ m, n ≤ m → coefficient _ f' m = 0}.

  Theorem polynomials_are_subset : polynomial_set ⊂ set_R (power_series_ring R).
  Proof.
    intros f H.
    apply Specify_classification in H as [H H0].
    exact H.
  Qed.

  Theorem polynomials_are_subring :
    is_subring (power_series_ring R) polynomial_set.
  Proof.
    repeat split.
    - intros [a A] [b B] H H0.
      apply Specify_classification in H as [H [[a' A'] [H1 [n H2]]]].
      apply Specify_classification in H0 as [H0 [[b' B'] [H3 [m H4]]]].
      unfold rings.IRS, ISS in *.
      simpl in *.
      subst.
      replace A with A' by now apply proof_irrelevance.
      replace B with B' by now apply proof_irrelevance.
      set (a := (exist (λ x : set, x ∈ power_series_set R) a' A')).
      set (b := (exist (λ x : set, x ∈ power_series_set R) b' B')).
      fold a b in H2, H4 |-*.
      apply Specify_classification.
      split; try now apply (proj2_sig (a + b)).
      exists (a + b).
      split; auto.
      exists (max m n).
      intros x H1.
      unfold add.
      rewrite coefficient_seriesify, H2, H4, A3; auto.
      + eapply le_trans; eauto using max_le_l.
      + eapply le_trans; eauto using max_le_r.
    - intros [a A] [b B] H H0.
      apply Specify_classification in H as [H [[a' A'] [H1 [n H2]]]].
      apply Specify_classification in H0 as [H0 [[b' B'] [H3 [m H4]]]].
      unfold rings.IRS, ISS in *.
      simpl in *.
      subst.
      replace A with A' by now apply proof_irrelevance.
      replace B with B' by now apply proof_irrelevance.
      set (a := (exist (λ x : set, x ∈ power_series_set R) a' A')).
      set (b := (exist (λ x : set, x ∈ power_series_set R) b' B')).
      fold a b in H2, H4 |-*.
      apply Specify_classification.
      split; try now apply (proj2_sig (a * b)).
      exists (a * b).
      split; auto.
      exists (n + m)%N.
      intros x H1.
      unfold mul.
      rewrite coefficient_seriesify.
      replace 0 with (sum R (λ k : N, 0) 0 x).
      + apply iterate_extensionality.
        intros k H3.
        destruct (classic (n ≤ k)).
        * now rewrite H2, mul_0_l.
        * rewrite H4, mul_0_r; auto.
          apply NNPP.
          intros H6.
          rewrite <-lt_not_ge in H5, H6.
          assert (k + (x - k) < n + m) as H7 by now apply lt_cross_add.
          rewrite sub_abab, lt_not_ge in H7; intuition.
      + clear.
        induction x using Induction.
        * unfold sum.
          now rewrite iterate_0.
        * rewrite sum_succ, IHx, A3; auto using zero_le.
    - intros [a A] H.
      apply Specify_classification in H as [H [[a' A'] [H0 [n H1]]]].
      unfold rings.IRS, ISS in *.
      simpl in *.
      subst.
      replace A with A' by now apply proof_irrelevance.
      set (a := (exist (λ x : set, x ∈ power_series_set R) a' A')).
      fold a in H1 |-*.
      apply Specify_classification.
      split; try now apply (proj2_sig (-a)).
      exists (-a).
      split; auto.
      exists n.
      intros x H0.
      unfold neg.
      rewrite coefficient_seriesify.
      rewrite H1; auto.
      ring.
    - apply Specify_classification.
      split; try now apply (proj2_sig 1%series).
      exists (1%series).
      split; auto.
      exists 1%N.
      intros m H.
      unfold one, IRS.
      rewrite coefficient_seriesify.
      destruct excluded_middle_informative; subst; auto.
      apply le_not_gt in H.
      contradict H.
      apply succ_lt.
  Qed.

  Definition polynomial_ring :=
    subring _ polynomial_set polynomials_are_subset polynomials_are_subring.

  Definition poly := (rings.R polynomial_ring).

  Delimit Scope Poly_scope with poly.
  Bind Scope Poly_scope with poly.
  Open Scope Poly_scope.

  Infix "+" := (rings.add polynomial_ring) : Poly_scope.
  Infix "*" := (rings.mul polynomial_ring) : Poly_scope.
  Notation "0" := (rings.zero polynomial_ring) : Poly_scope.
  Notation "1" := (rings.one polynomial_ring) : Poly_scope.
  Notation "- f" := (rings.neg polynomial_ring f) : Poly_scope.

  Add Ring generic_polynomial_ring :
    (mk_rt 0 1 (rings.add polynomial_ring) (rings.mul polynomial_ring)
           (rings.sub polynomial_ring) (rings.neg polynomial_ring) eq
           (rings.A3 polynomial_ring) (rings.A1 polynomial_ring)
           (rings.A2 polynomial_ring) (rings.M3 polynomial_ring)
           (rings.M1 polynomial_ring) (rings.M2 polynomial_ring)
           (rings.D1 polynomial_ring) (rings.sub_is_neg polynomial_ring)
           (rings.A4 polynomial_ring)).

End Polynomial_construction.
