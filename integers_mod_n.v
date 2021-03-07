Set Warnings "-ambiguous-paths".
Require Export polynomials Setoid.

Open Scope Z_scope.

Definition eqm n a b := n｜b - a.

Notation "a ≡ b (mod  n )" := (eqm n a b) (at level 70) : Z_scope.

Theorem eqm_refl : ∀ n a : Z, a ≡ a (mod n).
Proof.
  intros n a.
  unfold eqm.
  replace (a - a) with 0 by ring.
  now apply div_0_r.
Qed.

Theorem eq_eqm : ∀ a b n, a = b → a ≡ b (mod n).
Proof.
  intros a b n H.
  rewrite H.
  apply eqm_refl.
Qed.

Theorem eqm_sym : ∀ n a b : Z, a ≡ b (mod n) → b ≡ a (mod n).
Proof.
  intros n a b H.
  unfold eqm in *.
  replace (a-b) with ((-(1))*(b-a)) by ring.
  now apply div_mul_l.
Qed.

Theorem eqm_gcd : ∀ n a b, a ≡ b (mod n) → gcd (a, n) = 1 → gcd (b, n) = 1.
Proof.
  intros n a b H H0.
  repeat split; try apply div_1_l.
  intros x H1 H2.
  apply H0; auto.
  destruct H as [k H]; simpl in *.
  replace a with (b + (-k)*n).
  - apply div_add, div_mul_l; auto.
  - replace ((-k)*n) with (-(k*n)) by ring.
    rewrite <-H.
    ring.
Qed.

Theorem n_mod_n_is_0 : ∀ n, n ≡ 0 (mod n).
Proof.
  intros n.
  apply div_add.
  - apply div_0_r.
  - apply div_sign_r_neg, div_refl.
Qed.

Theorem eqm_trans : ∀ n a b c : Z,
    a ≡ b (mod n) → b ≡ c (mod n) → a ≡ c (mod n).
Proof.
  intros n a b c H H0.
  unfold eqm in *.
  replace (c-a) with ((c-b)+(b-a)) by ring.
  now apply div_add.
Qed.

Theorem eqn_zero : ∀ n, n ≡ 0 (mod n).
Proof.
  intros n.
  apply eqm_sym.
  exists 1.
  simpl.
  now ring_simplify.
Qed.

Theorem eqm_div_n : ∀ n a, n｜a ↔ a ≡ 0 (mod n).
Proof.
  intros n a.
  split; intros H.
  - apply eqm_sym.
    unfold eqm.
    now ring_simplify.
  - apply eqm_sym in H.
    unfold eqm in *.
    now ring_simplify in H.
Qed.

Section Modular_arithmetic.

  Variable n : Z.

  Add Parametric Relation : Z (eqm n)
      reflexivity proved by (eqm_refl n)
      symmetry proved by (eqm_sym n)
      transitivity proved by (eqm_trans n) as Z_mod_n.

  Theorem eqm_sym_iff : ∀ a b : Z, a ≡ b (mod n) ↔ b ≡ a (mod n).
  Proof.
    split; intros H; now rewrite H.
  Qed.

  Add Morphism integers.add
      with signature (eqm n) ==> (eqm n) ==> (eqm n) as Z_add_mod.
  Proof.
    intros x y H x0 y0 H0.
    unfold eqm in *.
    replace (y+y0-(x+x0)) with ((y-x)+(y0-x0)) by ring.
    now apply div_add.
  Qed.

  Add Morphism integers.mul
      with signature (eqm n) ==> (eqm n) ==> (eqm n) as Z_mul_mod.
  Proof.
    intros x y H x0 y0 H0.
    apply (eqm_trans n _ (y*x0)); unfold eqm in *.
    - replace (y*x0-x*x0) with ((y-x)*x0) by ring.
      now apply div_mul_r.
    - replace (y*y0-y*x0) with (y*(y0-x0)) by ring.
      now apply div_mul_l.
  Qed.

  Add Morphism integers.neg
      with signature (eqm n) ==> (eqm n) as Z_neg_mod.
  Proof.
    intros x y H.
    unfold eqm in *.
    replace (-y--x) with ((-(1))*(y-x)) by ring.
    now apply div_mul_l.
  Qed.

  Add Morphism integers.sub
      with signature (eqm n) ==> (eqm n) ==> (eqm n) as Z_sub_mod.
  Proof.
    intros x y H x0 y0 H0.
    unfold integers.sub.
    now rewrite H, H0.
  Qed.

  Add Morphism (rings.pow ℤ)
      with signature (eqm n) ==> (eq) ==> (eqm n) as Z_pow_mod.
  Proof.
    intros x y H k.
    induction k using Induction;
      now rewrite ? rings.pow_0_r, ? rings.pow_succ_r, ? IHk, ? H.
  Qed.

  Definition modulo : Z → Z.
  Proof.
    intros x.
    destruct (excluded_middle_informative (0 < n)).
    - pose proof division_algorithm x n l as H.
      destruct (constructive_indefinite_description _ H) as [q H0].
      destruct (constructive_indefinite_description _ H0) as [r H1].
      exact r.
    - exact 0.
  Defined.

  Theorem reduce_mod_eqm : ∀ a, 0 < n → a ≡ modulo a (mod n).
  Proof.
    intros a H.
    unfold modulo.
    destruct excluded_middle_informative; try tauto.
    destruct constructive_indefinite_description as [q];
      destruct constructive_indefinite_description as [r [H0 H1]].
    rewrite <-H0.
    rewrite n_mod_n_is_0 at 2.
    now ring_simplify.
  Qed.

  Definition relation_mod :=
    {z in Zset × Zset | ∃ a b : Z, (a,b) = z ∧ a ≡ b (mod n)}.

  Theorem equivalence_mod : is_equivalence Zset relation_mod.
  Proof.
    repeat split.
    - intros a H.
      rewrite <-(setify_action _ _ H).
      apply Specify_classification; split.
      + apply Product_classification; eauto.
      + eauto using eqm_refl.
    - intros a b H H0 H1.
      apply Specify_classification; split.
      + apply Product_classification; eauto.
      + apply Specify_classification in H1 as [H1 [a' [b' [H2 H3]]]].
        apply Ordered_pair_iff in H2 as [H2 H4].
        subst.
        eauto using eqm_sym.
    - intros a b c H H0 H1 H2 H3.
      apply Specify_classification; split.
      + apply Product_classification; eauto.
      + apply Specify_classification in H2
          as [H2 [a' [b' [H4 H5]]]], H3 as [H3 [b'' [c' [H6 H7]]]].
        apply Ordered_pair_iff in H4 as [H4 H8], H6 as [H6 H9].
        subst.
        apply set_proj_injective in H6; subst.
        eauto using eqm_trans.
  Qed.

  Declare Scope Zn_scope.
  Delimit Scope Zn_scope with Zn.
  Open Scope Zn_scope.

  Definition Z_mod := Zset / relation_mod.

  Definition Z_ := elts (Z_mod).

  Bind Scope Zn_scope with Z_.

  Definition IZnS := (elt_to_set Z_mod) : Z_ → set.
  Coercion IZnS : Z_ >-> set.

  Definition Z_to_Z_n : Z → Z_.
  Proof.
    intros x.
    assert (x ∈ Zset) as H by apply elts_in_set.
    exact (quotient_map _ _ (exist _ _ H)).
  Defined.

  Coercion Z_to_Z_n : Z >-> Z_.

  Definition Z_n_to_Z : Z_ → Z.
  Proof.
    intros x.
    destruct (constructive_indefinite_description _ (quotient_lift _ _ x))
      as [z].
    exact z.
  Defined.

  Coercion Z_n_to_Z : Z_ >-> Z.

  Definition add : Z_ → Z_ → Z_.
  Proof.
    intros a b.
    exact (a + b).
  Defined.

  Definition mul : Z_ → Z_ → Z_.
  Proof.
    intros a b.
    exact (a * b).
  Defined.

  Definition neg : Z_ → Z_.
  Proof.
    intros a.
    exact (-a).
  Defined.

  Definition sub : Z_ → Z_ → Z_.
  Proof.
    intros a b.
    exact (a - b).
  Defined.

  Infix "+" := add : Zn_scope.
  Infix "*" := mul : Zn_scope.
  Infix "-" := sub : Zn_scope.
  Notation "- a" := (neg a) : Zn_scope.

  Theorem IZn_eq : ∀ a b : Z, (a : Z_) = (b : Z_) ↔ a ≡ b (mod n).
  Proof.
    intros a b.
    split; intros H; unfold Z_to_Z_n in *.
    - apply quotient_equiv in H; auto using equivalence_mod.
      apply Specify_classification in H as [H [a' [b' [H0 H1]]]].
      apply Ordered_pair_iff in H0 as [H0 H2].
      simpl in *.
      apply set_proj_injective in H0, H2.
      now subst.
    - apply quotient_equiv, Specify_classification; auto using equivalence_mod.
      split.
      + apply Product_classification; eauto using elts_in_set.
      + now exists a, b.
  Qed.

  Theorem Zproj_eq : ∀ a : Z_, a = ((a : Z) : Z_).
  Proof.
    intros a.
    unfold Z_n_to_Z, Z_to_Z_n.
    destruct constructive_indefinite_description.
    rewrite <-e.
    now apply f_equal, set_proj_injective.
  Qed.

  Theorem Zlift_equiv : ∀ a : Z, a ≡ (a : Z_) : Z (mod n).
  Proof.
    intros a.
    now rewrite <-IZn_eq, <-Zproj_eq.
  Qed.

  Theorem modulus_zero : (n : Z_) = 0.
  Proof.
    apply IZn_eq, eqn_zero.
  Qed.

  Theorem A1 : ∀ a b : Z_, a + b = b + a.
  Proof.
    intros a b.
    unfold add.
    now rewrite integers.A1.
  Qed.

  Theorem A2 : ∀ a b c : Z_, a + (b + c) = (a + b) + c.
  Proof.
    intros a b c.
    unfold add.
    now rewrite IZn_eq, <-? Zlift_equiv, integers.A2.
  Qed.

  Theorem A3 : ∀ a : Z_, 0 + a = a.
  Proof.
    intros a.
    unfold add.
    now rewrite Zproj_eq, IZn_eq, <-Zlift_equiv, integers.A3.
  Qed.

  Theorem A4 : ∀ a : Z_, a + -a = 0.
  Proof.
    intros a.
    unfold add, neg.
    now rewrite IZn_eq, <-Zlift_equiv, integers.A4.
  Qed.

  Theorem sub_is_neg : ∀ a b : Z_, a - b = a + -b.
  Proof.
    intros a b.
    apply IZn_eq.
    unfold neg.
    now rewrite <-Zlift_equiv.
  Qed.

  Theorem M1 : ∀ a b : Z_, a * b = b * a.
  Proof.
    intros a b.
    unfold mul.
    now rewrite integers.M1.
  Qed.

  Theorem M2 : ∀ a b c : Z_, a * (b * c) = (a * b) * c.
  Proof.
    intros a b c.
    unfold mul.
    apply IZn_eq.
    now rewrite <-? Zlift_equiv, integers.M2.
  Qed.

  Theorem M3 : ∀ a : Z_, 1 * a = a.
  Proof.
    intros a.
    unfold mul.
    now rewrite Zproj_eq, IZn_eq, <-Zlift_equiv, integers.M3.
  Qed.

  Theorem D1 : ∀ a b c, (a + b) * c = a * c + b * c.
  Proof.
    intros a b c.
    unfold add, mul.
    apply IZn_eq.
    now rewrite <-? Zlift_equiv, integers.D1.
  Qed.

  Definition ℤ_ :=
    mkRing Z_mod (0 : Z_) (1 : Z_) add mul neg A3 A1 A2 M3 M1 M2 D1 A4.

  Add Ring Z_ring_raw : (ringify ℤ_).
  Add Ring Z_ring : (ringify ℤ_ : ring_theory (0 : Z_) _ _ _ _ _ eq).

  Infix "^" := (rings.pow ℤ_) : Zn_scope.

  Theorem units_in_ℤ_ : ∀ a : Z_, rings.unit ℤ_ a ↔ gcd (a, n) = 1.
  Proof.
    split; intros H.
    - destruct H as [x H].
      apply IZn_eq in H.
      destruct H as [y H].
      simpl in *.
      fold Z Z_ in x, y.
      assert (1 = a * x + n * (-y))%Z as H0.
      { replace (n*(-y))%Z with (-(y*n))%Z by ring.
        rewrite <-H.
        ring. }
      repeat split; try apply div_1_l.
      intros z H1 H2.
      rewrite H0.
      now apply div_mul_add.
    - apply Euclidean_algorithm in H as [x [y H]].
      exists (x : Z_); simpl.
      apply IZn_eq.
      rewrite H, <-Zlift_equiv.
      unfold eqm.
      ring_simplify.
      apply div_mul_r, (div_sign_r ℤ n n), div_refl.
  Qed.

  Lemma injective_mod_n_on_interval_left :
    ∀ a b, 0 ≤ a < n → 0 ≤ b < n → a ≤ b → a ≡ b (mod n) → a = b.
  Proof.
    intros a b H H0 H1 H2.
    unfold eqm, integers.sub in H2.
    destruct H1 as [H1 | H1]; auto; simpl in *.
    apply (ordered_rings.lt_shift ℤ_order) in H1; simpl in *.
    apply div_le in H2; auto.
    contradiction (ordered_rings.lt_irrefl ℤ_order b); simpl.
    destruct H as [H _], H0 as [_ H0].
    apply le_def in H as [c H].
    eapply (ordered_rings.lt_le_trans ℤ_order); eauto; fold integers.le.
    eapply ordered_rings.le_trans; fold integers.le; eauto.
    rewrite le_def.
    exists c.
    ring [H].
  Qed.

  Theorem injective_mod_n_on_interval :
    ∀ a b, 0 ≤ a < n → 0 ≤ b < n → a ≡ b (mod n) → a = b.
  Proof.
    intros a b H H0 H1.
    destruct (classic (a ≤ b)); auto using injective_mod_n_on_interval_left.
    symmetry in H1 |-*.
    apply injective_mod_n_on_interval_left; auto.
    now apply or_introl, lt_not_ge.
  Qed.

  Theorem IZn_neg : ∀ a : Z, (-a : Z_) = (-a)%Z.
  Proof.
    intros a.
    apply IZn_eq.
    now rewrite <-Zlift_equiv.
  Qed.

  Theorem IZn_mul : ∀ a b : Z, (a * b : Z_) = (a * b)%Z.
  Proof.
    intros a b.
    apply IZn_eq.
    now rewrite <-? Zlift_equiv.
  Qed.

  Theorem IZn_add : ∀ a b : Z, (a + b : Z_) = (a + b)%Z.
  Proof.
    intros a b.
    apply IZn_eq.
    now rewrite <-? Zlift_equiv.
  Qed.

  Theorem IZn_pow : ∀ (a : Z) k, ((a : Z_)^k) = ((a^k : Z)%Z : Z_).
  Proof.
    intros a k.
    induction k using Induction.
    - now rewrite ? rings.pow_0_r.
    - now rewrite ? rings.pow_succ_r, IHk, IZn_mul.
  Qed.

  Section Positive_modulus.

    Hypothesis modulus_pos : 0 < n.

    Theorem surjective_mod_n_on_interval :
      ∀ a : Z_, exists ! x : Z, 0 ≤ x < n ∧ a = x.
    Proof.
      intros a.
      exists ( modulo a).
      unfold modulo.
      destruct excluded_middle_informative; try tauto.
      destruct constructive_indefinite_description as [q].
      destruct constructive_indefinite_description as [r].
      destruct a0 as [H H0].
      split.
      - split; auto.
        symmetry.
        rewrite Zproj_eq, <-H.
        apply IZn_eq.
        rewrite (eqn_zero n) at 2.
        now ring_simplify.
      - intros y [H1 H2].
        apply injective_mod_n_on_interval, IZn_eq; auto.
        rewrite <-H2, Zproj_eq.
        apply IZn_eq.
        rewrite <-H.
        rewrite (eqn_zero n) at 2.
        now ring_simplify.
    Qed.

    Definition modulus_in_N : N.
    Proof.
      apply lt_def in modulus_pos.
      destruct (constructive_indefinite_description _ modulus_pos) as [k], a.
      exact k.
    Defined.

    Theorem modulus_in_Z : n = modulus_in_N.
    Proof.
      unfold modulus_in_N.
      destruct constructive_indefinite_description, a.
      subst.
      ring.
    Qed.

    Definition map_to_N : elts modulus_in_N → N.
    Proof.
      intros x.
      pose proof (elts_in_set _ x) as H.
      apply elements_of_naturals_are_naturals in H; auto using N_in_ω.
      exact (exist _ _ H).
    Defined.

    Theorem map_to_lt_n : ∀ x, map_to_N x < n.
    Proof.
      intros x.
      rewrite modulus_in_Z.
      apply INZ_lt, lt_is_in.
      simpl.
      auto using elts_in_set.
    Qed.

    Theorem map_to_ge_0 : ∀ x, 0 ≤ map_to_N x.
    Proof.
      intros x.
      apply INZ_le, zero_le.
    Qed.

    Definition map_to_mod_n : elts modulus_in_N → Z_.
    Proof.
      intros x.
      exact (map_to_N x).
    Defined.

    Theorem bijective_map_to_mod_n :
      bijective (sets.functionify _ _ map_to_mod_n).
    Proof.
      split; rewrite ? Injective_classification, ? Surjective_classification,
             ? sets.functionify_domain, ? sets.functionify_range.
      - intros x y H H0 H1.
        rewrite <-(setify_action _ _ H), <-(setify_action _ _ H0),
        ? functionify_action in *.
        apply set_proj_injective, IZn_eq, injective_mod_n_on_interval,
        INZ_eq in H1; auto using map_to_ge_0, map_to_lt_n.
        inversion H1.
        subst.
        now replace H with H0 in H1 by now apply proof_irrelevance.
      - intros y H.
        rewrite <-(setify_action _ _ H) in *.
        destruct (surjective_mod_n_on_interval (exist _ _ H))
          as [x [[[H0 H1] H2] H3]].
        apply le_def in H0 as [ξ H4].
        ring_simplify in H4.
        exists ξ.
        assert (ξ ∈ modulus_in_N) as H5.
        { now rewrite <-lt_is_in, <-INZ_lt, <-modulus_in_Z, <-H4. }
        split; auto.
        rewrite <-(setify_action _ _ H5), functionify_action, H2, H4.
        now apply f_equal, set_proj_injective, f_equal,
        IZn_eq, eq_eqm, f_equal, set_proj_injective.
    Qed.

    Theorem bijection_of_Z_mod : (Z_mod ~ modulus_in_N)%set.
    Proof.
      symmetry.
      exists (sets.functionify _ _ map_to_mod_n).
      rewrite sets.functionify_domain, sets.functionify_range.
      auto using bijective_map_to_mod_n.
    Qed.
 
    Theorem finite_Z_mod : finite Z_mod.
    Proof.
      exists modulus_in_N.
      auto using bijection_of_Z_mod.
    Qed.

    Theorem Z_mod_card : # Z_mod = modulus_in_N.
    Proof.
      auto using equivalence_to_card, bijection_of_Z_mod.
    Qed.

    Definition Euler_Phi_set := {x of type Z_mod | gcd (x : Z_, n) = 1}.

    Definition Euler_Phi := # Euler_Phi_set.

    Definition unit_set_mod := {x of type Z_mod | rings.unit ℤ_ x}.

    Theorem Euler_Phi_unit : Euler_Phi_set = unit_set_mod.
    Proof.
      apply Extensionality.
      split; intros H; apply Specify_classification in H as [H H0];
        apply Specify_classification;
        rewrite <-(setify_action _ _ H), <-specify_action in *; split;
          eauto using elts_in_set; eapply units_in_ℤ_; eauto using eqm_gcd.
    Qed.

    Theorem Euler_Phi_finite : finite Euler_Phi_set.
    Proof.
      eapply subsets_of_finites_are_finite; eauto using finite_Z_mod.
      intros x H.
      now apply Specify_classification in H.
    Qed.

    Theorem Euler_Phi_nonzero : Euler_Phi ≠ 0%N.
    Proof.
      unfold Euler_Phi.
      intros H.
      apply finite_empty in H; auto using Euler_Phi_finite.
      contradict H.
      apply Nonempty_classification.
      exists (1 : Z_).
      rewrite Euler_Phi_unit.
      apply Specify_classification.
      rewrite <-specify_action.
      auto using (elts_in_set Z_mod), (one_unit ℤ_).
    Qed.

    Corollary Euler_Phi_ge_1 : (1 ≤ Euler_Phi)%N.
    Proof.
      apply naturals.le_not_gt.
      intros H.
      apply le_lt_succ in H.
      auto using Euler_Phi_nonzero, naturals.le_antisymm, zero_le.
    Qed.

    Theorem Euler_Phi_helper : ∀ f,
        range f = Euler_Phi_set → ∀ x, x ∈ domain f → f x ∈ Z_mod.
    Proof.
      intros f H x H0.
      assert (Euler_Phi_set ⊂ Z_mod) as H1.
      { intros z H1.
        now apply Specify_classification in H1. }
      apply H1.
      rewrite <-H.
      now apply function_maps_domain_to_range.
    Qed.

    Definition Euler_Phi_list : N → Z_.
    Proof.
      intros x.
      pose proof Euler_Phi_finite.
      destruct (constructive_indefinite_description _ H)
        as [m H0], (excluded_middle_informative (x < m)%N).
      - symmetry in H0.
        destruct (constructive_indefinite_description _ H0) as [f [H1 [H2 H3]]].
        rewrite lt_is_in, <-H1 in l.
        apply Euler_Phi_helper in l; auto.
        exact (exist _ _ l).
      - exact 0.
    Defined.

    Lemma Euler_Phi_set_classification :
      ∀ a : Z_, a ∈ Euler_Phi_set ↔ gcd(a, n) = 1.
    Proof.
      split; intros H.
      - apply Specify_classification in H as [H H0].
        rewrite <-(setify_action _ _ H), <-specify_action in *.
        eapply eqm_gcd; eauto.
        apply IZn_eq.
        rewrite <-? Zproj_eq.
        now apply set_proj_injective.
      - apply Specify_classification.
        rewrite <-specify_action.
        auto using (elts_in_set Z_mod).
    Qed.

    Lemma Euler_Phi_list_unit :
      ∀ i, (0 ≤ i ≤ Euler_Phi - 1)%N → rings.unit ℤ_ (Euler_Phi_list i).
    Proof.
      intros i H.
      unfold Euler_Phi_list.
      destruct constructive_indefinite_description, excluded_middle_informative.
      - destruct constructive_indefinite_description as [f], a as [e0 [e1 b]].
        rewrite units_in_ℤ_, <-Euler_Phi_set_classification.
        simpl.
        rewrite <-e1.
        apply function_maps_domain_to_range.
        now rewrite e0, <-lt_is_in.
      - contradict n0.
        destruct H as [H H0].
        apply le_lt_succ in H0.
        rewrite <-add_1_r, add_comm, sub_abab in H0; auto using Euler_Phi_ge_1.
        replace x with Euler_Phi; eauto using equivalence_to_card.
    Qed.

    Lemma Euler_Phi_list_surj :
      ∀ a : Z_, rings.unit ℤ_ a → ∃ i,
          (0 ≤ i ≤ Euler_Phi - 1)%N ∧ a = Euler_Phi_list i.
    Proof.
      intros a H.
      unfold Euler_Phi_list.
      destruct constructive_indefinite_description.
      rewrite units_in_ℤ_ in H.
      assert (a ∈ Euler_Phi_set).
      { apply Specify_classification.
        rewrite <-specify_action.
        auto using (elts_in_set Z_mod). }
      destruct constructive_indefinite_description as [f].
      repeat destruct a0.
      assert ((inverse f) a ∈ x) as H1.
      { rewrite <-e0, <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite inverse_domain, e1; auto. }
      assert ((inverse f) a ∈ ω) as H2 by
            (eapply elements_of_naturals_are_naturals; eauto using N_in_ω).
      set (ι := exist _ _ H2 : N).
      exists ι.
      assert (ι < x)%N as H3 by now apply lt_is_in.
      destruct excluded_middle_informative; try tauto.
      repeat split; auto using zero_le.
      - apply le_lt_succ.
        rewrite <-add_1_r, add_comm, sub_abab; auto using Euler_Phi_ge_1.
        replace Euler_Phi with x; eauto using eq_sym, equivalence_to_card.
      - apply set_proj_injective.
        simpl.
        rewrite right_inverse; rewrite ? inverse_domain, ? e1; auto.
    Qed.

    Lemma Euler_Phi_list_inj :
      ∀ i j : N, (0 ≤ i ≤ Euler_Phi - 1)%N → (0 ≤ j ≤ Euler_Phi - 1)%N →
                 Euler_Phi_list i = Euler_Phi_list j → i = j.
    Proof.
      intros i j H H0 H1.
      unfold Euler_Phi_list in H1.
      destruct constructive_indefinite_description
        as [m], constructive_indefinite_description as [f].
      repeat destruct a.
      destruct excluded_middle_informative.
      - destruct excluded_middle_informative, b as [H2 H3].
        + inversion H1.
          rewrite Injective_classification in H2.
          apply set_proj_injective, H2; auto; now rewrite e0, <-lt_is_in.
        + contradiction n0.
          replace m with Euler_Phi by eauto using equivalence_to_card.
          destruct H0 as [H0 H4].
          apply le_lt_succ in H4.
          rewrite <-add_1_r, add_comm, sub_abab in *; auto using Euler_Phi_ge_1.
      - contradiction n0.
        replace m with Euler_Phi by eauto using equivalence_to_card.
        destruct H as [H H2].
        apply le_lt_succ in H2.
        rewrite <-add_1_r, add_comm, sub_abab in *; auto using Euler_Phi_ge_1.
    Qed.

    Definition Euler_Phi_product := prod ℤ_ Euler_Phi_list 0 (Euler_Phi - 1).

    Lemma Euler_Phi_product_unit : rings.unit ℤ_ Euler_Phi_product.
    Proof.
      eauto using unit_prod_closure, Euler_Phi_list_unit.
    Qed.

    Section Euler's_Theorem.

      Variable a : Z_.
      Hypothesis unit_a : rings.unit ℤ_ a.

      Definition Euler_Phi_product_shifted :=
        prod ℤ_ (λ x, a * (Euler_Phi_list x)) 0 (Euler_Phi - 1).

      Lemma Euler_Phi_equal : Euler_Phi_product = Euler_Phi_product_shifted.
      Proof.
        unfold Euler_Phi_product, Euler_Phi_product_shifted.
        apply (product_bijection ℤ_).
        - intros j H.
          destruct (Euler_Phi_list_surj (a * Euler_Phi_list j)) as [i [H0 H1]].
          { apply unit_closure; auto using Euler_Phi_list_unit. }
          exists i.
          split; auto.
          intros y [H2 H3].
          apply Euler_Phi_list_inj; auto; congruence.
        - intros i H.
          destruct unit_a as [x H0].
          destruct (Euler_Phi_list_surj (x * Euler_Phi_list i)) as [j [H1 H2]].
          { apply unit_closure; auto using Euler_Phi_list_unit.
            exists a.
            now rewrite H0, M1. }
          exists j.
          simpl in H0.
          split; try split; auto.
          + now rewrite <-H2, M2, (M1 a), <-H0, M3.
          + intros y [H3 H4].
            apply Euler_Phi_list_inj; auto.
            now rewrite <-H2, H4, M2, <-H0, M3.
      Qed.

      Theorem Euler : a^Euler_Phi = (1 : Z_).
      Proof.
        pose proof Euler_Phi_equal as H.
        unfold Euler_Phi_product_shifted in H.
        rewrite <-prod_mul, sub_0_r, <-(M3 Euler_Phi_product),
        ? (M1 _ Euler_Phi_product), <-add_1_r, naturals.add_comm, sub_abab
          in H at 1; auto using zero_le, Euler_Phi_ge_1.
        apply (unit_cancel ℤ_) in H; auto using Euler_Phi_product_unit.
      Qed.

    End Euler's_Theorem.

  End Positive_modulus.

  Definition square (a : Z_) := a * a.

  Definition square_function := sets.functionify _ _ square.

  Definition QR := {x of type Z_mod | rings.unit ℤ_ x ∧ ∃ a, square a = x}.
  Definition QNR := {x of type Z_mod | rings.unit ℤ_ x ∧ (x : Z_) ∉ QR}.

  Definition legendre_symbol (a : Z_) : Z.
  Proof.
    destruct (excluded_middle_informative (a ∈ QR)).
    - exact 1.
    - destruct (excluded_middle_informative (a ∈ QNR)).
      + exact (-(1))%Z.
      + exact 0.
  Defined.

  Section Prime_modulus.

    Notation p := n.
    Hypothesis prime_modulus : prime p.
    Hypothesis positive_prime : 0 < p.
    Notation p_in_N := ( modulus_in_N positive_prime).

    Theorem Z_mod_prime_is_ID : is_integral_domain ℤ_.
    Proof.
      split.
      - intros a b H; simpl in *.
        apply IZn_eq, eqm_div_n, Euclid's_lemma in H as [H | H]; auto;
          [ left | right ]; apply eqm_div_n, IZn_eq in H;
            now rewrite <-H, <-Zproj_eq.
      - intros H; simpl in *.
        apply IZn_eq, eqm_div_n in H.
        now destruct prime_modulus.
    Qed.

    Definition ℤ_ID := integral_domain_from_ring ℤ_ Z_mod_prime_is_ID.

    Lemma nonzero_unit : ∀ a : Z_, a ≠ 0 → rings.unit ℤ_ a.
    Proof.
      intros a H.
      apply units_in_ℤ_, gcd_sym, prime_rel_prime; auto.
      contradict H.
      apply eqm_div_n, IZn_eq in H.
      now rewrite <-Zproj_eq in H.
    Qed.

    Definition inv : Z_ → Z_.
    Proof.
      intros a.
      destruct (excluded_middle_informative (a = 0)).
      - exact 0.
      - apply nonzero_unit in n0.
        destruct (constructive_indefinite_description _ n0) as [x H].
        exact x.
    Defined.

    Theorem inv_l : ∀ a : Z_, a ≠ 0 → inv a * a = 1.
    Proof.
      intros a H.
      unfold inv.
      destruct excluded_middle_informative; try tauto.
      now destruct constructive_indefinite_description.
    Qed.

    Definition 𝔽 := mkField ℤ_ inv inv_l (Logic.proj2 Z_mod_prime_is_ID).

    Theorem QR_QNR_0 : ∀ a : Z_, a ∉ QR → a ∉ QNR → a = 0.
    Proof.
      intros a H H0.
      apply NNPP.
      contradict H0.
      apply nonzero_unit in H0.
      apply Specify_classification.
      rewrite <-specify_action.
      auto using (elts_in_set Z_mod).
    Qed.

    Theorem Euler_Criterion_zero : ∀ a, legendre_symbol a = 0 ↔ a = 0.
    Proof.
      split; unfold legendre_symbol; intros H.
      destruct excluded_middle_informative.
      - contradiction (integers.zero_ne_1).
      - destruct excluded_middle_informative; auto using QR_QNR_0.
        contradiction (integral_domains.minus_one_nonzero integers.ℤ_ID).
      - subst; repeat destruct excluded_middle_informative; auto;
          apply Specify_classification in i as [H0 H1];
          rewrite <-(setify_action _ _ H0), <-specify_action in *;
          replace (exist _ _ H0 : Z_) with (0 : Z_) in *
            by (now apply set_proj_injective);
          destruct H1 as [[x H1] H2], Z_mod_prime_is_ID as [H3 H4];
          contradiction H4;
          now rewrite H1, mul_0_r.
    Qed.

    Theorem Prime_Euler_Phi : (Euler_Phi = p_in_N - 1)%N.
    Proof.
      rewrite <-(singleton_card (0 : Z_)), <-Z_mod_card, <-complement_card;
        auto using singletons_are_finite.
      2: { intros z H.
           apply Singleton_classification in H.
           subst.
           auto using (elts_in_set Z_mod). }
      apply f_equal, Extensionality.
      split; intros H; destruct prime_modulus as [H0 H1].
      - apply Specify_classification in H as [H H2].
        rewrite <-(setify_action _ _ H), <-specify_action,
        Complement_classification, Singleton_classification in *.
        split; auto.
        intros H3.
        apply set_proj_injective in H3.
        destruct H2 as [H2 [H4 H5]].
        contradict H0.
        apply H5; eauto using (divide_refl ℤ) with Z.
        apply eqm_div_n.
        now rewrite H3, <-Zlift_equiv.
      - apply Complement_classification in H as [H H2].
        apply Specify_classification.
        split; auto.
        rewrite <-(setify_action _ _ H), <-specify_action,
        Singleton_classification in *.
        repeat split; try apply div_1_l.
        intros d H3 H4.
        apply H1 in H4 as [H4 | [H4 H5]]; fold integers.divide in *; auto.
        contradict H2.
        apply f_equal.
        rewrite Zproj_eq, IZn_eq, <-eqm_div_n at 1.
        eapply div_trans; eauto.
    Qed.

    Theorem Prime_Euler_Phi_Z : (p - 1 = Euler_Phi)%Z.
    Proof.
      unfold integers.one.
      rewrite ( modulus_in_Z positive_prime), INZ_sub.
      - apply INZ_eq, eq_sym, Prime_Euler_Phi.
      - rewrite <-lt_0_le_1, <-( modulus_in_Z positive_prime); auto.
    Qed.

    Theorem QR_Euler_Phi : QR ⊂ Euler_Phi_set.
    Proof.
      intros x H.
      apply Specify_classification in H as [H H0].
      apply Specify_classification.
      rewrite <-(setify_action _ _ H), <-specify_action in *.
      split; eauto using elts_in_set.
      now apply units_in_ℤ_.
    Qed.

    Theorem QNR_QR_c : QNR = Euler_Phi_set \ QR.
    Proof.
      apply Extensionality.
      split; intros H.
      - apply Specify_classification in H as [H H0].
        rewrite <-(setify_action _ _ H), <-specify_action in *.
        apply Complement_classification.
        split; try tauto.
        apply Specify_classification.
        rewrite <-specify_action.
        split; auto using elts_in_set.
        now apply units_in_ℤ_.
      - apply Complement_classification in H as [H H0].
        apply Specify_classification in H as [H H1].
        apply Specify_classification.
        rewrite <-(setify_action _ _ H), <-specify_action in *.
        repeat split; auto using elts_in_set.
        now apply units_in_ℤ_.
    Qed.

    Definition unit_square_function := restriction square_function unit_set_mod.

    Lemma domain_usf : domain unit_square_function = unit_set_mod.
    Proof.
      unfold unit_square_function, square_function.
      rewrite restriction_domain, sets.functionify_domain.
      apply Intersection_subset.
      intros x H.
      now apply Specify_classification in H.
    Qed.

    Lemma image_usf : image unit_square_function = QR.
    Proof.
      unfold unit_square_function, square_function.
      apply Extensionality.
      split; intros H.
      - apply Specify_classification in H as [H [x [H0 H1]]].
        rewrite restriction_domain, restriction_range, <-restriction_action,
        sets.functionify_domain, sets.functionify_range in *;
          try now rewrite sets.functionify_domain in *.
        apply Pairwise_intersection_classification in H0 as [H0 H2].
        apply Specify_classification.
        rewrite <-(setify_action _ _ H), <-(setify_action _ _ H2),
        functionify_action, <-specify_action in *.
        apply set_proj_injective in H1.
        repeat split; eauto.
        apply Specify_classification in H0 as [H0 H3].
        rewrite <-specify_action, <-H1 in *.
        now apply unit_closure.
      - apply Specify_classification.
        rewrite restriction_domain, restriction_range,
        sets.functionify_domain, sets.functionify_range.
        apply Specify_classification in H as [H H0].
        rewrite <-(setify_action _ _ H), <-specify_action in *.
        destruct H0 as [H0 [a H1]].
        split; eauto using elts_in_set.
        exists a.
        enough (a ∈ unit_set_mod ∩ Z_mod).
        { now rewrite <-restriction_action, functionify_action, H1;
            try now rewrite sets.functionify_domain. }
        rewrite Pairwise_intersection_classification.
        split; eauto using elts_in_set.
        apply Specify_classification.
        split; eauto using elts_in_set.
        rewrite <-specify_action, <-H1 in *.
        unfold square in H0.
        destruct H0 as [x H0].
        exists (x * a).
        now rewrite H0, M2.
    Qed.

    Theorem inverse_image_usf :
      ∀ x, x ∈ QR → inverse_image_of_element square_function x =
                    inverse_image_of_element unit_square_function x.
    Proof.
      intros x H.
      pose proof H as H0.
      rewrite <-image_usf in H0.
      assert (image unit_square_function ⊂ range square_function) as H1.
      { unfold unit_square_function.
        erewrite <-restriction_range; eauto using image_subset_range. }
      apply Extensionality.
      split; intros H2.
      - assert (z ∈ domain square_function) as H3
            by eauto using Inverse_image_classification_domain.
        pose proof H3 as H4.
        unfold square_function in H4.
        rewrite sets.functionify_domain in H4.
        assert (z ∈ unit_set_mod) as H5.
        { apply Specify_classification.
          split; auto.
          apply Specify_classification in H as [H H5].
          rewrite <-(setify_action _ _ H4), <-(setify_action _ _ H),
          <-? specify_action in *.
          destruct H5 as [H5 [a H6]].
          apply Inverse_image_classification in H2; auto.
          unfold square_function in H2.
          rewrite sets.functionify_action in H2.
          apply set_proj_injective in H2.
          rewrite <-H2 in H5.
          unfold square in *.
          destruct H5 as [y H5].
          exists (y * (exist _ _ H4)).
          now rewrite H5, M2. }
        rewrite Inverse_image_classification in *; eauto;
          unfold unit_square_function; rewrite <-? restriction_action; auto;
            now apply Pairwise_intersection_classification.
      - apply Specify_classification in H2 as [H2 H3].
        unfold unit_square_function in *.
        rewrite restriction_domain, <-restriction_action,
        Pairwise_intersection_classification in *; auto.
        now apply Inverse_image_classification; auto.
    Qed.

    Theorem finite_QR : finite QR.
    Proof.
      apply (subsets_of_finites_are_finite _ Z_mod); auto using finite_Z_mod.
      intros x H.
      now apply Specify_classification in H.
    Qed.

    Theorem Fpow_wf : ∀ (a : Z_) k, rings.pow ℤ_ a k = (fields.pow 𝔽 a k).
    Proof.
      intros a k.
      now rewrite <-pow_wf.
    Qed.

  End Prime_modulus.

  Section Odd_prime_modulus.

    Notation p := n.
    Hypothesis prime_modulus : prime p.
    Hypothesis odd_prime : p > 2.

    Theorem odd_prime_positive : 0 < p.
    Proof.
      eapply integers.lt_trans; eauto.
      apply (ordered_rings.zero_lt_2 ℤ_order).
    Qed.

    Theorem one_ne_minus_one : (1 : Z_) ≠ ((-(1))%Z : Z_).
    Proof.
      intros H.
      apply IZn_eq, eqm_sym in H.
      unfold eqm in H.
      replace (1--(1))%Z with (2%Z) in H by ring.
      now apply div_le, le_not_gt in H;
        try apply (ordered_rings.zero_lt_2 ℤ_order).
    Qed.

    Theorem number_of_square_roots : ∀ x : Z_,
        x ∈ QR → (inverse_image_of_element square_function x ~ 2%N)%set.
    Proof.
      intros x H.
      apply Specify_classification in H as [H H0].
      rewrite <-specify_action in H0.
      destruct H0 as [H0 [a H1]].
      replace (inverse_image_of_element square_function x) with {a, -a}.
      { apply pairing_card.
        intros H2.
        destruct (surjective_mod_n_on_interval odd_prime_positive a)
          as [a' [[[H3 H4] H5] H6]].
        subst.
        apply set_proj_injective in H2.
        rewrite Zproj_eq in H2.
        rewrite (Zproj_eq a'), IZn_neg in H2 at 1.
        apply IZn_eq, eqm_sym in H2.
        rewrite <-? Zlift_equiv in H2.
        unfold eqm, integers.sub in H2.
        replace (--a')%Z with (a') in * by now ring_simplify.
        rewrite <-(integers.M3 a'), <-integers.D1 in H2.
        apply Euclid's_lemma in H2 as [H2 | H2]; auto.
        - now apply div_le, le_not_gt in H2; try apply (zero_lt_2 ℤ_order).
        - apply (unit_nonzero (ℤ_ID prime_modulus)) in H0.
          contradict H0; simpl.
          apply IZn_eq.
          rewrite eqm_div_n in H2.
          now rewrite <-Zlift_equiv, H2, (mul_0_r ℤ). }
      apply Extensionality.
      unfold square_function.
      assert ({a,-a} ⊂ Z_mod) as H2.
      { intros z H2.
        apply Pairing_classification in H2 as [H2 | H2];
          subst; eauto using elts_in_set. }
      split; intros H3.
      - rewrite Inverse_image_classification in *;
          rewrite ? sets.functionify_domain, ? sets.functionify_range;
          auto using elts_in_set.
        apply Pairing_classification in H3 as [H3 | H3]; subst.
        + now rewrite functionify_action.
        + rewrite functionify_action.
          unfold square.
          apply f_equal.
          now rewrite (rings.mul_neg_neg ℤ_).
      - apply Inverse_image_subset in H3 as H4;
          rewrite ? sets.functionify_range, ? sets.functionify_domain in *;
          auto using elts_in_set.
        rewrite Inverse_image_classification in *;
          rewrite ? sets.functionify_domain, ? sets.functionify_range;
          auto using elts_in_set.
        set (ζ := exist _ _ H4 : Z_).
        rewrite <-(setify_action _ _ H4), functionify_action in *.
        fold ζ in H3 |-*.
        unfold square in *.
        subst.
        apply set_proj_injective in H3.
        pose proof (difference_of_squares ℤ_ ζ a) as H1; simpl in H1.
        rewrite H3, A4 in H1.
        apply Pairing_classification.
        apply eq_sym, (integral_domains.cancellation (ℤ_ID prime_modulus)) in H1
          as [H1 | H1]; simpl in H1.
        + left; unfold IZnS; f_equal.
          now rewrite <-(A3 a), <-H1, <-A2, (A1 _ a), A4, A1, A3.
        + right.
          now rewrite <-(A3 (-a)), <-H1, <-A2, A4, A1, A3.
    Qed.

    Theorem size_of_QR_in_Z : (p - 1 = 2 * # QR)%Z.
    Proof.
      unfold integers.one at 2 3.
      rewrite (Prime_Euler_Phi_Z prime_modulus odd_prime_positive), INZ_add,
      INZ_mul; auto using odd_prime_positive.
      apply INZ_eq, equivalence_to_card.
      rewrite add_1_r, <-(card_of_natural 2), mul_comm, <-finite_products_card,
      card_equiv, Euler_Phi_unit, <-domain_usf, <-image_usf;
        auto using finite_products_are_finite, naturals_are_finite,
        finite_QR, odd_prime_positive.
      apply orbit_stabilizer_cardinality_image.
      intros y H0.
      rewrite image_usf, <-inverse_image_usf in *; auto.
      pose proof H0 as H1.
      apply Specify_classification in H1 as [H1 _].
      rewrite <-(setify_action _ _ H1).
      auto using number_of_square_roots.
    Qed.

    Theorem size_of_QR : Euler_Phi = (2 * # QR)%N.
    Proof.
      apply INZ_eq.
      rewrite <-INZ_mul, <-add_1_r, <-INZ_add, <-Prime_Euler_Phi_Z;
        auto using odd_prime_positive, size_of_QR_in_Z.
    Qed.

    Theorem size_QR_ge_1 : (1 ≤ # QR)%N.
    Proof.
      destruct (classic (# QR = 0%N)) as [H | H].
      - pose proof size_of_QR.
        rewrite H in H0.
        contradiction Euler_Phi_nonzero; auto using odd_prime_positive.
        now rewrite H0, naturals.mul_0_r.
      - apply succ_0 in H as [m H].
        rewrite H.
        auto using one_le_succ.
    Qed.

    Theorem size_QR_QNR : # QR = # QNR.
    Proof.
      rewrite QNR_QR_c, complement_card;
        eauto using finite_QR, odd_prime_positive, QR_Euler_Phi.
      fold Euler_Phi.
      now rewrite size_of_QR, <-add_1_r, mul_distr_r, mul_1_l, sub_abba.
    Qed.

    Theorem size_of_QNR : Euler_Phi = (2 * # QNR)%N.
    Proof.
      rewrite <-add_1_r, mul_distr_r, mul_1_l, QNR_QR_c, complement_card,
      ? size_of_QR, <-? add_1_r, ? mul_distr_r, ? mul_1_l, <-size_QR_QNR,
      sub_abba at 1; auto using finite_QR, odd_prime_positive, QR_Euler_Phi.
    Qed.

    Notation ℤ_p_x := (polynomial_ring ℤ_).
    Notation Z_p_x := (poly ℤ_).

    Notation x := (polynomials.x ℤ_).

    Declare Scope poly_scope.
    Delimit Scope poly_scope with poly.
    Bind Scope poly_scope with poly.
    Infix "+" := (rings.add ℤ_p_x) : poly_scope.
    Infix "-" := (rings.sub ℤ_p_x) : poly_scope.
    Infix "*" := (rings.mul ℤ_p_x) : poly_scope.
    Infix "^" := (rings.pow ℤ_p_x) : poly_scope.
    Notation "0" := (rings.zero ℤ_p_x) : poly_scope.
    Notation "1" := (rings.one ℤ_p_x) : poly_scope.
    Notation "- a" := (rings.neg ℤ_p_x a) : poly_scope.
    Definition IRP := (IRP ℤ_ : Z_ → Z_p_x).
    Coercion IRP : Z_ >-> Z_p_x.

    Declare Scope F_scope.
    Delimit Scope F_scope with F.
    Bind Scope F_scope with 𝔽.
    Infix "^" := (fields.pow  (𝔽 prime_modulus)) : F_scope.

    Theorem Euler_Criterion_QR : ∀ a : Z_, a ∈ QR → a^(# QR) = (1 : Z_).
    Proof.
      intros a H.
      apply Specify_classification in H as [H H0].
      rewrite <-specify_action in H0.
      destruct H0 as [H0 [x H1]].
      subst.
      unfold square.
      rewrite <-(rings.pow_2_r ℤ_), <-(rings.pow_mul_r ℤ_), <-size_of_QR.
      auto using Euler, unit_square, odd_prime_positive.
    Qed.

    Theorem roots_QR : roots _ (x^(# QR) - 1)%poly = QR.
    Proof.
      assert (QR ⊂ roots ℤ_ ((x ^ (# QR))%poly + (- (1))%poly)) as S.
      { intros x H.
        apply Specify_classification; simpl Rset.
        pose proof H as H0.
        apply Specify_classification in H0 as [H0 H1].
        rewrite <-(setify_action _ _ H0), <-specify_action in *.
        destruct H1 as [H1 [a H2]].
        split; auto using elts_in_set.
        rewrite eval_add, eval_neg, IRP_1, eval_const, eval_x_to_n,
        Euler_Criterion_QR, A4; auto. }
      assert ((x ^ (# QR) + - (1))%poly ≠ 0%poly) as N.
      { apply nonzero_coefficients.
        exists 0%N.
        rewrite coefficient_add, coefficient_neg, coeffs_of_x_ne_n, IRP_1,
        coeff_const, rings.A3, rings.neg_0; intros H.
        - rewrite <-(neg_0 ℤ_) in H.
          contradiction (integral_domains.minus_one_nonzero
                           (ℤ_ID prime_modulus)).
        - contradiction Euler_Phi_nonzero; auto using odd_prime_positive.
          rewrite size_of_QR, <-H.
          ring. }
      assert (degree _ (x^(# QR) + (-(1)))%poly = # QR) as D.
      { apply naturals.le_antisymm.
        - rewrite <-max_0_r.
          eapply naturals.le_trans; eauto using (add_degree ℤ_).
          exists 0%N.
          rewrite add_0_r.
          f_equal.
          + apply degree_x_to_n; now destruct Z_mod_prime_is_ID.
          + apply const_classification.
            exists (-(1)).
            now rewrite IRP_1, IRP_neg.
        - apply finite_subsets in S;
            eauto using finite_roots, Z_mod_prime_is_ID,
            naturals.le_trans, root_degree_bound. }
      rewrite rings.sub_is_neg.
      apply eq_sym, finite_subsets_bijective, finite_cardinality_equinumerous,
      naturals.le_antisymm; auto using finite_subsets, finite_roots,
                            finite_QR, odd_prime_positive, Z_mod_prime_is_ID.
      rewrite <-D at 2; auto using root_degree_bound, Z_mod_prime_is_ID.
    Qed.

    Theorem roots_QNR : roots _ (x^(# QR) + 1)%poly = QNR.
    Proof.
      pose proof (eq_refl Euler_Phi_set) as E.
      replace Euler_Phi_set with (QR ∪ QNR) in E at 1.
      2: { apply Extensionality.
           split; intros H.
           - apply Pairwise_union_classification in H as [H | H];
             apply Specify_classification in H as [H H0];
             apply Specify_classification;
             rewrite <-(setify_action _ _ H), <-specify_action in *;
             split; auto; now rewrite <-units_in_ℤ_.
           - apply Specify_classification in H as [H H0].
             apply Pairwise_union_classification.
             destruct (classic (z ∈ QR)); auto.
             right.
             apply Specify_classification.
             now rewrite <-(setify_action _ _ H),
             <-specify_action, units_in_ℤ_ in *. }
      replace Euler_Phi_set with
          ((roots _ (x^(# QR) - 1)%poly) ∪ (roots _ (x^(# QR) + 1)%poly)) in E.
      2: { rewrite <-prod_root, <-difference_of_squares, <-rings.pow_mul_l,
           <-rings.pow_2_r, <-rings.pow_mul_r, <-size_of_QR, rings.M3,
           rings.sub_is_neg; auto using Z_mod_prime_is_ID.
           apply Extensionality.
           split; intros H.
           - apply Specify_classification in H as [H H0]; simpl Rset in H.
             apply Specify_classification.
             set (ζ := exist _ _ H : Z_).
             rewrite <-(setify_action _ _ H), <-specify_action,
             <-units_in_ℤ_ in *; fold ζ in H0 |-*.
             split; auto.
             rewrite eval_add, eval_neg, IRP_1, eval_const, eval_x_to_n,
             <-(rings.A4 ℤ_ (1:Z_)), ? (rings.A1 ℤ_ _ (-(1:Z_))) in H0;
               simpl in *.
             apply (cancellation_add ℤ_) in H0.
             eapply unit_pow_closure; try rewrite H0.
             + pose proof Euler_Phi_nonzero odd_prime_positive.
               apply succ_0 in H1 as [m H1].
               rewrite H1.
               apply naturals.lt_succ.
             + apply one_unit.
           - apply Specify_classification in H as [H H0].
             apply Specify_classification; simpl Rset.
             set (ζ := exist _ _ H : Z_).
             rewrite <-(setify_action _ _ H), <-specify_action,
             <-units_in_ℤ_ in *; fold ζ in H0 |-*.
             split; auto.
             rewrite eval_add, eval_neg, IRP_1, eval_const, eval_x_to_n,
             Euler, A4; auto using odd_prime_positive. }
      apply Euler_Phi_lemma in E; auto using roots_QR.
      { apply NNPP.
        intros H.
        apply Nonempty_classification in H as [x H].
        apply Pairwise_intersection_classification in H as [H H0].
        apply Specify_classification in H0 as [H0 H1].
        now rewrite <-(setify_action _ _ H0), <-specify_action in *. }
      apply NNPP.
      intros H.
      apply Nonempty_classification in H as [z H].
      apply Pairwise_intersection_classification in H as [H H0].
      apply Specify_classification in H as [H H1], H0 as [H0 H2].
      simpl Rset in *.
      rewrite <-(setify_action _ _ H), <-specify_action, <-H2, rings.sub_is_neg,
      ? eval_add, ? eval_neg, ? IRP_1, ? eval_const, ? eval_x_to_n in *.
      apply (rings.cancellation_add ℤ_) in H1; simpl in H1.
      contradiction one_ne_minus_one.
      now rewrite <-H1, IZn_neg.
    Qed.

    Theorem Euler_Criterion_QNR :
      ∀ a : Z_, a ∈ QNR → a^(# QR) = ((-(1)) : Z_)%Z.
    Proof.
      intros a H.
      rewrite <-roots_QNR in H.
      apply Specify_classification in H as [H H0]; simpl Rset in *.
      rewrite <-(setify_action _ _ H), <-specify_action in *.
      rewrite eval_add, IRP_1, eval_const, eval_x_to_n, (A1 _ 1),
      <-(rings.A4 ℤ_ (1:Z_)) in H0; simpl in H0.
      apply (rings.cancellation_add ℤ_) in H0.
      rewrite <-IZn_neg, <-H0.
      f_equal.
      now apply set_proj_injective.
    Qed.

    Theorem Euler's_Criterion : ∀ a : Z_, a^(# QR) = ((legendre_symbol a) : Z_).
    Proof.
      intros a.
      unfold legendre_symbol.
      repeat destruct excluded_middle_informative;
        auto using Euler_Criterion_QR, Euler_Criterion_QNR.
      destruct (classic (a = 0)) as [H | H]; subst.
      - rewrite rings.pow_0_l; auto.
        intros H.
        contradiction Euler_Phi_nonzero; auto using odd_prime_positive.
        now rewrite size_of_QR, H, naturals.mul_0_r.
      - contradict H.
        now apply QR_QNR_0.
    Qed.

    Definition trinary_value (a : Z) := a = 0 ∨ a = 1 ∨ a = (-(1))%Z.

    Lemma trinary_legendre : ∀ a, trinary_value (legendre_symbol a).
    Proof.
      intros a.
      unfold legendre_symbol, trinary_value.
      repeat destruct excluded_middle_informative; tauto.
    Qed.

    Lemma trinary_mul :
      ∀ a b, trinary_value a → trinary_value b → trinary_value (a*b).
    Proof.
      unfold trinary_value.
      intros a b [H | [H | H]] [H0 | [H0 | H0]]; subst;
        rewrite ? (mul_0_l ℤ), ? (mul_0_r ℤ), ? integers.M3,
        ? (rings.mul_neg_neg ℤ), ? (M3_r ℤ); auto.
    Qed.

    Theorem trinary_IZn_eq : ∀ a b,
        trinary_value a → trinary_value b → (a : Z_) = (b : Z_) ↔ a = b.
    Proof.
      unfold trinary_value.
      intros a b [H | [H | H]] [H0 | [H0 | H0]]; subst; split; intros H1;
        try tauto; try now contradiction integers.zero_ne_1;
          try now contradiction one_ne_minus_one;
          try now contradiction (integral_domains.nontriviality
                                   (ℤ_ID prime_modulus));
          try now contradiction (integral_domains.minus_one_nonzero
                                   (integers.ℤ_ID));
          try (now contradiction (ordered_rings.one_ne_minus_one ℤ_order));
          try (rewrite <-IZn_neg in H1;
               now contradiction (integral_domains.minus_one_nonzero
                                    (ℤ_ID prime_modulus))).
    Qed.

    Theorem trinary_pow_neg_1_l : ∀ k, trinary_value ((-(1))^k)%Z.
    Proof.
      intros k.
      unfold trinary_value.
      destruct (pow_neg_1_l ℤ k) as [H | H]; simpl in *; rewrite H; intuition.
    Qed.

    Theorem legendre_mult : ∀ a b : Z_,
        legendre_symbol (a * b) = (legendre_symbol a * legendre_symbol b)%Z.
    Proof.
      intros a b.
      apply trinary_IZn_eq; auto using trinary_legendre, trinary_mul.
      now rewrite <-IZn_mul, <-? Euler's_Criterion, rings.pow_mul_l.
    Qed.

    Variable a : N.
    Hypothesis p_ndiv_a : ¬ p｜a.

    Definition QR_b (l : N) : Z.
    Proof.
      destruct (excluded_middle_informative (0 < a * l)%Z) as [H | H].
      - apply (division_QR (a*l)%Z p) in H.
        + destruct (constructive_indefinite_description _ H) as [q H0].
          exact q.
        + apply odd_prime_positive.
      - exact 0.
    Defined.

    Definition QR_r (l : N) : Z.
    Proof.
      destruct (excluded_middle_informative (0 < a * l)%Z) as [H | H].
      - apply (division_QR (a*l)%Z p) in H.
        + destruct (constructive_indefinite_description _ H) as [q H0].
          destruct (constructive_indefinite_description _ H0) as [r H1].
          exact r.
        + apply odd_prime_positive.
      - exact 0.
    Defined.

    Definition QR_ε (l : N) := rationals.QR_ε (a*l)%Z p.

    Theorem QR_ε_values : ∀ l, QR_ε l = ± 1.
    Proof.
      intros l.
      unfold QR_ε, rationals.QR_ε.
      apply (pow_neg_1_l ℤ).
    Qed.

    Theorem QR_ε_trinary : ∀ l, trinary_value (QR_ε l).
    Proof.
      intros l.
      destruct (QR_ε_values l) as [H | H]; right; intuition.
    Qed.

    Theorem modified_division_algorithm :
      ∀ l : N, (a*l = QR_b l * p + QR_ε l * QR_r l)%Z.
    Proof.
      intros l.
      unfold QR_b, QR_ε, QR_r.
      destruct excluded_middle_informative.
      - repeat destruct constructive_indefinite_description.
        rewrite (integers.M1 x p).
        intuition.
      - unfold integers.zero in n0.
        rewrite INZ_mul, INZ_lt, <-naturals.le_not_gt,
        ? (mul_0_l ℤ), ? (mul_0_r ℤ), integers.A3 in *.
        apply INZ_eq, naturals.le_antisymm; auto using zero_le.
    Qed.

    Theorem QR_r_bound : ∀ l, (0 ≤ QR_r l ≤ # QR)%Z.
    Proof.
      intros l.
      unfold QR_r.
      destruct excluded_middle_informative.
      - repeat destruct constructive_indefinite_description.
        destruct a0 as [[H H0] H1].
        split; auto.
        eapply ordered_rings.le_trans; eauto; fold integers.le.
        apply IZQ_le, floor_lower.
        unfold rationals.one; fold (IZQ 1).
        rewrite inv_div, IZQ_add; auto using (zero_ne_2 ℤ_order).
        apply (mul_denom_l ℚ_order);
          try apply IZQ_lt, (zero_lt_2 ℤ_order); simpl.
        rewrite IZQ_mul.
        apply IZQ_lt.
        unfold integers.one.
        rewrite (D1_l ℤ), ? INZ_add, ? INZ_mul, add_1_r, <-size_of_QR,
        <-Prime_Euler_Phi_Z, <-add_1_r, <-INZ_mul, <-INZ_add;
          auto using odd_prime_positive.
        fold integers.one; apply (ordered_rings.lt_shift ℤ_order); simpl.
        replace (p - 1 + 2 * 1 + - p)%Z with 1%Z by ring.
        auto using integers.zero_lt_1.
      - split.
        + apply le_refl.
        + apply INZ_le, zero_le.
    Qed.

    Definition QR_r_N : N → N.
    Proof.
      intros l.
      destruct (QR_r_bound l) as [H H0].
      rewrite le_def in H.
      destruct (constructive_indefinite_description _ H) as [r H1].
      exact r.
    Defined.

    Lemma QR_r_N_action : ∀ l, QR_r l = QR_r_N l.
    Proof.
      intros l.
      unfold QR_r_N.
      destruct QR_r_bound, constructive_indefinite_description.
      now rewrite integers.A3 in e.
    Qed.

    Definition QR_r_function := sets.functionify ω ω QR_r_N.

    Lemma QR_lt_p : ¬ p ≤ # QR.
    Proof.
      apply lt_not_ge.
      rewrite lt_def.
      exists ((# QR) + 1)%N.
      split.
      + rewrite add_1_r.
        intros H4.
        now apply INZ_eq, PA4 in H4.
      + rewrite INZ_add, add_assoc, <-mul_2_r, mul_comm, <-size_of_QR,
        (Prime_Euler_Phi prime_modulus odd_prime_positive), <-INZ_add,
        <-INZ_sub; rewrite  <-modulus_in_Z; try ring.
        apply lt_0_le_1, odd_prime_positive.
    Qed.

    Theorem QR_r_nonzero : ∀ l, (1 ≤ l ≤ # QR)%N → 1 ≤ QR_r l.
    Proof.
      intros l [H H0].
      destruct (QR_r_bound l) as [[H1 | H1] H2]; try now apply lt_0_le_1.
      assert (p｜a*l) as H3.
      { rewrite modified_division_algorithm, <-H1.
        apply div_add; fold divide.
        - apply div_mul_l, div_refl.
        - apply div_mul_l, div_0_r. }
      apply Euclid's_lemma in H3 as [H3 | H3]; try now intuition.
      apply INZ_le in H, H0.
      apply div_le in H3.
      - contradiction QR_lt_p.
        eapply (ordered_rings.le_trans ℤ_order); eauto.
      - now apply lt_0_le_1.
    Qed.

    Theorem QR_r_restriction_construction :
      (image (restriction QR_r_function {x of type ω | 1 ≤ x ≤ # QR}) ⊂
             {x of type ω | 1 ≤ x ≤ # QR})%N.
    Proof.
      intros z H.
      apply Specify_classification in H as [H [x [H0 H1]]].
      rewrite restriction_domain, restriction_range, <-restriction_action,
      Pairwise_intersection_classification in *; auto.
      destruct H0 as [H0 H2].
      apply Specify_classification in H0 as [H0 H3].
      set (ξ := exist _ _ H0 : N).
      rewrite <-(setify_action _ _ H0), <-specify_action in *.
      fold ξ in H1, H2, H3.
      unfold QR_r_function in *.
      rewrite sets.functionify_domain, sets.functionify_range,
      ? functionify_action in *.
      unfold QR_r_N in H1.
      destruct QR_r_bound, constructive_indefinite_description as [z'].
      rewrite integers.A3 in e.
      subst.
      apply Specify_classification.
      rewrite <-specify_action.
      repeat split; auto using N_in_ω; apply INZ_le; destruct e;
        auto using QR_r_nonzero.
    Qed.

    Definition QR_r_res := restriction_Y _ _ QR_r_restriction_construction.

    Theorem QR_r_res_domain : domain QR_r_res = {x of type ω | 1 ≤ x ≤ # QR}%N.
    Proof.
      unfold QR_r_res, QR_r_function.
      rewrite restriction_Y_domain, restriction_domain, sets.functionify_domain.
      apply Intersection_subset.
      intros x H.
      now apply Specify_classification in H.
    Qed.

    Theorem QR_r_res_action : ∀ i, (1 ≤ i ≤ # QR)%N → QR_r_res i = QR_r_N i.
    Proof.
      intros i H.
      assert (i ∈ {x of type ω | (1 ≤ x ≤ # QR)%N} ∩ domain QR_r_function).
      { apply Pairwise_intersection_classification.
        split.
        - apply Specify_classification.
          rewrite <-specify_action.
          split; auto using N_in_ω.
        - unfold QR_r_function.
          rewrite sets.functionify_domain.
          auto using N_in_ω. }
      unfold QR_r_res.
      rewrite restriction_Y_action.
      2: { now rewrite restriction_domain. }
      rewrite <-restriction_action; auto.
      unfold QR_r_function.
      now rewrite functionify_action.
    Qed.

    Lemma range_constraint : ∀ i j,
        1 ≤ i ≤ # QR → 1 ≤ j ≤ # QR → (i : Z_) = (j : Z_) → i = j.
    Proof.
      intros i j [H H0] [H1 H2] H3.
      apply injective_mod_n_on_interval; try now apply IZn_eq.
      - split.
        eapply (ordered_rings.le_trans ℤ_order); eauto.
        + apply or_introl, zero_lt_1.
        + eapply (ordered_rings.le_lt_trans ℤ_order); eauto.
          apply lt_not_ge, QR_lt_p.
      - split.
        eapply (ordered_rings.le_trans ℤ_order); eauto.
        + apply or_introl, zero_lt_1.
        + eapply (ordered_rings.le_lt_trans ℤ_order); eauto.
          apply lt_not_ge, QR_lt_p.
    Qed.

    Lemma range_constraint_neg : ∀ i j,
        1 ≤ i ≤ # QR → 1 ≤ j ≤ # QR → (i : Z_) ≠ -(j : Z_).
    Proof.
      intros i j [H H0] [H1 H2] H3.
      Set Printing Coercions.
      assert (i+j = 0) as H4.
      { now rewrite H3, A1, A4. }
      rewrite IZn_add in H4.
      apply IZn_eq, injective_mod_n_on_interval in H4.
      - contradiction (ordered_rings.lt_irrefl ℤ_order 0); simpl.
        rewrite <-H4 at 2.
        apply (ordered_rings.O0 ℤ_order); simpl; now apply lt_0_le_1.
      - split.
        + left.
          apply (ordered_rings.O0 ℤ_order); simpl; now apply lt_0_le_1.
        + eapply (ordered_rings.le_lt_trans ℤ_order);
            try (eapply le_cross_add; eauto); simpl.
          rewrite <-(integers.M3 (# QR)), <-integers.D1,
          <-size_of_QR_in_Z, lt_def.
          exists 1%N.
          split.
          * intros H5.
            now apply INZ_eq, PA4 in H5.
          * fold integers.one.
            ring.
      - split.
        + apply le_refl.
        + apply odd_prime_positive.
    Qed.

    Theorem QR_r_res_bijective : bijective QR_r_res.
    Proof.
      pose proof QR_r_res_domain as Q.
      unfold QR_r_res in Q.
      rewrite restriction_Y_domain in Q.
      apply finite_set_injection_is_bijection; try rewrite QR_r_res_domain.
      { apply (subsets_of_finites_are_finite _ (S (# QR)));
          auto using naturals_are_finite.
        intros x H.
        apply Specify_classification in H as [H H0].
        set (ξ := exist _ _ H : N).
        rewrite <-(setify_action _ _ H), <-specify_action in *.
        fold ξ in H0 |-*.
        destruct H0 as [H0 H1].
        now apply lt_is_in, le_lt_succ. }
      { unfold QR_r_res, QR_r_function.
        now rewrite restriction_Y_range. }
      apply Injective_classification.
      intros x y H H0 H1.
      rewrite QR_r_res_domain in *.
      unfold QR_r_res in *.
      rewrite ? restriction_Y_action in *; try congruence.
      rewrite restriction_domain in Q.
      rewrite <-? restriction_action in *; try congruence.
      clear Q.
      unfold QR_r_function in *.
      apply Specify_classification in H as [H H2], H0 as [H0 H3].
      set (ξ := exist _ _ H : N).
      set (γ := exist _ _ H0 : N).
      rewrite <-(setify_action _ _ H), <-(setify_action _ _ H0),
      <-? specify_action, ? sets.functionify_action in *.
      fold ξ γ in H1, H2, H3 |-*.
      unfold QR_r_N in *.
      repeat destruct QR_r_bound.
      destruct constructive_indefinite_description as [r_x].
      destruct constructive_indefinite_description as [r_y].
      rewrite integers.A3 in e, e0.
      apply set_proj_injective in H1.
      assert ((a*ξ : Z_) = (a*γ : Z_) ∨ (a*ξ : Z_) = -(a*γ : Z_)) as [H4 | H4];
        destruct H2, H3; rewrite <-INZ_le in *.
      { rewrite ? IZn_mul, ? modified_division_algorithm, ? e, ? e0,
        <-? IZn_add, <-? IZn_mul, modulus_zero, ? (rings.mul_0_r ℤ_), ? A3,
        ? IZn_mul.
        destruct (QR_ε_values ξ) as [H7 | H7], (QR_ε_values γ) as [H8 | H8];
          rewrite H7, H8; try (left; congruence); right; subst; rewrite IZn_neg;
            apply IZn_eq; now ring_simplify. }
      - apply (cancellation_mul_l (ℤ_ID prime_modulus)), range_constraint in H4;
          auto.
        + apply INZ_eq in H4; congruence.
        + intros H7.
          apply IZn_eq, eqm_sym in H7.
          unfold eqm in H7.
          now ring_simplify in H7.
      - rewrite <-(mul_neg_1_r ℤ_), <-M2 in H4.
        apply (cancellation_mul_l (ℤ_ID prime_modulus)) in H4.
        + rewrite (mul_neg_1_r ℤ_) in H4.
          apply range_constraint_neg in H4; intuition.
        + intros H7.
          apply IZn_eq, eqm_sym in H7.
          unfold eqm in H7.
          now ring_simplify in H7.
    Qed.

    Lemma Gauss_Lemma_helper :
      prod ℤ_ (λ n, n : Z_) 1 (# QR) = prod ℤ_ (λ n, (QR_r n) : Z_) 1 (# QR).
    Proof.
      apply product_bijection.
      - intros j H.
        exists (QR_r_N j).
        apply QR_r_nonzero in H.
        pose proof (QR_r_bound j) as [H0 H1].
        repeat split.
        + apply INZ_le.
          now rewrite <-QR_r_N_action.
        + apply INZ_le.
          now rewrite <-QR_r_N_action.
        + now rewrite <-QR_r_N_action.
        + intros x' [[H2 H3] H4].
          apply INZ_eq.
          rewrite <-QR_r_N_action.
          apply IZn_eq, injective_mod_n_on_interval in H4; repeat split; auto.
          * left.
            now apply lt_0_le_1, INZ_le.
          * apply INZ_le in H3.
            eapply (ordered_rings.le_lt_trans ℤ_order); eauto.
            apply lt_not_ge, QR_lt_p.
          * eapply (ordered_rings.le_lt_trans ℤ_order); eauto.
            apply lt_not_ge, QR_lt_p.
      - intros i H.
        assert ((inverse QR_r_res) i ∈ ω).
        { assert ((range (inverse QR_r_res)) ⊂ ω) as H0.
          { rewrite inverse_range; auto using QR_r_res_bijective.
            unfold QR_r_res, QR_r_function.
            rewrite restriction_Y_domain, restriction_domain.
            intros x H0.
            apply Pairwise_intersection_classification in H0 as [H0 H1].
            now apply Specify_classification in H0. }
          apply H0, function_maps_domain_to_range.
          rewrite inverse_domain; auto using QR_r_res_bijective.
          unfold QR_r_res.
          rewrite restriction_Y_range.
          apply Specify_classification.
          rewrite <-specify_action.
          eauto using N_in_ω. }
        set (η := exist _ _ H0 : N).
        exists η.
        split.
        + assert (1 ≤ η ≤ # QR)%N as H1.
          { assert (η ∈ range (inverse QR_r_res)) as H1.
            { unfold η.
              simpl.
              apply function_maps_domain_to_range.
              rewrite inverse_domain; auto using QR_r_res_bijective.
              unfold QR_r_res.
              rewrite restriction_Y_range.
              apply Specify_classification.
              rewrite <-specify_action.
              eauto using N_in_ω. }
            rewrite inverse_range in H1; auto using QR_r_res_bijective.
            unfold QR_r_res in H1.
            rewrite restriction_Y_domain in H1.
            apply Pairwise_intersection_classification in H1 as [H1 H2].
            apply Specify_classification in H1.
            now rewrite <-specify_action in H1. }
          split; auto.
          rewrite QR_r_N_action.
          repeat f_equal.
          apply set_proj_injective.
          fold (INS (QR_r_N η)).
          rewrite <-QR_r_res_action; auto.
          unfold η.
          simpl.
          rewrite right_inverse; try rewrite inverse_domain;
            auto using QR_r_res_bijective.
          unfold QR_r_res.
          rewrite restriction_Y_range.
          apply Specify_classification.
          rewrite <-specify_action.
          auto using N_in_ω.
        + intros x' [H1 H2].
          apply range_constraint in H2.
          2: { split; apply INZ_le; intuition. }
          2: { split.
               - now apply QR_r_nonzero.
               - destruct (QR_r_bound x'); auto. }
          unfold η.
          rewrite QR_r_N_action in H2.
          apply INZ_eq, (f_equal INS) in H2.
          apply set_proj_injective.
          simpl.
          rewrite H2, <-QR_r_res_action, left_inverse;
            auto using QR_r_res_bijective.
          unfold QR_r_res.
          rewrite restriction_Y_domain.
          apply Pairwise_intersection_classification.
          split.
          * apply Specify_classification.
            rewrite <-specify_action.
            auto using N_in_ω.
          * unfold QR_r_function.
            rewrite sets.functionify_domain.
            auto using N_in_ω.
    Qed.

    Theorem Gauss's_Lemma_mod_p :
      (legendre_symbol a : Z_) =
      ((-(1))^sum_N (λ l : N, QR_ε_exponent (a*l)%Z p) 1 (# QR)).
    Proof.
      pose (eq_refl ((a : Z_)^(# QR) * prod ℤ_ (λ n, n : Z_) 1 (# QR))) as H.
      replace (# QR) with (S ((# QR) - 1))%N in H at 3.
      2: { rewrite <-add_1_r, add_comm, sub_abab; auto using size_QR_ge_1. }
      pose (prod_mul ℤ_ (λ n, n : Z_) 1 (# QR) (a : Z_) size_QR_ge_1)
        as H0; simpl in H0; rewrite H0 in H; clear H0.
      replace (λ n : N, a * n) with (λ l : N, (QR_ε l * QR_r l)) in H.
      2: { extensionality l.
           rewrite ? IZn_mul, modified_division_algorithm.
           apply IZn_eq.
           rewrite (n_mod_n_is_0 p) at 2.
           now rewrite (rings.mul_0_r ℤ), integers.A3. }
      unfold QR_ε, rationals.QR_ε in H.
      rewrite Gauss_Lemma_helper, Euler's_Criterion, prod_dist in H.
      replace (λ l : N, (((-(1))%Z^ QR_ε_exponent (INZ a * INZ l) p)%Z : Z)
               : Z_) with
          (λ l : N, (((-(1))^ QR_ε_exponent (INZ a * INZ l) p))) in H.
      2: { extensionality l.
           now rewrite <-IZn_pow, IZn_neg. }
      apply (cancellation_mul_r (ℤ_ID prime_modulus)) in H;
        try now rewrite H, prod_sum.
      rewrite <-Gauss_Lemma_helper.
      apply unit_nonzero, unit_prod_closure.
      intros i [H0 H1].
      apply nonzero_unit; auto.
      intros H2.
      apply IZn_eq, eqm_sym in H2.
      unfold eqm in H2.
      ring_simplify in H2.
      apply div_le in H2; try now apply lt_0_le_1, INZ_le.
      apply INZ_le in H1.
      assert (p ≤ # QR) as H3 by
            (eapply (ordered_rings.le_trans ℤ_order); eauto).
      apply le_not_gt in H3; simpl in H3.
      apply H3.
      rewrite lt_def.
      exists ((# QR) + 1)%N.
      split.
      + rewrite add_1_r.
        intros H4.
        now apply INZ_eq, PA4 in H4.
      + rewrite INZ_add, add_assoc, <-mul_2_r, mul_comm, <-size_of_QR,
        (Prime_Euler_Phi prime_modulus odd_prime_positive), <-INZ_add,
        <-INZ_sub; rewrite  <-modulus_in_Z; try ring.
        apply lt_0_le_1, odd_prime_positive.
    Qed.

    Theorem Gauss's_Lemma :
      legendre_symbol a =
      ((-(1))^sum_N (λ l : N, QR_ε_exponent (a*l)%Z p) 1 (# QR))%Z.
    Proof.
      apply trinary_IZn_eq.
      - apply trinary_legendre.
      - apply trinary_pow_neg_1_l.
      - rewrite <-IZn_pow, <-IZn_neg.
        apply Gauss's_Lemma_mod_p.
    Qed.

  End Odd_prime_modulus.

End Modular_arithmetic.

Notation "a % n " := ( modulo n a) (at level 45) : Z_scope.

Theorem mod_0_r : ∀ a, a % 0 = 0.
Proof.
  intros a.
  unfold modulo.
  destruct excluded_middle_informative; auto.
  exfalso.
  contradiction (ordered_rings.lt_irrefl ℤ_order 0).
Qed.

Theorem mod_1_r : ∀ a, a % 1 = 0.
Proof.
  intros a.
  unfold modulo.
  destruct excluded_middle_informative; auto.
  repeat destruct constructive_indefinite_description.
  destruct a0 as [H [[H0 | H0] H1]]; auto.
  contradiction (lt_0_1 x0).
Qed.
