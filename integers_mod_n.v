Set Warnings "-ambiguous-paths".
Require Export combinatorics Setoid.

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

Theorem n_mod_n_is_0 : ∀ n, n ≡ 0 (mod n).
Proof.
  intros n.
  apply eqm_sym.
  unfold eqm.
  ring_simplify.
  now apply div_refl.
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
  unfold eqm.
  exists 1.
  simpl.
  now ring_simplify.
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
    induction k using Induction.
    - now rewrite ? rings.pow_0_r.
    - now rewrite ? rings.pow_succ_r, IHk, H.
  Qed.

  Definition modulo : Z → Z.
  Proof.
    intros x.
    destruct (excluded_middle_informative (0 < n)).
    - pose proof division_algorithm x n l as H.
      destruct (constructive_indefinite_description _ H) as [q H0].
      clear H.
      destruct (constructive_indefinite_description _ H0) as [r H1].
      clear H0.
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
      replace a with ((exist _ _ H : Z) : set) by auto.
      apply Specify_classification; split.
      + apply Product_classification; eauto.
      + eauto using eqm_refl.
    - intros a b H H0 H1.
      apply Specify_classification; split.
      + apply Product_classification; eauto.
      + apply Specify_classification in H1 as [H1 [a' [b' [H2 H3]]]].
        apply Ordered_pair_iff in H2 as [H2 H4].
        subst.
        exists b', a'.
        split; auto.
        eauto using eqm_sym.
    - intros a b c H H0 H1 H2 H3.
      apply Specify_classification; split.
      + apply Product_classification; eauto.
      + apply Specify_classification in H2 as [H2 [a' [b' [H4 H5]]]].
        apply Specify_classification in H3 as [H3 [b'' [c' [H6 H7]]]].
        apply Ordered_pair_iff in H4 as [H4 H8].
        apply Ordered_pair_iff in H6 as [H6 H9].
        subst.
        apply set_proj_injective in H6; subst.
        eauto using eqm_trans.
  Qed.

  Declare Scope Zn_scope.
  Delimit Scope Zn_scope with Zn.
  Open Scope Zn_scope.

  Definition Zset_mod := Zset / relation_mod.

  Definition Z_ := elts (Zset_mod).

  Bind Scope Zn_scope with Z_.

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
    split; intros H.
    - unfold Z_to_Z_n in H.
      apply quotient_equiv in H; auto using equivalence_mod.
      apply Specify_classification in H as [H [a' [b' [H0 H1]]]].
      apply Ordered_pair_iff in H0 as [H0 H2].
      simpl in *.
      apply set_proj_injective in H0.
      apply set_proj_injective in H2.
      now subst.
    - unfold Z_to_Z_n.
      apply quotient_equiv; auto using equivalence_mod.
      apply Specify_classification.
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
    f_equal.
    now apply set_proj_injective.
  Qed.

  Theorem Zlift_equiv : ∀ a : Z, a ≡ (a : Z_) : Z (mod n).
  Proof.
    intros a.
    apply IZn_eq.
    now rewrite <-Zproj_eq.
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
    apply IZn_eq.
    now rewrite <-? Zlift_equiv, integers.A2.
  Qed.

  Theorem A3 : ∀ a : Z_, a + 0 = a.
  Proof.
    intros a.
    unfold add.
    now rewrite Zproj_eq, IZn_eq, <-Zlift_equiv, integers.A1, integers.A3.
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

  Theorem M3 : ∀ a : Z_, a * 1 = a.
  Proof.
    intros a.
    unfold mul.
    now rewrite Zproj_eq, IZn_eq, <-Zlift_equiv, integers.M1, integers.M3.
  Qed.

  Theorem D1 : ∀ a b c, (a + b) * c = a * c + b * c.
  Proof.
    intros a b c.
    unfold add, mul.
    apply IZn_eq.
    now rewrite <-? Zlift_equiv, integers.D1.
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

  Section finite_mod.

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
        apply injective_mod_n_on_interval; auto.
        apply IZn_eq.
        rewrite <-H2, Zproj_eq.
        apply IZn_eq.
        rewrite <-H.
        rewrite (eqn_zero n) at 2.
        now ring_simplify.
    Qed.

    Definition modulus_in_N : N.
    Proof.
      apply lt_def in modulus_pos.
      destruct (constructive_indefinite_description _ modulus_pos) as [k].
      destruct a.
      exact k.
    Defined.

    Theorem size_of_Zset_mod_in_Z : n = modulus_in_N.
    Proof.
      unfold modulus_in_N.
      destruct constructive_indefinite_description, a.
      subst.
      ring.
    Qed.

    Definition map_to_N : elts modulus_in_N → N.
      intros x.
      pose proof (elts_in_set _ x) as H.
      apply elements_of_naturals_are_naturals in H;
        auto using (elts_in_set _ modulus_in_N).
      exact (exist _ _ H).
    Defined.

    Theorem map_to_lt_n : ∀ x, map_to_N x < n.
    Proof.
      intros x.
      rewrite size_of_Zset_mod_in_Z.
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

    Theorem bijection_of_Zset_mod : (Zset_mod ~ modulus_in_N)%set.
    Proof.
      symmetry.
      exists (sets.functionify _ _ map_to_mod_n).
      rewrite sets.functionify_domain, sets.functionify_range.
      repeat split; auto.
      - apply Injective_classification.
        intros x y H H0 H1.
        rewrite ? sets.functionify_domain, ? sets.functionify_range in *.
        unfold sets.functionify in *.
        destruct constructive_indefinite_description as [f].
        destruct a as [H2 [H3 H4]].
        set (ξ := (exist _ _ H : elts modulus_in_N)).
        set (γ := (exist _ _ H0 : elts modulus_in_N)).
        replace x with (ξ : set) in *; replace y with (γ : set) in *; auto.
        rewrite ? H4 in H1.
        repeat f_equal.
        apply set_proj_injective in H1.
        unfold map_to_mod_n in H1.
        apply IZn_eq, injective_mod_n_on_interval, INZ_eq in H1;
          auto using map_to_ge_0, map_to_lt_n.
        inversion H1.
        subst.
        unfold ξ, γ.
        now replace H with H0 by now apply proof_irrelevance.
      - apply Surjective_classification.
        intros y H.
        rewrite ? sets.functionify_domain, ? sets.functionify_range in *.
        set (γ := (exist _ _ H : Z_)).
        replace y with (elt_to_set _ γ) by auto.
        destruct (surjective_mod_n_on_interval γ) as [x [[[H0 H1] H2] H3]].
        apply le_def in H0 as H4.
        destruct H4 as [ξ H4].
        ring_simplify in H4.
        exists ξ.
        assert (ξ ∈ modulus_in_N) as H5.
        { apply lt_is_in, INZ_lt.
          rewrite <-size_of_Zset_mod_in_Z.
          congruence. }
        split; auto.
        replace (ξ : set) with ((exist _ _ H5 : elts _) : set) by auto.
        unfold sets.functionify.
        destruct constructive_indefinite_description as [f], a as [H6 [H7 H8]].
        rewrite H8, H2, H4.
        f_equal.
        apply IZn_eq, eq_eqm.
        f_equal.
        now apply set_proj_injective.
    Qed.
 
    Theorem finite_Z_mod : finite Zset_mod.
    Proof.
      exists modulus_in_N.
      auto using bijection_of_Zset_mod.
    Qed.

    Theorem size_of_Z_mod : # Zset_mod = modulus_in_N.
    Proof.
      auto using equivalence_to_card, bijection_of_Zset_mod.
    Qed.

    Definition Euler_Phi := # {x in Zset_mod | ∃ a : Z,
                                 x = elt_to_set _ (a : Z_) ∧ gcd(a, n) = 1}.

    Hypothesis prime_modulus : prime n.

    Theorem Prime_Euler_Phi : (Euler_Phi = modulus_in_N - 1)%N.
    Proof.
      intros.
      rewrite <-(singleton_card (elt_to_set _ (0 : Z_))), <-size_of_Z_mod,
      <-complement_card; auto using finite_Z_mod.
      2: { intros z H.
           apply Singleton_classification in H.
           subst.
           auto using elts_in_set. }
      apply f_equal, Extensionality.
      split; intros H.
      - apply Specify_classification in H as [H [a [H0 H1]]].
        subst.
        apply Complement_classification.
        split; auto.
        intros H0.
        apply Singleton_classification, set_proj_injective, IZn_eq in H0.
        destruct prime_modulus as [H3 H4].
        contradict H3.
        apply H1; try apply rings.divide_refl.
        symmetry in H0.
        unfold eqm in H0.
        now replace a with (a - 0)%Z by ring.
      - apply Complement_classification in H as [H H0].
        apply Specify_classification.
        split; auto.
        set (ζ := exist _ _ H : Z_).
        replace z with (elt_to_set _ ζ) in * by auto.
        exists ζ.
        split; try now rewrite <-Zproj_eq.
        repeat split; try apply div_1_l.
        intros d H1 H2.
        destruct prime_modulus as [H3 H4].
        apply H4 in H2 as [H2 | H2]; auto.
        destruct H2 as [H2 H5]; fold integers.divide in H2, H5.
        contradict H0.
        apply Singleton_classification.
        f_equal.
        rewrite Zproj_eq, IZn_eq, eqm_sym_iff at 1.
        unfold eqm.
        ring_simplify.
        eapply div_trans; eauto.
    Qed.

  End finite_mod.

End Modular_arithmetic.

Notation "a % n " := ( modulo n a) (at level 45) : Z_scope.

Theorem mod_0_r : ∀ a, a % 0 = 0.
Proof.
  intros a.
  unfold modulo.
  destruct excluded_middle_informative.
  - exfalso.
    rewrite (ordered_rings.lt_not_ge ℤ_order) in l.
    contradict l.
    now right.
  - auto.
Qed.

Theorem mod_1_r : ∀ a, a % 1 = 0.
Proof.
  intros a.
  unfold modulo.
  destruct excluded_middle_informative; auto.
  repeat destruct constructive_indefinite_description.
  clear e.
  destruct a0 as [H [[H0 | H0] H1]]; auto.
  contradiction (lt_0_1 x0).
Qed.
