Set Warnings "-ambiguous-paths,-notation-overridden".
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
  replace (a-b) with ((-1%Z)*(b-a)) by ring.
  now apply div_mul_l.
Qed.

Theorem eqm_gcd : ∀ n a b, a ≡ b (mod n) → gcd(a, n) = 1 → gcd(b, n) = 1.
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
    replace (-y--x) with ((-1%Z)*(y-x)) by ring.
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
      destruct (constructive_indefinite_description H) as [q H0].
      destruct (constructive_indefinite_description H0) as [r H1].
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
    {z in 𝐙 × 𝐙 | ∃ a b : Z, (a, b) = z ∧ a ≡ b (mod n)}.

  Theorem equivalence_mod : is_equivalence 𝐙 relation_mod.
  Proof.
    repeat split.
    - intros a H.
      rewrite (reify H).
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

  Definition 𝐙_ := (𝐙 / relation_mod)%set.

  Definition Z_ := elts (𝐙_).

  Bind Scope Zn_scope with Z_.

  Definition IZnS := elt_to_set : Z_ → set.
  Coercion IZnS : Z_ >-> set.

  Definition Z_to_Z_n (x : Z) :=
    quotient_map relation_mod (exist (elts_in_set x)) : Z_.

  Coercion Z_to_Z_n : Z >-> Z_.

  Definition Z_n_to_Z : Z_ → Z.
  Proof.
    intros x.
    destruct (constructive_indefinite_description (quotient_lift x)) as [z].
    exact z.
  Defined.

  Coercion Z_n_to_Z : Z_ >-> Z.

  Definition add (a b : Z_) := a + b : Z_.

  Definition mul (a b : Z_) := a * b : Z_.

  Definition neg (a : Z_) := ((-a) : Z_).

  Definition sub (a b : Z_) := a - b : Z_.

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
    mkRing 𝐙_ (0 : Z_) (1 : Z_) add mul neg A3 A1 A2 M3 M1 M2 D1 A4.

  Add Ring Z_ring_raw : (ringify ℤ_).
  Add Ring Z_ring : (ringify ℤ_ : ring_theory (0 : Z_) _ _ _ _ _ eq).

  Infix "^" := (rings.pow ℤ_ : Z_ → N → Z_) : Zn_scope.
  Notation "a ^ n" := (rings.pow ℤ_ (a : Z_) (n : N) : Z_) : Zn_scope.

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

  Theorem IZn_pow : ∀ (a : Z) k, (a^k) = (a^k : Z)%Z.
  Proof.
    intros a k.
    induction k using Induction.
    - now rewrite ? rings.pow_0_r.
    - now rewrite ? rings.pow_succ_r, IHk, IZn_mul.
  Qed.

  Theorem units_in_ℤ_ : ∀ a : Z_, @rings.unit ℤ_ a ↔ gcd(a, n) = 1.
  Proof.
    split; intros H.
    - destruct H as [x H]; simpl in *.
      apply IZn_eq in H as [y H]; simpl in *; fold Z Z_ in x, y.
      repeat split; try apply div_1_l.
      intros z H1 H2.
      replace 1 with (a * x + n * (-y))%Z; try now apply div_mul_add.
      replace (n*(-y))%Z with (-(y*n))%Z by ring.
      rewrite <-H.
      ring.
    - apply Euclidean_algorithm in H as [x [y H]].
      exists (x : Z_); simpl.
      now rewrite H, <-IZn_add, <-? IZn_mul, modulus_zero, (mul_0_l ℤ_),
      A1, A3, M1, <-Zproj_eq.
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
      destruct constructive_indefinite_description
        as [q], constructive_indefinite_description as [r], a0 as [H H0].
      repeat split; intuition;
        [ symmetry | apply injective_mod_n_on_interval, IZn_eq; auto; subst ];
        now rewrite Zproj_eq, <-H, <-IZn_add, <-IZn_mul,
        modulus_zero, (mul_0_l ℤ_), A3.
    Qed.

    Definition modulus_in_N : N.
    Proof.
      apply lt_def in modulus_pos.
      destruct (constructive_indefinite_description modulus_pos) as [k], a.
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
      pose proof (elts_in_set x) as H.
      apply elements_of_naturals_are_naturals in H; eauto using elts_in_set.
      exact (exist H).
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

    Definition map_to_mod_n (x : elts modulus_in_N) := map_to_N x : Z_.

    Theorem bijective_map_to_mod_n : bijective (sets.functionify map_to_mod_n).
    Proof.
      split; rewrite ? Injective_classification, ? Surjective_classification,
             ? sets.functionify_domain, ? sets.functionify_range.
      - intros x y H H0 H1.
        rewrite (reify H), (reify H0), ? @functionify_action in *.
        apply set_proj_injective, IZn_eq, injective_mod_n_on_interval,
        INZ_eq in H1; auto using map_to_ge_0, map_to_lt_n.
        inversion H1.
        subst.
        now replace H with H0 in H1 by now apply proof_irrelevance.
      - intros y H.
        rewrite (reify H) in *.
        destruct (surjective_mod_n_on_interval (exist H))
          as [x [[[H0 H1] H2] H3]].
        apply le_def in H0 as [ξ H4].
        ring_simplify in H4; subst.
        exists ξ.
        assert (ξ ∈ modulus_in_N) as H5.
        { now rewrite <-lt_is_in, <-INZ_lt, <-modulus_in_Z. }
        split; auto.
        rewrite (reify H5), functionify_action, H2.
        now apply f_equal, set_proj_injective, f_equal,
        IZn_eq, eq_eqm, f_equal, set_proj_injective.
    Qed.

    Theorem bijection_of_Z_mod : (𝐙_ ~ modulus_in_N)%set.
    Proof.
      symmetry.
      exists (sets.functionify map_to_mod_n).
      rewrite sets.functionify_domain, sets.functionify_range.
      auto using bijective_map_to_mod_n.
    Qed.

    Theorem finite_Z_mod : finite 𝐙_.
    Proof.
      exists modulus_in_N.
      auto using bijection_of_Z_mod.
    Qed.

    Theorem Z_mod_card : # 𝐙_ = modulus_in_N.
    Proof.
      auto using equivalence_to_card, bijection_of_Z_mod.
    Qed.

    Definition Euler_Phi_set := {x of type 𝐙_ | gcd(x : Z_, n) = 1}.

    Definition Euler_Phi := # Euler_Phi_set.

    Definition 𝐔_ := {x of type 𝐙_ | @rings.unit ℤ_ x}.

    Theorem Euler_Phi_unit : Euler_Phi_set = 𝐔_.
    Proof.
      apply Extensionality.
      split; intros H; apply Specify_classification in H as [H H0];
        apply Specify_classification; rewrite (reify H), despecify in *; split;
          try apply units_in_ℤ_; eauto using eqm_gcd.
    Qed.

    Theorem unit_classification : ∀ a : Z_, a ∈ 𝐔_ ↔ @rings.unit ℤ_ a.
    Proof.
      split; intros H.
      - apply Specify_classification in H.
        now rewrite despecify in *.
      - apply Specify_classification.
        rewrite despecify.
        eauto using elts_in_set.
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
      rewrite Nonempty_classification, Euler_Phi_unit.
      exists (1 : Z_).
      apply Specify_classification.
      rewrite despecify.
      eauto using elts_in_set, (one_unit ℤ_).
    Qed.

    Corollary Euler_Phi_ge_1 : (1 ≤ Euler_Phi)%N.
    Proof.
      apply naturals.le_not_gt.
      intros H.
      apply le_lt_succ in H.
      auto using Euler_Phi_nonzero, naturals.le_antisymm, zero_le.
    Qed.

    Theorem Euler_Phi_helper : ∀ f,
        range f = Euler_Phi_set → ∀ x, x ∈ domain f → f x ∈ 𝐙_.
    Proof.
      intros f H x H0.
      pose proof function_maps_domain_to_range f x H0 as H1.
      rewrite H in H1.
      now apply Specify_classification in H1.
    Qed.

    Definition Euler_Phi_list : N → Z_.
    Proof.
      intros x.
      pose proof Euler_Phi_finite.
      destruct (constructive_indefinite_description H)
        as [m H0], (excluded_middle_informative (x < m)%N).
      - symmetry in H0.
        destruct (constructive_indefinite_description H0) as [f [H1 [H2 H3]]].
        rewrite lt_is_in, <-H1 in l.
        apply Euler_Phi_helper in l; auto.
        exact (exist l).
      - exact 0.
    Defined.

    Lemma Euler_Phi_set_classification :
      ∀ a : Z_, a ∈ Euler_Phi_set ↔ gcd(a, n) = 1.
    Proof.
      split; intros H.
      - apply Specify_classification in H as [H H0].
        rewrite (reify H), despecify in *.
        eapply eqm_gcd; eauto.
        apply IZn_eq, set_proj_injective.
        now rewrite <-? Zproj_eq.
      - apply Specify_classification.
        rewrite despecify.
        eauto using elts_in_set.
    Qed.

    Lemma Euler_Phi_list_unit :
      ∀ i, (0 ≤ i ≤ Euler_Phi - 1)%N → @rings.unit ℤ_ (Euler_Phi_list i).
    Proof.
      intros i [H H0].
      unfold Euler_Phi_list.
      destruct constructive_indefinite_description, excluded_middle_informative.
      - destruct constructive_indefinite_description as [f], a as [e0 [e1 b]].
        rewrite units_in_ℤ_, <-Euler_Phi_set_classification.
        simpl.
        rewrite <-e1.
        apply function_maps_domain_to_range.
        now rewrite e0, <-lt_is_in.
      - contradict n0.
        rewrite le_lt_succ, <-add_1_r, add_comm, sub_abab in H0;
          replace x with Euler_Phi;
          eauto using equivalence_to_card, Euler_Phi_ge_1.
    Qed.

    Lemma Euler_Phi_list_surj :
      ∀ a : Z_, @rings.unit ℤ_ a → ∃ i,
          (0 ≤ i ≤ Euler_Phi - 1)%N ∧ a = Euler_Phi_list i.
    Proof.
      intros a H.
      unfold Euler_Phi_list.
      destruct constructive_indefinite_description.
      rewrite units_in_ℤ_ in H.
      assert (a ∈ Euler_Phi_set) as H0.
      { apply Specify_classification.
        rewrite despecify.
        eauto using elts_in_set. }
      destruct constructive_indefinite_description as [f].
      repeat destruct a0.
      assert ((inverse f) a ∈ x) as H1.
      { rewrite <-e0, <-inverse_range; auto.
        apply function_maps_domain_to_range.
        rewrite inverse_domain, e1; auto. }
      assert ((inverse f) a ∈ ω) as H2 by
            (eapply elements_of_naturals_are_naturals; eauto using elts_in_set).
      set (ι := exist H2 : N).
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
      intros i j [H H0] [H1 H2] H3.
      unfold Euler_Phi_list in H3.
      destruct constructive_indefinite_description
        as [m], constructive_indefinite_description as [f].
      repeat destruct a; repeat destruct excluded_middle_informative;
        replace m with Euler_Phi in * by eauto using equivalence_to_card;
        try now contradiction n0;
        rewrite le_lt_succ, <-add_1_r, add_comm, sub_abab in *;
        eauto using equivalence_to_card, Euler_Phi_ge_1.
      destruct b as [H4 H5].
      inversion H3.
      rewrite Injective_classification in H4.
      apply set_proj_injective, H4; auto; now rewrite e0, <-lt_is_in.
    Qed.

    Definition Euler_Phi_product := prod ℤ_ Euler_Phi_list 0 (Euler_Phi - 1).

    Lemma Euler_Phi_product_unit : @rings.unit ℤ_ Euler_Phi_product.
    Proof.
      eauto using unit_prod_closure, Euler_Phi_list_unit.
    Qed.

    Section Euler's_Theorem.

      Variable a : Z_.
      Hypothesis unit_a : @rings.unit ℤ_ a.

      Definition Euler_Phi_product_shifted :=
        prod ℤ_ (λ x, a * (Euler_Phi_list x)) 0 (Euler_Phi - 1).

      Lemma Euler_Phi_equal : Euler_Phi_product = Euler_Phi_product_shifted.
      Proof.
        unfold Euler_Phi_product, Euler_Phi_product_shifted.
        apply iterate_bijection; auto using M1, M2; intros z H.
        - destruct (Euler_Phi_list_surj (a * Euler_Phi_list z)) as [i [H0 H1]].
          { apply unit_closure; auto using Euler_Phi_list_unit. }
          exists i.
          split; auto.
          intros y [H2 H3].
          apply Euler_Phi_list_inj; auto; congruence.
        - destruct unit_a as [x H0].
          destruct (Euler_Phi_list_surj (x * Euler_Phi_list z)) as [j [H1 H2]].
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

    Theorem order_construction : ∀ a : Z_, a ∈ 𝐔_ → ∃ m : N,
          (a^m = 1 ∧ m ≠ 0%N) ∧ (∀ k : N, (a^k = 1 ∧ k ≠ 0%N) → (m ≤ k)%N).
    Proof.
      intros a H.
      apply Specify_classification in H as [H H0].
      rewrite despecify in H0.
      apply naturals.WOP.
      apply Euler in H0.
      eauto using Euler_Phi_nonzero.
    Qed.

    Definition order : Z_ → N.
    Proof.
      intros a.
      destruct (excluded_middle_informative (a ∈ 𝐔_)).
      - apply order_construction in i.
        destruct (constructive_indefinite_description i) as [m].
        exact m.
      - exact 0%N.
    Defined.

    Theorem order_pos : ∀ a : Z_, a ∈ 𝐔_ → 0 < order a.
    Proof.
      intros a H.
      apply INZ_lt, nonzero_lt.
      unfold order.
      destruct excluded_middle_informative; try tauto.
      destruct constructive_indefinite_description; intuition.
    Qed.

    Theorem order_pow : ∀ a : Z_, a ∈ 𝐔_ → a^(order a) = 1.
    Proof.
      intros a H.
      unfold order.
      destruct excluded_middle_informative; try tauto.
      destruct constructive_indefinite_description; intuition.
    Qed.

    Theorem div_order : ∀ (a : Z_) (k : N), a ∈ 𝐔_ → order a｜k ↔ a^k = 1.
    Proof.
      split; intros H0; simpl in *.
      - destruct H0 as [x H0], (classic (k = 0%N)) as [H1 | H1].
        { now rewrite H1, rings.pow_0_r. }
        apply succ_0 in H1 as [m H1]; subst.
        rewrite integers.M1 in H0.
        assert (0 ≤ x) as H1.
        { eapply pos_mul_nonneg; simpl; fold integers.le; try rewrite <-H0.
          - now apply order_pos.
          - apply INZ_le, zero_le. }
        apply le_def in H1 as [c H1].
        rewrite H1, integers.A3, INZ_mul, INZ_eq in H0.
        now rewrite H0, rings.pow_mul_r, order_pow, rings.pow_1_l.
      - destruct (division_algorithm k (order a)) as
            [q [r [H1 [H2 H3]]]]; auto using order_pos; simpl in *.
        apply le_def in H2 as [c H2].
        rewrite integers.A3 in H2.
        subst.
        destruct (classic (c = 0)%N) as [H2 | H2]; subst.
        + exists q.
          now rewrite <-H1, integers.A1, integers.A3, rings.M1.
        + apply (ordered_rings.lt_not_ge ℤ_order) in H3; fold integers.le in *.
          contradict H3.
          unfold order.
          destruct excluded_middle_informative; try tauto.
          destruct constructive_indefinite_description as [m [[H3 H4] H5]].
          apply INZ_le, H5.
          split; auto.
          apply Specify_classification in H as H6.
          rewrite despecify, <-pow_nonneg, <-H1, integer_powers.pow_add_r,
          integer_powers.pow_mul_r, pow_nonneg, order_pow,
          integer_powers.pow_1_l, rings.M3, pow_nonneg in *; intuition.
    Qed.

    Theorem order_one : order 1 = 1%N.
    Proof.
      apply naturals.le_antisymm; apply INZ_le.
      - apply div_le, div_order; try apply zero_lt_1;
          try apply unit_classification, one_unit.
        now rewrite rings.pow_1_r.
      - apply lt_0_le_1, order_pos, unit_classification, one_unit.
    Qed.

    Theorem order_upper_bound : ∀ a : Z_, a ∈ 𝐔_ → (order a ≤ Euler_Phi)%N.
    Proof.
      intros a H.
      apply INZ_le, div_le.
      - apply INZ_lt, nonzero_lt, Euler_Phi_nonzero.
      - apply div_order, Euler; now rewrite <-? unit_classification.
    Qed.

    Theorem mul_order : ∀ a b : Z_,
        a ∈ 𝐔_ → b ∈ 𝐔_ →
        gcd(order a, order b) = 1 → order (a * b) = (order a * order b)%N.
    Proof.
      intros a b H H0 H1.
      apply unit_classification in H as H2, H0 as H3.
      apply assoc_N, conj; fold divide.
      - apply div_order.
        + now apply unit_classification, unit_closure.
        + now rewrite rings.pow_mul_l, rings.pow_mul_r, mul_comm,
          rings.pow_mul_r, ? order_pow, ? rings.pow_1_l, M3.
      - rewrite <-INZ_mul.
        apply rel_prime_mul; auto.
        + eapply FTA; eauto.
          rewrite INZ_mul.
          apply div_order; auto.
          rewrite <-(M3 (a^(order b * order (a * b)))), M1,
          <-(rings.pow_1_l ℤ_ _ : 1^(order (a * b)) = 1), <-(order_pow b),
          <-rings.pow_mul_r, <-(rings.pow_mul_l ℤ_ a b), mul_comm,
          rings.pow_mul_r, order_pow, rings.pow_1_l at 1; auto.
          now apply unit_classification, unit_closure.
        + apply is_gcd_sym in H1.
          eapply FTA; eauto.
          rewrite INZ_mul.
          apply div_order; auto.
          rewrite <-(M3 (b^(order a * order (a *b)))), M1,
          <-(rings.pow_1_l ℤ_ _ : 1^(order (a * b )) = 1), <-(order_pow a),
          <-rings.pow_mul_r, <-(rings.pow_mul_l ℤ_ b a), M1, mul_comm,
          rings.pow_mul_r, order_pow, rings.pow_1_l at 1; auto.
          now apply unit_classification, unit_closure.
    Qed.

    Theorem pow_order :
      ∀ (k : N) (a : Z_), a ∈ 𝐔_ → order a / gcd k (order a) = order (a^k).
    Proof.
      intros k a H.
      assert (gcd k (order a) ≠ 0) as Z.
      { rewrite gcd_sym.
        apply gcd_pos.
        intros H0.
        apply INZ_eq in H0.
        contradict H0.
        now apply nonzero_lt, INZ_lt, order_pos. }
      assert (0 ≤ order a / gcd k (order a)) as H0.
      { apply div_nonneg.
        - now apply or_introl, order_pos.
        - destruct (gcd_nonneg k (order a)) as [H0 | H0]; auto.
          rewrite gcd_sym in H0.
          apply eq_sym, gcd_pos in H0; intuition.
          apply order_pos in H.
          rewrite H1 in H.
          contradiction (lt_irrefl ℤ_order 0). }
      apply unit_classification in H as H1.
      assert ((a^k)%Zn ∈ 𝐔_) as H2.
      { now apply unit_classification, (unit_prod_closure ℤ_). }
      apply pm_pos; auto.
      2: { now apply or_introl, order_pos. }
      apply assoc_pm, conj; fold divide.
      - apply inv_div_l; auto using gcd_r_div.
        assert (0 ≤ gcd k (order a)) as H3 by now apply gcd_nonneg.
        apply le_def in H3 as [c H3].
        rewrite integers.A3 in H3.
        rewrite H3, INZ_mul.
        apply div_order; auto.
        destruct (Euclidean_gcd k (order a)) as [x [y H4]].
        rewrite <-pow_nonneg, <-INZ_mul, <-H3, <-H4, integers.D1,
        integer_powers.pow_add_r, <-integers.M2, integer_powers.pow_mul_r,
        integers.M1, integer_powers.pow_mul_r, ? pow_nonneg, order_pow,
        integer_powers.pow_1_l, M1, <-integers.M2, integer_powers.pow_mul_r,
        ? pow_nonneg, order_pow, integer_powers.pow_1_l, M3 in *; auto.
        rewrite pow_nonneg.
        now apply unit_prod_closure.
      - apply le_def in H0 as [c H3].
        rewrite integers.A3 in H3.
        rewrite H3.
        apply div_order; auto.
        rewrite <-? pow_nonneg, <-H3, <-integer_powers.pow_mul_r, mul_div,
        integers.M1, <-mul_div, integer_powers.pow_mul_r, pow_nonneg, order_pow,
        integer_powers.pow_1_l in *; auto using gcd_r_div, gcd_l_div.
    Qed.

    Theorem order_lcm_closed : ∀ a b : Z_,
        a ∈ 𝐔_ → b ∈ 𝐔_ → ∃ c : Z_, c ∈ 𝐔_ ∧ lcm (order a) (order b) = order c.
    Proof.
      intros a b.
      remember ((order a) * (order b))%N as m.
      revert m a b Heqm.
      induction m using Strong_Induction.
      intros a b Heqm H0 H1.
      apply (order_pos a) in H0 as H2.
      apply lt_0_le_1 in H2 as [H2 | H2]; subst.
      2: { exists b.
           rewrite <-H2, lcm_l_1; auto.
           left; now apply order_pos. }
      apply exists_prime_divisor in H2 as [p [H2 [H3 H4]]].
      set (k := v p (order a)).
      set (l := v p (order b)).
      assert (0 < order a / p^k) as H5; assert (0 < order b / p^l) as H6;
        eauto using val_quot_positive, order_pos.
      assert (0 < p^k) as H7; assert (0 < p^l) as H8;
        try now apply (ordered_rings.pow_pos ℤ_order).
      assert ((order a / p^k) * (order b / p^l) < order a * order b) as H9.
      { apply (lt_le_cross_mul ℤ_order); simpl; try apply val_quot_bound;
            try apply quot_le_bound; eauto using order_pos, val_div. }
      apply lt_def in H5 as [x [H5 H10]], H6 as [y [H6 H11]], H7
            as [z [H7 H12]], H8 as [w [H8 H13]].
      rewrite integers.A3, H10, H11, ? INZ_mul, INZ_lt in *.
      unfold k, l in H10, H11, H12, H13.
      pose proof H10 as H14.
      pose proof H11 as H15.
      rewrite <-gcd_val in H10, H11; try apply (pos_ne_0 ℤ_order), order_pos;
        try (rewrite H12, pow_order in H10; rewrite H13, pow_order in H11);
        auto; apply INZ_eq in H10, H11.
      rewrite <-H10, <-H11 in H9.
      eapply H in H9 as [c [H9 H16]]; try reflexivity;
        try now (rewrite unit_classification in *;
                 try now apply unit_prod_closure).
      rewrite H10, H11, <-H14, <-H15 in H16.
      destruct (le_trichotomy k l) as [H17 | H17].
      - erewrite <-val_lcm_l; eauto using order_pos.
        assert (order (b^y) = w) as H18.
        { rewrite <-INZ_eq, <-pow_order, <-H13, <-H15, div_l_gcd; auto.
          - rewrite div_div; auto using val_div, prime_power_nonzero.
            now apply (pos_ne_0 ℤ_order), order_pos.
          - rewrite H15.
            apply INZ_le, zero_le.
          - exists (p^l)%Z; simpl.
            apply eq_sym, div_inv_l; auto using val_div. }
        assert ((b^y)%Zn ∈ 𝐔_) as H19.
        { rewrite unit_classification in *.
          now apply unit_prod_closure. }
        exists (b^y * c).
        rewrite H16, H13, <-H18, mul_order, INZ_mul; auto.
        + rewrite unit_classification in *.
          split; auto; now apply unit_closure.
        + rewrite <-H16, H18, <-H13.
          apply val_lcm_l_rel_prime; auto using order_pos.
      - erewrite <-val_lcm_r; eauto using order_pos.
        assert (order (a^x) = z) as H18.
        { rewrite <-INZ_eq, <-pow_order, <-H12, <-H14, div_l_gcd; auto.
          - rewrite div_div; auto using val_div, prime_power_nonzero.
            now apply (pos_ne_0 ℤ_order), order_pos.
          - rewrite H14.
            apply INZ_le, zero_le.
          - exists (p^k)%Z; simpl.
            apply eq_sym, div_inv_l; auto using val_div. }
        assert ((a^x)%Zn ∈ 𝐔_) as H19.
        { rewrite unit_classification in *.
          now apply unit_prod_closure. }
        exists (a^x * c).
        rewrite H16, H12, <-H18, mul_order, INZ_mul; auto.
        + rewrite unit_classification in *.
          split; auto; now apply unit_closure.
        + rewrite <-H16, H18, <-H12.
          apply val_lcm_r_rel_prime; auto using order_pos.
    Qed.

    Definition max_order : N.
    Proof.
      pose proof (lub (λ x, ∃ a : Z_, a ∈ 𝐔_ ∧ order a = x)) as H.
      apply constructive_indefinite_description in H as [x [H H0]].
      - exact x.
      - exists 1%N, 1.
        rewrite unit_classification.
        split; auto using order_one; apply one_unit.
      - exists Euler_Phi.
        intros n0 [a [H0 H1]].
        rewrite <-H1.
        now apply order_upper_bound.
    Defined.

    Theorem max_order_ex : ∃ a : Z_, a ∈ 𝐔_ ∧ order a = max_order.
    Proof.
      unfold max_order.
      destruct constructive_indefinite_description as [x [[a H] H0]].
      eauto.
    Qed.

    Theorem max_order_bound : ∀ a : Z_, a ∈ 𝐔_ → (order a ≤ max_order)%N.
    Proof.
      intros a H.
      unfold max_order.
      destruct constructive_indefinite_description as [x [[b H0] H1]].
      eauto.
    Qed.

    Theorem max_order_div : ∀ a : Z_, a ∈ 𝐔_ → order a｜max_order.
    Proof.
      intros a H.
      destruct max_order_ex as [b [H0 H1]], (order_lcm_closed a b)
          as [c [H2 H3]]; auto.
      rewrite H1 in H3.
      replace (order c) with max_order in H3.
      - rewrite <-H3.
        apply lcm_div_l.
      - apply naturals.le_antisymm.
        + rewrite <-INZ_le, <-H3.
          now apply lcm_bound, order_pos.
        + auto using max_order_bound.
    Qed.

    Theorem max_order_pow : ∀ a : Z_, a ∈ 𝐔_ → a^max_order = 1.
    Proof.
      intros a H.
      apply div_order; auto using max_order_div.
    Qed.

  End Positive_modulus.

  Definition square (a : Z_) := a * a.

  Definition square_function := sets.functionify square.

  Definition QR := {x of type 𝐙_ | @rings.unit ℤ_ x ∧ ∃ a, square a = x}.
  Definition QNR := {x of type 𝐙_ | @rings.unit ℤ_ x ∧ (x : Z_) ∉ QR}.

  Definition legendre_symbol (a : Z_) : Z.
  Proof.
    destruct (excluded_middle_informative (a ∈ QR)).
    - exact 1.
    - destruct (excluded_middle_informative (a ∈ QNR)).
      + exact (-(1%Z))%Z.
      + exact 0.
  Defined.

  Theorem legendre_square : ∀ a, @rings.unit ℤ_ a → legendre_symbol (a * a) = 1.
  Proof.
    intros a H.
    unfold legendre_symbol.
    destruct excluded_middle_informative; auto.
    contradiction n0.
    apply Specify_classification.
    rewrite despecify.
    unfold square.
    eauto using elts_in_set, (unit_closure ℤ_).
  Qed.

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

    Lemma nonzero_unit : ∀ a : Z_, a ≠ 0 → @rings.unit ℤ_ a.
    Proof.
      intros a H.
      apply units_in_ℤ_, is_gcd_sym, prime_rel_prime; auto.
      contradict H.
      now rewrite eqm_div_n, <-IZn_eq, <-Zproj_eq in H.
    Qed.

    Definition inv : Z_ → Z_.
    Proof.
      intros a.
      destruct (excluded_middle_informative (a = 0)).
      - exact 0.
      - apply nonzero_unit in n0.
        destruct (constructive_indefinite_description n0) as [x H].
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
      rewrite despecify.
      eauto using elts_in_set.
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
          rewrite (reify H0), despecify in *;
          replace (exist H0 : Z_) with (0 : Z_) in *
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
           eauto using elts_in_set. }
      apply f_equal, Extensionality.
      split; intros H; destruct prime_modulus as [H0 H1].
      - apply Specify_classification in H as [H H2].
        rewrite (reify H), despecify, Complement_classification,
        Singleton_classification in *.
        split; auto.
        intros H3.
        apply set_proj_injective in H3.
        destruct H2 as [_ [_ H2]].
        contradict H0.
        apply H2; eauto using (divide_refl ℤ) with Z.
        now rewrite eqm_div_n, H3, <-Zlift_equiv.
      - apply Complement_classification in H as [H H2].
        apply Specify_classification.
        split; auto.
        rewrite (reify H), despecify, Singleton_classification in *.
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
      rewrite (reify H), despecify in *.
      split; eauto.
      now apply units_in_ℤ_.
    Qed.

    Theorem QNR_QR_c : QNR = Euler_Phi_set \ QR.
    Proof.
      apply Extensionality.
      split; intros H.
      - apply Specify_classification in H as [H H0].
        rewrite (reify H), despecify, Complement_classification in *.
        split; try tauto.
        apply Specify_classification.
        rewrite despecify.
        split; auto.
        now apply units_in_ℤ_.
      - apply Complement_classification in H as [H H0].
        apply Specify_classification in H as [H H1].
        apply Specify_classification.
        rewrite (reify H), despecify in *.
        repeat split; auto.
        now apply units_in_ℤ_.
    Qed.

    Definition unit_square_function := restriction square_function 𝐔_.

    Lemma domain_usf : domain unit_square_function = 𝐔_.
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
        @sets.functionify_domain, @sets.functionify_range in *;
          try now rewrite sets.functionify_domain in *.
        apply Pairwise_intersection_classification in H0 as [H0 H2].
        apply Specify_classification.
        rewrite (reify H), (reify H2), @functionify_action, despecify in *.
        apply set_proj_injective in H1.
        repeat split; eauto.
        apply Specify_classification in H0 as [H0 H3].
        rewrite despecify, <-H1 in *.
        now apply unit_closure.
      - apply Specify_classification.
        rewrite restriction_domain, restriction_range,
        sets.functionify_domain, sets.functionify_range.
        apply Specify_classification in H as [H H0].
        rewrite (reify H), despecify in *.
        destruct H0 as [[x H0] [a H1]].
        split; eauto.
        exists a.
        enough (a ∈ 𝐔_ ∩ 𝐙_).
        { now rewrite <-restriction_action, @functionify_action, H1;
            try now rewrite sets.functionify_domain. }
        rewrite Pairwise_intersection_classification.
        split; eauto using elts_in_set.
        apply Specify_classification.
        split; eauto using elts_in_set.
        rewrite despecify, <-H1 in *.
        exists (x * a).
        now rewrite H0, <-M2.
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
        unfold square_function, square in *.
        rewrite sets.functionify_domain in H4.
        assert (z ∈ 𝐔_) as H5.
        { apply Specify_classification.
          split; auto.
          apply Specify_classification in H as [H H5].
          rewrite (reify H4), (reify H), despecify in *.
          destruct H5 as [[y H5] [a H6]].
          apply Inverse_image_classification in H2; auto.
          rewrite sets.functionify_action in H2.
          apply set_proj_injective in H2.
          rewrite <-H2 in H5.
          exists (y * (exist H4)).
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
      apply (subsets_of_finites_are_finite _ 𝐙_); auto using finite_Z_mod.
      intros x H.
      now apply Specify_classification in H.
    Qed.

    Theorem Fpow_wf : ∀ (a : Z_) k, rings.pow ℤ_ a k = (fields.pow 𝔽 a k).
    Proof.
      intros a k.
      now rewrite <-pow_wf.
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

    Theorem max_order_full : (max_order positive_prime) = Euler_Phi.
    Proof.
      set (d := max_order positive_prime).
      assert (1 ≤ d)%N as O.
      { destruct (max_order_ex positive_prime) as [x [H H0]]; unfold d.
        rewrite <-H0.
        now apply INZ_le, lt_0_le_1, order_pos. }
      apply naturals.le_antisymm.
      - destruct (max_order_ex positive_prime) as [x [H H0]]; unfold d.
        rewrite <-H0.
        now apply order_upper_bound.
      - rewrite <-(cyclotomic_degree ℤ_ Z_mod_prime_is_ID d (1 : Z_)); auto.
        eapply naturals.le_trans; try apply root_degree_bound;
          auto using Z_mod_prime_is_ID.
        2: { apply monic_nonzero, cyclotomic_monic;
             auto using Z_mod_prime_is_ID. }
        unfold Euler_Phi.
        rewrite Euler_Phi_unit.
        apply INZ_le, or_intror, INZ_eq, f_equal, Extensionality.
        split; intros H.
        + assert (z ∈ 𝐙_) as H0.
          { now apply Specify_classification in H. }
          set (ζ := exist H0 : Z_).
          replace z with (ζ : set) in * by auto.
          apply unit_classification in H as H1.
          apply Specify_classification.
          split; eauto using elts_in_set.
          rewrite despecify.
          unfold rings.sub.
          rewrite eval_add, eval_neg, eval_const, eval_x_to_n; simpl.
          replace (ζ^d) with (1 : Z_); auto using A4.
          now apply eq_sym, max_order_pow.
        + apply Specify_classification in H as [H H0].
          assert (z ∈ 𝐙_) as H1 by easy.
          set (ζ := exist H1 : Z_).
          replace z with (ζ : set) in * by auto.
          rewrite despecify in H0.
          unfold rings.sub in H0.
          rewrite eval_add, eval_neg, eval_const, eval_x_to_n in H0;
            simpl in H0.
          apply unit_classification.
          exists (ζ^(d-1)).
          rewrite <-(rings.pow_1_r ℤ_ ζ) at 2.
          rewrite <-(rings.pow_add_r ℤ_), add_comm, sub_abab,
          <-(rings.A3_r ℤ_ (ζ^d)); simpl; auto.
          now rewrite <-(A4 1), (A1 1), A2, H0, A3.
    Qed.

    Theorem Gauss_primroot :
      ∃ c : Z_, c ∈ 𝐔_ ∧ (p - 1)%Z = order positive_prime c.
    Proof.
      destruct (max_order_ex positive_prime) as [x [H H0]].
      exists x.
      split; auto.
      now rewrite H0, max_order_full, Prime_Euler_Phi_Z.
    Qed.

  End Prime_modulus.

  Section Odd_prime_modulus.

    Notation p := n.
    Hypothesis prime_modulus : prime p.
    Hypothesis odd_prime : p > 2.

    Theorem odd_prime_positive : 0 < p.
    Proof.
      eapply integers.lt_trans; eauto using (zero_lt_2 ℤ_order : 0 < 2).
    Qed.

    Theorem one_ne_minus_one : (1 : Z_) ≠ ((-1%Z)%Z : Z_).
    Proof.
      intros H.
      apply IZn_eq, eqm_sym in H.
      unfold eqm in H.
      replace (1--1%Z)%Z with (2%Z) in H by ring.
      now apply div_le, le_not_gt in H; try apply (zero_lt_2 ℤ_order).
    Qed.

    Theorem two_nonzero : (2 : Z_) ≠ 0.
    Proof.
      intros H.
      rewrite <-(A4 1), <-IZn_add, IZn_neg in H.
      apply (rings.cancellation_add ℤ_) in H.
      contradiction one_ne_minus_one.
    Qed.

    Theorem number_of_square_roots : ∀ x : Z_,
        x ∈ QR → (inverse_image_of_element square_function x ~ 2%N)%set.
    Proof.
      intros x H.
      apply Specify_classification in H as [H H0].
      rewrite despecify in *.
      destruct H0 as [H0 [a H1]].
      replace (inverse_image_of_element square_function x) with {a, -a}.
      { apply pairing_card.
        intros H2.
        destruct (surjective_mod_n_on_interval odd_prime_positive a)
          as [a' [[[H3 H4] H5] H6]].
        subst.
        apply set_proj_injective, eq_sym in H2.
        rewrite Zproj_eq, (Zproj_eq a'), IZn_neg in H2 at 1.
        apply IZn_eq in H2.
        rewrite <-? Zlift_equiv in H2.
        unfold eqm, integers.sub in H2.
        replace (--a')%Z with (a') in * by now ring_simplify.
        rewrite <-(integers.M3 a'), <-integers.D1 in H2.
        apply Euclid's_lemma in H2 as [H2 | H2]; auto.
        - now apply div_le, le_not_gt in H2; try apply (zero_lt_2 ℤ_order).
        - apply (integral_domains.unit_nonzero (ℤ_ID prime_modulus)) in H0.
          contradict H0; simpl.
          unfold square.
          now rewrite eqm_div_n, <-IZn_eq, H2, (mul_0_r ℤ_) in *. }
      apply Extensionality.
      unfold square_function.
      assert ({a,-a} ⊂ 𝐙_) as H2.
      { intros z H2.
        apply Pairing_classification in H2 as [H2 | H2];
          subst; eauto using elts_in_set. }
      split; intros H3; unfold square in *.
      - rewrite Inverse_image_classification in *;
          rewrite ? sets.functionify_domain, ? sets.functionify_range; auto.
        apply Pairing_classification in H3 as [H3 | H3]; subst;
          rewrite @functionify_action; auto; now rewrite (rings.mul_neg_neg ℤ_).
      - apply Inverse_image_subset in H3 as H4;
          rewrite ? @sets.functionify_range, ? @sets.functionify_domain in *;
          auto; rewrite Inverse_image_classification, (reify H4),
                @functionify_action in *; rewrite ? sets.functionify_domain,
                                         ? sets.functionify_range; auto.
        subst.
        apply set_proj_injective in H3.
        pose proof difference_of_squares ℤ_ (exist H4) a as H1; simpl in H1.
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
      rewrite (reify H1).
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
      now rewrite size_of_QR, size_QR_QNR.
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
    Notation "- 1" := (rings.neg ℤ_p_x 1) : poly_scope.
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
      rewrite despecify in H0.
      destruct H0 as [H0 [x H1]].
      subst.
      unfold square.
      rewrite <-(rings.pow_2_r ℤ_), <-(rings.pow_mul_r ℤ_), <-size_of_QR.
      auto using Euler, unit_square, odd_prime_positive.
    Qed.

    Theorem roots_QR : roots _ (x^(# QR) - 1)%poly = QR.
    Proof.
      assert (QR ⊂ roots ℤ_ (x ^ (# QR) + -1%poly)%poly) as S.
      { intros x H.
        apply Specify_classification; simpl Rset.
        pose proof H as H0.
        apply Specify_classification in H0 as [H0 H1].
        rewrite (reify H0), despecify in *.
        destruct H1 as [H1 [a H2]].
        split; auto.
        rewrite eval_add, eval_neg, IRP_1, eval_const, eval_x_to_n,
        Euler_Criterion_QR, A4; auto. }
      assert ((x ^ (# QR) + -1%poly)%poly ≠ 0%poly) as N.
      { apply nonzero_coefficients.
        exists 0%N.
        rewrite coefficient_add, coefficient_neg, coeffs_of_x_ne_n, IRP_1,
        coeff_const, rings.A3, rings.neg_0; intros H.
        - rewrite <-(neg_0 ℤ_) in H;
            contradiction (integral_domains.minus_one_nonzero
                             (ℤ_ID prime_modulus)).
        - contradiction Euler_Phi_nonzero; auto using odd_prime_positive.
          rewrite size_of_QR, <-H.
          ring. }
      assert (degree _ (x^(# QR) + -1%poly)%poly = # QR) as D.
      { apply naturals.le_antisymm.
        - rewrite <-max_0_r.
          eapply naturals.le_trans; eauto using (add_degree ℤ_).
          exists 0%N.
          rewrite add_0_r.
          f_equal.
          + apply degree_x_to_n; now destruct Z_mod_prime_is_ID.
          + apply const_classification.
            exists (-1%Zn).
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
             apply Specify_classification; rewrite (reify H), despecify in *;
             split; auto; now rewrite <-units_in_ℤ_.
           - apply Specify_classification in H as [H H0].
             apply Pairwise_union_classification.
             destruct (classic (z ∈ QR)); auto.
             apply or_intror, Specify_classification.
             now rewrite (reify H), despecify, units_in_ℤ_ in *. }
      replace Euler_Phi_set with
          ((roots _ (x^(# QR) - 1)%poly) ∪ (roots _ (x^(# QR) + 1)%poly)) in E.
      2: { rewrite <-prod_root, <-difference_of_squares, <-rings.pow_mul_l,
           <-rings.pow_2_r, <-rings.pow_mul_r, <-size_of_QR, rings.M3,
           rings.sub_is_neg; auto using Z_mod_prime_is_ID.
           apply Extensionality.
           split; intros H.
           - apply Specify_classification in H as [H H0]; simpl Rset in H.
             apply Specify_classification.
             rewrite (reify H), despecify, <-units_in_ℤ_ in *.
             split; auto.
             rewrite eval_add, eval_neg, IRP_1, eval_const, eval_x_to_n,
             <-(rings.A4 ℤ_ (1:Z_)), ? (rings.A1 ℤ_ _ (-(1:Z_))) in H0;
               simpl in *.
             apply (cancellation_add ℤ_) in H0.
             eapply unit_pow_closure; try rewrite H0; try apply one_unit.
             pose proof Euler_Phi_nonzero odd_prime_positive.
             apply succ_0 in H1 as [m H1].
             rewrite H1.
             apply naturals.lt_succ.
           - apply Specify_classification in H as [H H0].
             apply Specify_classification; simpl Rset.
             rewrite (reify H), despecify, <-units_in_ℤ_, eval_add, eval_neg,
             IRP_1, eval_const, eval_x_to_n, Euler, A4 in *; repeat split;
               auto using odd_prime_positive. }
      apply Euler_Phi_lemma in E; auto using roots_QR.
      { apply NNPP.
        intros H.
        apply Nonempty_classification in H as [x H].
        apply Pairwise_intersection_classification in H as [H H0].
        apply Specify_classification in H0 as [H0 H1].
        now rewrite (reify H0), despecify in *. }
      apply NNPP.
      intros H.
      apply Nonempty_classification in H as [z H].
      apply Pairwise_intersection_classification in H as [H H0].
      apply Specify_classification in H as [H H1], H0 as [H0 H2].
      rewrite (reify H), despecify, <-H2, rings.sub_is_neg,
      ? eval_add, ? eval_neg, ? IRP_1, ? eval_const, ? eval_x_to_n in *.
      apply (rings.cancellation_add ℤ_) in H1; simpl in H1.
      contradiction one_ne_minus_one.
      now rewrite <-H1, IZn_neg.
    Qed.

    Theorem Euler_Criterion_QNR :
      ∀ a : Z_, a ∈ QNR → a^(# QR) = ((-1%Z) : Z_)%Z.
    Proof.
      intros a H.
      rewrite <-roots_QNR in H.
      apply Specify_classification in H as [H H0]; simpl Rset in *.
      rewrite (reify H), despecify, eval_add, IRP_1, eval_const, eval_x_to_n,
      (A1 _ 1), <-(rings.A4 ℤ_ (1:Z_)) in H0.
      apply (rings.cancellation_add ℤ_) in H0; simpl in H0.
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
      - exfalso; eauto using QR_QNR_0.
    Qed.

    Definition trinary_value (a : Z) := a = 0 ∨ a = 1 ∨ a = (-1%Z)%Z.

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

    Theorem trinary_pow_neg_1_l : ∀ k, trinary_value ((-1)^k)%Z.
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
        + destruct (constructive_indefinite_description H) as [q H0].
          exact q.
        + apply odd_prime_positive.
      - exact 0.
    Defined.

    Definition QR_r (l : N) : Z.
    Proof.
      destruct (excluded_middle_informative (0 < a * l)%Z) as [H | H].
      - apply (division_QR (a*l)%Z p) in H.
        + destruct (constructive_indefinite_description H) as [q H0].
          destruct (constructive_indefinite_description H0) as [r H1].
          exact r.
        + apply odd_prime_positive.
      - exact 0.
    Defined.

    Definition QR_ε (l : N) := rationals.QR_ε (2*a*l)%Z p.

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
        now rewrite (integers.M1 x p), <-integers.M2.
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
        apply (mul_denom_l ℚ_order); try apply IZQ_lt, (zero_lt_2 ℤ_order).
        rewrite IZQ_mul.
        apply IZQ_lt.
        unfold integers.one.
        rewrite (D1_l ℤ), ? INZ_add, ? INZ_mul, add_1_r, <-size_of_QR,
        <-Prime_Euler_Phi_Z, <-add_1_r, <-INZ_mul, <-INZ_add;
          auto using odd_prime_positive.
        fold integers.one; apply (ordered_rings.lt_shift ℤ_order); simpl.
        replace (p - 1 + 2 * 1 + - p)%Z with 1%Z by ring.
        auto using integers.zero_lt_1.
      - split; apply INZ_le; eauto using naturals.le_refl, zero_le.
    Qed.

    Definition QR_r_N : N → N.
    Proof.
      intros l.
      destruct (QR_r_bound l) as [H H0].
      apply le_def in H.
      destruct (constructive_indefinite_description H) as [r H1].
      exact r.
    Defined.

    Lemma QR_r_N_action : ∀ l, QR_r l = QR_r_N l.
    Proof.
      intros l.
      unfold QR_r_N.
      destruct QR_r_bound, constructive_indefinite_description.
      now rewrite integers.A3 in e.
    Qed.

    Definition QR_r_function := sets.functionify QR_r_N.

    Lemma QR_lt_p : ¬ p ≤ # QR.
    Proof.
      apply lt_not_ge, lt_def.
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
        apply div_add; fold divide; apply div_mul_l;
          auto using div_refl, (div_0_r ℤ). }
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
      rewrite (reify H0), despecify in *.
      unfold QR_r_function, QR_r_N in *.
      rewrite @sets.functionify_domain, @sets.functionify_range,
      ? @functionify_action in *.
      destruct QR_r_bound, constructive_indefinite_description as [z'].
      rewrite integers.A3 in e.
      subst.
      apply Specify_classification.
      rewrite despecify.
      repeat split; try apply INZ_le; destruct e; auto using QR_r_nonzero.
    Qed.

    Definition QR_r_res := restriction_Y QR_r_restriction_construction.

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
      unfold QR_r_res, QR_r_function.
      enough (i ∈ {x of type ω | (1 ≤ x ≤ # QR)%N} ∧
              i ∈ domain (sets.functionify QR_r_N)).
      - rewrite <-Pairwise_intersection_classification, @restriction_Y_action,
        <-restriction_action, @functionify_action in *; auto.
      - split.
        + apply Specify_classification.
          rewrite despecify.
          split; eauto using elts_in_set.
        + rewrite sets.functionify_domain.
          eauto using elts_in_set.
    Qed.

    Lemma range_constraint : ∀ i j,
        1 ≤ i ≤ # QR → 1 ≤ j ≤ # QR → (i : Z_) = (j : Z_) → i = j.
    Proof.
      intros i j [H H0] [H1 H2] H3.
      apply injective_mod_n_on_interval; try (now apply IZn_eq); split.
      - eapply (ordered_rings.le_trans ℤ_order); eauto.
        apply or_introl, zero_lt_1.
      - eapply (ordered_rings.le_lt_trans ℤ_order); eauto.
        apply lt_not_ge, QR_lt_p.
      - eapply (ordered_rings.le_trans ℤ_order); eauto.
        apply or_introl, zero_lt_1.
      - eapply (ordered_rings.le_lt_trans ℤ_order); eauto.
        apply lt_not_ge, QR_lt_p.
    Qed.

    Lemma range_constraint_neg : ∀ i j,
        1 ≤ i ≤ # QR → 1 ≤ j ≤ # QR → (i : Z_) ≠ -(j : Z_).
    Proof.
      intros i j [H H0] [H1 H2] H3.
      assert ((i+j : Z_) = (0 : Z_))%Z as H4.
      { now rewrite <-IZn_add, H3, A1, A4. }
      apply IZn_eq, injective_mod_n_on_interval in H4.
      - contradiction (ordered_rings.lt_irrefl ℤ_order 0); simpl.
        rewrite <-H4 at 2.
        apply (ordered_rings.O0 ℤ_order); simpl; now apply lt_0_le_1.
      - split.
        + apply or_introl, (ordered_rings.O0 ℤ_order); now apply lt_0_le_1.
        + eapply (ordered_rings.le_lt_trans ℤ_order);
            try (eapply le_cross_add; eauto).
          rewrite <-(integers.M3 (# QR)), <-integers.D1,
          <-size_of_QR_in_Z, lt_def.
          exists 1%N.
          split.
          * intros H5.
            now apply INZ_eq, PA4 in H5.
          * fold integers.one.
            ring.
      - split; auto using odd_prime_positive; apply le_refl.
    Qed.

    Theorem QR_r_res_bijective : bijective QR_r_res.
    Proof.
      pose proof QR_r_res_domain as Q.
      unfold QR_r_res in Q.
      rewrite restriction_Y_domain in Q.
      apply finite_set_injection_is_bijection; try rewrite QR_r_res_domain;
        unfold QR_r_res in *.
      { apply (subsets_of_finites_are_finite _ (S (# QR)));
          auto using naturals_are_finite.
        intros x H.
        apply Specify_classification in H as [H H0].
        rewrite (reify H), despecify in *.
        destruct H0 as [H0 H1].
        now apply lt_is_in, le_lt_succ. }
      { now rewrite restriction_Y_range. }
      apply Injective_classification.
      intros x y H H0 H1.
      rewrite @restriction_Y_domain, ? @restriction_Y_action,
      @restriction_domain, <-? restriction_action, Q in *; try congruence.
      clear Q.
      unfold QR_r_function, QR_r_N in *.
      apply Specify_classification in H as [H H2], H0 as [H0 H3].
      set (ξ := exist H : N).
      set (γ := exist H0 : N).
      rewrite (reify H), (reify H0), despecify, ? @sets.functionify_action in *.
      fold ξ γ in H1, H2, H3 |-*.
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
      apply iterate_bijection; auto using M1, M2.
      - intros j H.
        exists (QR_r_N j).
        apply QR_r_nonzero in H.
        pose proof (QR_r_bound j) as [H0 H1].
        repeat split; try apply INZ_le; rewrite <-? QR_r_N_action; auto.
        intros x' [[H2 H3] H4].
        rewrite <-INZ_eq, <-QR_r_N_action.
        apply IZn_eq, injective_mod_n_on_interval in H4; repeat split; auto;
          try (now apply or_introl, lt_0_le_1, INZ_le);
          [ apply INZ_le in H3 | ]; eapply (ordered_rings.le_lt_trans ℤ_order);
            eauto; apply lt_not_ge, QR_lt_p.
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
          unfold QR_r_res.
          rewrite inverse_domain, restriction_Y_range;
            auto using QR_r_res_bijective.
          apply Specify_classification.
          rewrite despecify.
          eauto using elts_in_set. }
        set (η := exist H0 : N).
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
              rewrite despecify.
              eauto using elts_in_set. }
            unfold QR_r_res in H1.
            rewrite inverse_range, restriction_Y_domain in H1;
              auto using QR_r_res_bijective.
            apply Pairwise_intersection_classification in H1 as [H1 H2].
            apply Specify_classification in H1.
            now rewrite despecify in H1. }
          split; auto.
          rewrite QR_r_N_action.
          apply f_equal, f_equal, set_proj_injective.
          rewrite <-QR_r_res_action; auto.
          simpl.
          rewrite right_inverse;
            try rewrite inverse_domain, ? restriction_Y_range;
            auto using QR_r_res_bijective.
          apply Specify_classification.
          rewrite despecify.
          eauto using elts_in_set.
        + intros x' [H1 H2].
          apply range_constraint in H2.
          2: { split; apply INZ_le; intuition. }
          2: { split; auto using QR_r_nonzero.
               now destruct (QR_r_bound x'). }
          rewrite QR_r_N_action in H2.
          apply INZ_eq, (f_equal INS) in H2.
          apply set_proj_injective.
          simpl.
          rewrite H2, <-QR_r_res_action, left_inverse;
            auto using QR_r_res_bijective.
          unfold QR_r_res, QR_r_function.
          rewrite restriction_Y_domain.
          apply Pairwise_intersection_classification.
          split.
          * apply Specify_classification.
            rewrite despecify.
            eauto using elts_in_set.
          * rewrite sets.functionify_domain.
            eauto using elts_in_set.
    Qed.

    Theorem Gauss's_Lemma :
      legendre_symbol a = ((-1%Z)^sum_N (λ l, QR_ε_exp (2*a*l)%Z p) 1 (# QR))%Z.
    Proof.
      apply trinary_IZn_eq; auto using trinary_legendre, trinary_pow_neg_1_l.
      rewrite <-IZn_pow, <-IZn_neg.
      apply (cancellation_mul_r (ℤ_ID prime_modulus)
                                (prod ℤ_ (λ n : N, QR_r n : Z_) 1 (# QR)));
        rewrite <-Gauss_Lemma_helper at 1; simpl.
      - apply (integral_domains.unit_nonzero (ℤ_ID prime_modulus)),
        unit_prod_closure.
        intros i [H H0].
        apply nonzero_unit; auto.
        intros H1.
        apply IZn_eq, eqm_sym in H1.
        unfold eqm in H1.
        ring_simplify in H1.
        apply div_le in H1; try now apply lt_0_le_1, INZ_le.
        apply INZ_le in H0.
        eapply QR_lt_p, (ordered_rings.le_trans ℤ_order); eauto.
      - rewrite <-Euler's_Criterion, <-(sub_abab 1 (# QR)), add_comm, add_1_r,
        (prod_mul ℤ_) at 1; auto using size_QR_ge_1; simpl.
        replace (λ n : N, a * n) with (λ l : N, (QR_ε l * QR_r l)).
        + unfold QR_ε, rationals.QR_ε.
          rewrite prod_dist, <-? Gauss_Lemma_helper, <-prod_sum; simpl.
          repeat f_equal.
          extensionality k.
          now rewrite <-IZn_pow, <-IZn_neg.
        + extensionality l.
          now rewrite ? IZn_mul, modified_division_algorithm, <-? IZn_add,
          <-? IZn_mul, modulus_zero, (mul_0_r ℤ_), A3.
    Qed.

  End Odd_prime_modulus.

  Section Gauss_Lemma_helper.

    Variable a : N.
    Notation p := n.
    Hypothesis prime_modulus : prime p.
    Hypothesis odd_prime : p > 2.
    Hypothesis a_odd : odd a.
    Hypothesis p_ndiv_a : ¬ p｜a.
    Hypothesis a_positive : 0 < a.

    Theorem p_odd : odd p.
    Proof.
      intros H.
      clear p_ndiv_a.
      apply prime_modulus in H as [H | H].
      - apply unit_pm_1 in H as [H | H].
        + rewrite <-(integers.A3 1) in H at 3.
          rewrite (integers.A1 0) in H.
          apply (cancellation_add ℤ) in H.
          now contradiction integers.zero_ne_1.
        + rewrite <-(integers.A3 (-1%Z)), (integers.A1 0), <-(integers.A3 2),
          <-(integers.A4 1%Z), (integers.A1 1), <-integers.A2 in H at 1.
          apply (cancellation_add ℤ), eq_sym in H.
          contradiction (lt_irrefl ℤ_order (1+2))%Z.
          rewrite <-H at 1.
          apply (ordered_rings.O0 ℤ_order); simpl; auto using zero_lt_1.
          apply (zero_lt_2 ℤ_order).
      - apply assoc_pm, pm_sym in H as [H | H]; subst.
        + contradiction (lt_irrefl ℤ_order 2).
        + apply (lt_not_ge ℤ_order) in odd_prime.
          contradict odd_prime.
          left; simpl.
          rewrite (lt_shift ℤ_order); simpl.
          replace (--(2))%Z with 2 by ring.
          apply (ordered_rings.O0 ℤ_order); apply zero_lt_2.
    Qed.

    Lemma modified_Gauss_Lemma_helper :
      legendre_symbol (2*a)%Z =
      ((-1)^sum_N id 1 (#QR)*(-1)^sum_N (λ l, QR_ε_exp (a*l) p) 1 (#QR))%Z.
    Proof.
      eapply odd_add in a_odd as [k H]; try apply p_odd; simpl in *.
      rewrite <-IZn_mul, <-(A3 (2*a)), A1, <-(mul_0_r ℤ_ (2 : Z_) : (2*0 = 0)),
      <-modulus_zero, ? IZn_mul, IZn_add, <-(rings.D1_l ℤ), (integers.A1 _ p),
      H, (integers.M1 k), integers.M2, <-IZn_mul, legendre_mult, <-IZn_mul,
      legendre_square, integers.M3; auto.
      2: { apply nonzero_unit; auto using prime_modulus, two_nonzero. }
      assert (0 ≤ k) as H0.
      { rewrite (le_not_gt ℤ_order); simpl.
        intros H0.
        apply (O3 ℤ_order 2) in H0; simpl in *;
          try now apply (ordered_rings.zero_lt_2 ℤ_order).
        rewrite integers.M1, <-H, (lt_not_ge ℤ_order), (mul_0_r ℤ) in H0;
          fold integers.le in *; simpl in *.
        contradict H0.
        apply (add_nonneg_nonneg ℤ_order); fold integers.le; simpl.
        - left; now apply odd_prime_positive.
        - apply INZ_le, zero_le. }
      apply le_def in H0 as [k' H0].
      rewrite integers.A3 in H0.
      subst.
      rewrite Gauss's_Lemma; auto.
      2: { intros H0.
           contradict p_ndiv_a.
           apply (f_equal (λ x : Z, (x : Z_))), IZn_eq in H.
           rewrite eqm_div_n, H0 in *.
           rewrite eqn_zero in H at 2.
           now rewrite integers.A3, (mul_0_l ℤ) in H. }
      rewrite <-(rings.pow_add_r ℤ), <-sum_N_dist, (integers.M1 2), <-H.
      repeat f_equal.
      extensionality l.
      unfold id, QR_ε_exp.
      repeat destruct excluded_middle_informative;
        try (contradict n0; now apply odd_prime_positive);
        try (contradict n1; now apply odd_prime_positive).
      - repeat destruct constructive_indefinite_description.
        rewrite integers.A3 in e, e0.
        apply INZ_eq.
        rewrite <-INZ_add, <-e, <-e0, <-floor_add_int.
        f_equal.
        assert (p ≠ 0) as H0.
        { intros H0.
          contradiction (ordered_rings.lt_irrefl ℤ_order 0).
          rewrite <-H0 at 2.
          now apply odd_prime_positive. }
        rewrite inv_div, <-IZQ_mul, <-IZQ_add, ? rationals.D1, (rationals.M1 p),
        <-rationals.M2, (inv_r ℚ), rationals.M1, rationals.M3, inv_div, IZQ_mul;
          auto.
        contradict H0.
        now apply IZQ_eq.
      - contradict n0.
        apply integers.O2; auto.
        destruct (classic (l = 0%N)) as [H0 | H0];
          try apply succ_0 in H0 as [m H0]; subst.
        + rewrite (mul_0_r ℤ) in l0.
          contradiction (lt_irrefl ℤ_order 0).
        + apply INZ_lt, naturals.lt_succ.
      - contradict n0.
        apply integers.O2.
        + apply (ordered_rings.O0 ℤ_order); auto.
        + destruct (classic (l = 0%N)) as [H0 | H0];
            try apply succ_0 in H0 as [m H0]; subst.
          * rewrite (mul_0_r ℤ) in l0.
            contradiction (lt_irrefl ℤ_order 0).
          * apply INZ_lt, naturals.lt_succ.
      - destruct (classic (l = 0%N)) as [H0 | H0];
          try apply succ_0 in H0 as [m H0]; subst; try ring.
        contradict n1.
        apply integers.O2; auto.
        apply INZ_lt, naturals.lt_succ.
    Qed.

  End Gauss_Lemma_helper.

  Section Modified_Gauss's_Lemma.

    Variable a : N.
    Notation p := n.
    Hypothesis prime_modulus : prime p.
    Hypothesis odd_prime : p > 2.
    Hypothesis a_odd : odd a.
    Hypothesis p_ndiv_a : ¬ p｜a.
    Hypothesis a_positive : 0 < a.

    Theorem Gauss's_Lemma_2 : (legendre_symbol 2 = (-1)^sum_N id 1 (#QR))%Z.
    Proof.
      rewrite <-(integers.M3 2), <-integers.M1.
      unfold integers.one at 3.
      rewrite modified_Gauss_Lemma_helper; auto using integers.zero_lt_1.
      2: { apply odd_classification.
           exists 0.
           now rewrite (mul_0_r ℤ), integers.A3. }
      2: { destruct prime_modulus as [H H0].
           now contradict H. }
      rewrite <-(integers.M3 ((- 1) ^ sum_N id 1 (# QR)))%Z at 2.
      rewrite (integers.M1 1).
      replace 1 with ((-1)^0)%Z at 4 by now rewrite (rings.pow_0_r ℤ).
      repeat f_equal.
      rewrite <-(iterated_ops.sum_of_0_a_b 1 (# QR)).
      apply iterate_extensionality.
      intros k [H H0].
      unfold QR_ε_exp.
      repeat destruct excluded_middle_informative; auto.
      destruct constructive_indefinite_description.
      rewrite integers.M3, integers.A3 in e.
      apply INZ_eq.
      rewrite <-e.
      apply INZ_le in H, H0.
      apply (ordered_rings.le_antisymm ℤ_order); fold integers.le.
      - apply IZQ_le, floor_lower.
        rewrite rationals.A3, inv_div; auto using (pos_ne_0 ℤ_order).
        apply (mul_denom_l ℚ_order); simpl.
        + now apply IZQ_lt.
        + rewrite rationals.M1, rationals.M3.
          apply IZQ_lt.
          eapply (ordered_rings.le_lt_trans ℤ_order); eauto; simpl.
          now apply (lt_not_ge ℤ_order), (QR_lt_p).
      - apply IZQ_le, floor_upper.
        rewrite inv_div; auto using (pos_ne_0 ℤ_order).
        apply or_introl, ordered_rings.O2; simpl.
        + now apply IZQ_lt, lt_0_le_1.
        + now apply (ordered_fields.inv_lt ℚ_order), IZQ_lt.
    Qed.

    Theorem Gauss's_Lemma_a :
      (legendre_symbol a = (-1)^sum_N (λ l, QR_ε_exp (a*l) p) 1 (#QR))%Z.
    Proof.
      apply modified_Gauss_Lemma_helper in a_positive as H; auto.
      rewrite <-IZn_mul, legendre_mult, Gauss's_Lemma_2 in H; auto.
      apply (integral_domains.cancellation_mul_l integers.ℤ_ID) in H; auto.
      destruct (pow_neg_1_l ℤ (sum_N id 1 (# QR))) as [H0 | H0]; simpl in H0;
        rewrite H0.
      - apply (integral_domains.nontriviality integers.ℤ_ID).
      - apply (integral_domains.minus_one_nonzero integers.ℤ_ID).
    Qed.

  End Modified_Gauss's_Lemma.

End Modular_arithmetic.

Notation "a 'mod' p" := (Z_to_Z_n p a) (at level 45) : Z_scope.
Arguments Gauss's_Lemma_a {n}.
Arguments trinary_legendre {n}.
Arguments Euler {n}.
Arguments legendre_square {n}.
Arguments legendre_symbol {n}.
Arguments legendre_mult {n}.
Arguments nonzero_unit {n}.
Arguments Euler's_Criterion {n}.
Arguments Gauss's_Lemma {n}.

Theorem mod_0_r : ∀ a, modulo 0 a = 0.
Proof.
  intros a.
  unfold modulo.
  destruct excluded_middle_informative; auto.
  exfalso.
  contradiction (ordered_rings.lt_irrefl ℤ_order 0).
Qed.

Theorem mod_1_r : ∀ a, modulo 1 a = 0.
Proof.
  intros a.
  unfold modulo.
  destruct excluded_middle_informative; auto.
  repeat destruct constructive_indefinite_description.
  destruct a0 as [H [[H0 | H0] H1]]; auto.
  contradiction (lt_0_1 x0).
Qed.
