Require Export integers Setoid.

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

Section Modular_arithmetic.
  Variable n : Z.

  Add Parametric Relation : Z (eqm n)
      reflexivity proved by (eqm_refl n)
      symmetry proved by (eqm_sym n)
      transitivity proved by (eqm_trans n) as Z_mod_n.

  Add Morphism add with signature (eqm n) ==> (eqm n) ==> (eqm n) as Z_add_mod.
  Proof.
    intros x y H x0 y0 H0.
    unfold eqm in *.
    replace (y+y0-(x+x0)) with ((y-x)+(y0-x0)) by ring.
    now apply div_add.
  Qed.

  Add Morphism mul with signature (eqm n) ==> (eqm n) ==> (eqm n) as Z_mul_mod.
  Proof.
    intros x y H x0 y0 H0.
    apply (eqm_trans n _ (y*x0)); unfold eqm in *.
    - replace (y*x0-x*x0) with ((y-x)*x0) by ring.
      now apply div_mul_r.
    - replace (y*y0-y*x0) with (y*(y0-x0)) by ring.
      now apply div_mul_l.
  Qed.

  Add Morphism neg with signature (eqm n) ==> (eqm n) as Z_neg_mod.
  Proof.
    intros x y H.
    unfold eqm in *.
    replace (-y--x) with ((-(1))*(y-x)) by ring.
    now apply div_mul_l.
  Qed.

  Add Morphism sub with signature (eqm n) ==> (eqm n) ==> (eqm n) as Z_sub_mod.
  Proof.
    intros x y H x0 y0 H0.
    unfold sub.
    now rewrite H, H0.
  Qed.

  Add Morphism (rings.pow integers)
      with signature (eqm n) ==> (eq) ==> (eqm n) as Z_pow_mod.
  Proof.
    intros x y H k.
    induction k using Induction.
    - now rewrite ? pow_0_r.
    - now rewrite ? pow_succ_r, IHk, H.
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
    now rewrite (mul_0_l integers), A3.
  Qed.

End Modular_arithmetic.

Infix "mod" := modulo (at level 45) : Z_scope.
