Set Warnings "-ambiguous-paths".
Require Export ssreflect ssrbool ssrfun rings integers.

Section Integer_powers.

  Variable Ring : rings.ring.
  Notation R := (elts Ring).
  Declare Scope Ring_scope.
  Delimit Scope Ring_scope with R.
  Open Scope Ring_scope.
  Bind Scope Ring_scope with R.
  Notation "0" := (rings.zero Ring) : Ring_scope.
  Notation "1" := (rings.one Ring) : Ring_scope.
  Infix "+" := (rings.add Ring) : Ring_scope.
  Infix "-" := (rings.sub Ring) : Ring_scope.
  Infix "*" := (rings.mul Ring) : Ring_scope.
  Infix "**" := (rings.pow Ring) (at level 35) : Ring_scope.
  Notation "- a" := (rings.neg Ring a) : Ring_scope.
  Notation "- 1" := (rings.neg Ring 1) : Ring_scope.

  Add Ring generic_ring : (ringify Ring).

  Definition inv (a : R) : R.
  Proof.
    case (excluded_middle_informative (rings.unit a)) =>
           [/constructive_indefinite_description [x H] | H].
    - exact (x : R).
    - exact 0.
  Defined.

  Theorem inv_l : ∀ a, rings.unit a → (inv a) * a = 1.
  Proof.
    rewrite /inv => a H.
    case excluded_middle_informative => [{} H | ] //.
    elim constructive_indefinite_description => //.
  Qed.

  Theorem inv_r : ∀ a, rings.unit a → a * (inv a) = 1.
  Proof.
    move: rings.M1 => /[swap] a /[swap] /inv_l <- -> //.
  Qed.

  Theorem inv_1 : inv 1 = 1.
  Proof.
    rewrite /inv.
    (case excluded_middle_informative => [H | []]);
    [elim constructive_indefinite_description => x -> | exists 1]; ring.
  Qed.

  Theorem inv_neg_1 : inv (-1) = -1.
  Proof.
    rewrite /inv.
    (case excluded_middle_informative => [H | []]);
    [elim constructive_indefinite_description => x -> | exists (-1)]; ring.
  Qed.

  Theorem inv_inv : ∀ a, rings.unit a → inv (inv a) = a.
  Proof.
    rewrite /inv => a H.
    ((repeat elim excluded_middle_informative) =>
     [{}H | {}H | {}H | ] //; elim constructive_indefinite_description) =>
    [x H0 H1 | x H0 []].
    - elim constructive_indefinite_description => y.
      move: H0 (rings.M1 _ y x) => /[swap] -> -> /unit_cancel -> //.
    - esplit.
      rewrite H0 rings.M1 //.
  Qed.

  Theorem unit_inv : ∀ a, rings.unit a → rings.unit (inv a).
  Proof.
    eexists.
    by erewrite inv_r.
  Qed.

  Theorem inv_mul :
    ∀ a b, rings.unit a → rings.unit b → inv (a * b) = inv a * inv b.
  Proof.
    rewrite /inv => a b H H0.
    ((repeat elim excluded_middle_informative) =>
     H1 H2 H3; repeat elim constructive_indefinite_description; try tauto) =>
    [x H4 y H5 z /(f_equal (rings.mul _ (x*y))) | x H4 y H5].
    - suff -> : x * y * (z * (a * b)) =  z * (x * b) * (y * a); last by ring.
      rewrite -? H4 -? H5 ? M3_r rings.M1 => -> //.
    - move: H H0 H3 => /unit_closure /[apply] //.
  Qed.

  Theorem inv_unique : ∀ a b, a * b = 1 → b = inv a.
  Proof.
    move=> a b.
    case (classic (rings.unit a)) =>
    [/[dup] H /(unit_cancel _ a b (inv a)) /[swap] -> -> | /[swap] H []] //.
    - rewrite inv_r //.
    - esplit.
      rewrite -H rings.M1 //.
  Qed.

  Definition pow (a : R) (n : Z) : R.
  Proof.
    case (excluded_middle_informative (0 ≤ n)) =>
           [/le_def /constructive_indefinite_description [c H] | ].
    - exact (a ** c).
    - case (excluded_middle_informative (rings.unit a)) =>
      [H /lt_not_ge /lt_shift | H H0] /=.
      + rewrite A3 => /lt_def /constructive_indefinite_description [c H0].
        exact ((inv a)**c).
      + exact 0%R.
  Defined.

  Infix "^" := pow : Ring_scope.

  Theorem pow_nonneg : ∀ (a : R) (n : N), a ^ n = a ** n.
  Proof.
    rewrite /pow => a n.
    case excluded_middle_informative => [H | []].
    - elim constructive_indefinite_description => x.
      rewrite A3 => /INZ_eq -> //.
    - apply /INZ_le /zero_le.
  Qed.

  Theorem pow_0_r : ∀ a, a ^ 0 = 1.
  Proof.
    rewrite /zero => a.
    rewrite pow_nonneg pow_0_r //.
  Qed.

  Theorem pow_0_l : ∀ a : Z, a ≠ 0%Z → 0 ^ a = 0.
  Proof.
    move: classic => /[swap] a /(_ (0 ≤ a)) =>
    [[[/lt_def [c [/[swap] ->]] | ->] | H H0]] //.
    - rewrite INZ_eq A3 => /neq_sym /succ_0 [m ->] /INZ_eq H.
      rewrite pow_nonneg pow_0_l //.
    - rewrite /pow.
      (repeat case excluded_middle_informative; try tauto) => [[x H1]] *.
      apply zero_ring_degeneracy.
      rewrite H1 mul_0_r //.
  Qed.

  Theorem pow_1_r : ∀ a, a ^ 1 = a.
  Proof.
    rewrite /one => a.
    rewrite pow_nonneg pow_1_r //.
  Qed.

  Theorem pow_1_l : ∀ a, 1 ^ a = 1.
  Proof.
    rewrite /pow /eq_rect_r /eq_rect /eq_sym => a.
    (case excluded_middle_informative; auto) => H.
    - elim constructive_indefinite_description => x H0.
      rewrite pow_1_l //.
    - case excluded_middle_informative => [H0 | []]; auto using one_unit => /=.
      destruct A3.
      elim constructive_indefinite_description => x [H1 H2].
      rewrite inv_1 pow_1_l //.
   Qed.

  Theorem pow_neg : ∀ a b, rings.unit a → a ^ (-b) = (inv a) ^ b.
  Proof.
    rewrite /pow /eq_rect_r /eq_rect /eq_sym => a b H.
    ((((repeat case excluded_middle_informative; try tauto) => H0 H1) =>
     [| H2 | H2 | H2 | H2 H3 | H2 H3];
     repeat elim constructive_indefinite_description) =>
     [x | x | x | x | | ]; rewrite ? A3) =>
    [H2 | | | | |]; (try by (contradict H0; exists a; rewrite inv_r));
      try destruct A3; try elim constructive_indefinite_description => y [H3].
    - move: H2 H1 H0 -> => /le_neg_0 /le_antisymm /[apply] /INZ_eq -> y.
      rewrite A3 -(neg_0 ℤ_order: 0%Z = (-0)%Z) => /INZ_eq <-.
      rewrite ? rings.pow_0_r //.
    - rewrite ? A3 inv_inv // /INZ_eq => -> /INZ_eq -> //.
    - rewrite ? A3 (neg_neg ℤ b: --b = b)%Z => -> /INZ_eq -> //.
    - contradict H3.
      move: H1 => /lt_not_ge /lt_neg_0 /or_introl => /(_ (0 = -b))%Z //.
  Qed.

  Theorem inv_pow : ∀ a, rings.unit a → a ^ (-1) = inv a.
  Proof.
    move: pow_1_r => /[swap] a /[swap] /pow_neg -> -> //.
  Qed.

  Theorem unit_pow : ∀ a b, rings.unit a → rings.unit (a ^ b).
  Proof.
    rewrite /pow /eq_rect_r /eq_rect /eq_sym => a b H.
    repeat (case excluded_middle_informative)
    => * //; try destruct A3; elim constructive_indefinite_description
    => *; apply unit_prod_closure; auto using unit_inv.
  Qed.

  Theorem pow_mul_l :
    ∀ a b c, rings.unit a → rings.unit b → (a * b) ^ c = a ^ c * b ^ c.
  Proof.
    move=> a b c H H0.
    case (classic (0 ≤ c)) =>
    [/le_def [m ->] | /lt_not_ge /lt_shift /lt_def [m [H1]] /=].
    - rewrite A3 ? pow_nonneg pow_mul_l //.
    - rewrite -{2 3 4}(neg_neg ℤ c) ? A3 /= => ->.
      rewrite ? pow_neg ? pow_nonneg ? inv_mul ? pow_mul_l;
              auto using unit_closure, unit_inv.
  Qed.

  Theorem neg_pow : ∀ a b, rings.unit a → a ^ (-b) = inv (a ^ b).
  Proof.
    move: classic => /[swap] a /[swap] b /(_ (b = 0%Z)) => [[-> | H]] H0.
    - rewrite -(neg_0 ℤ: 0 = -0)%Z pow_0_r inv_1 //.
    - apply inv_unique.
      rewrite pow_neg -? pow_mul_l ? inv_r ? pow_1_l; auto using unit_inv.
  Qed.

  Theorem pow_mul_r : ∀ a b c, rings.unit a → a ^ (b * c) = (a ^ b) ^ c.
  Proof.
    move=> a b c H.
    wlog: a c H / (0 ≤ c)%Z => [pow_mul_r_pos | H0].
    - case (classic (0 ≤ c)) => [H0 | /lt_not_ge /lt_neg_0 /lt_def [d [H0 /=]]].
      + by rewrite pow_mul_r_pos.
      + rewrite A3 -{2 3}(neg_neg ℤ c: --c = c)%Z => ->.
        suff -> : (b*-d = -(b*d))%Z; last by ring.
        rewrite ? pow_neg ? pow_mul_r_pos ? pow_neg -? neg_pow ? pow_neg;
          auto using unit_inv, unit_pow.
        apply /INZ_le /zero_le.
    - rewrite {2}/pow.
      case excluded_middle_informative => [{}H0 | H1]; last by contradict H1.
      elim constructive_indefinite_description => x ->.
      case (classic (0 ≤ b)) =>
      [/le_def [d] | /lt_not_ge /lt_neg_0 /lt_def [d [H1 /=]]].
      + rewrite ? A3 => ->.
        rewrite INZ_mul ? pow_nonneg pow_mul_r //.
      + rewrite ? A3 -{2 3}(neg_neg ℤ b: --b = b)%Z
                           (mul_neg_l ℤ (-b)%Z (x:Z) : --b*x = -(-b*x))%Z => ->.
        rewrite ? pow_neg ? INZ_mul ? pow_nonneg ? pow_mul_r //.
  Qed.

  Theorem pow_div_distr : ∀ a b c,
      rings.unit a → rings.unit b → (a * (inv b)) ^ c = a ^ c * inv (b ^ c).
  Proof.
    move=> a b c H H0.
    rewrite pow_mul_l -? neg_pow ? pow_neg; auto using unit_inv.
  Qed.

  Lemma pow_add_r_opp : ∀ a b, rings.unit a → a^b * a^(-b) = 1.
  Proof.
    move=> a b H.
    rewrite pow_neg -? pow_mul_l ? inv_r ? pow_1_l;
      auto using unit_pow, unit_inv.
  Qed.

  Theorem pow_add_r : ∀ a b c, rings.unit a → a ^ (b + c) = a ^ b * a ^ c.
  Proof.
    move=> a b c H.
    wlog: a b c H / 0 ≤ b => [pow_add_r_pos | ].
    - case (classic (0 ≤ b)), (classic (0 ≤ c)); auto.
      + rewrite A1 rings.M1.
        apply pow_add_r_pos; auto.
      + rewrite -1 ? (neg_neg ℤ b: --b = b)%Z -1 ? (neg_neg ℤ c: --c = c)%Z.
        suff -> : (--b + --c = -(-b + -c))%Z; last by ring.
        rewrite ? (pow_neg a); auto.
        apply pow_add_r_pos; auto using unit_inv.
        move: H0 => /lt_not_ge /lt_neg_0 /or_introl => /(_ (0 = -b))%Z //.
    - case (le_sym ℤ_order 0%Z c).
      + move => /le_def [y ->] /le_def [x ->].
          by rewrite ? A3 INZ_add ? pow_nonneg pow_add_r.
      + move=> /[swap] /le_def [x ->] /(le_neg_0 ℤ_order) /le_def /= [y].
        rewrite -(rings.M3 _ (a^(0+x+c)))
        -(pow_add_r_opp a c) // -? rings.M2 rings.M1 ? pow_nonneg ? A3
        -{3 4 5}(neg_neg ℤ c: --c = c)%Z => ->; f_equal.
        case (classic (0 ≤ x+-y)) =>
        [/le_def [z] | /lt_not_ge /lt_neg_0 /lt_def [z [H2 /=]]].
        * rewrite A3 => /[dup] H0 ->.
          rewrite ? pow_nonneg -pow_add_r.
          apply f_equal, INZ_eq.
          rewrite -INZ_add -H0; ring.
        * suff {2}-> : (x + - y = --(x+-y))%Z; last by ring.
          rewrite A3 => /[dup] H0 ->.
          rewrite pow_neg // -(M3_r _ (a^x)) -(pow_1_l z) -(inv_r a) //.
          rewrite pow_div_distr // rings.M2 -neg_pow ? pow_neg ? pow_nonneg //.
          suff -> : (y = x + z)%N; first by rewrite pow_add_r.
          rewrite -INZ_eq -INZ_add -H0; ring.
  Qed.

End Integer_powers.
