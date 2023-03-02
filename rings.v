Require Export iterated_ops Ring.
Set Warnings "-notation-bound-to-variable,-notation-overridden".
Set Warnings "-ambiguous-paths,-uniform-inheritance".

Record ring :=
  mkRing {
      Rset :> set;
      zero : elts Rset where "0" := zero;
      one : elts Rset where "1" := one;
      add : elts Rset → elts Rset → elts Rset where "a + b" := (add a b);
      mul : elts Rset → elts Rset → elts Rset where "a * b" := (mul a b);
      neg : elts Rset → elts Rset where "- a" := (neg a);
      A3 : ∀ a, 0 + a = a;
      A1 : ∀ a b, a + b = b + a;
      A2 : ∀ a b c, a + (b + c) = (a + b) + c;
      M3 : ∀ a, 1 * a = a;
      M1 : ∀ a b, a * b = b * a;
      M2 : ∀ a b c, a * (b * c) = (a * b) * c;
      D1 : ∀ a b c, (a + b) * c = a * c + b * c;
      A4 : ∀ a, a + (-a) = 0;
    }.

Section Ring_theorems.

  Variable Ring : ring.
  Notation R := (elts Ring).
  Declare Scope Ring_scope.
  Delimit Scope Ring_scope with ring.
  Open Scope Ring_scope.
  Bind Scope Ring_scope with R.
  Notation "0" := (zero Ring) : Ring_scope.
  Notation "1" := (one Ring) : Ring_scope.
  Infix "+" := (add Ring) : Ring_scope.
  Infix "*" := (mul Ring) : Ring_scope.
  Notation "- a" := (neg Ring a) : Ring_scope.
  Notation "- 1" := (neg Ring 1) : Ring_scope.

  Definition IRS (a : R) := elt_to_set a : set.

  Global Coercion IRS : R >-> set.

  Definition sub (a b : R) := a + (-b) : R.

  Infix "-" := sub : Ring_scope.

  Lemma sub_is_neg : ∀ a b, a - b = a + -b.
  Proof.
    auto.
  Qed.

  Definition ringify :=
    (mk_rt 0 1 (add _) (mul _) sub (neg _) eq (A3 _) (A1 _) (A2 _)
           (M3 _) (M1 _) (M2 _) (D1 _) sub_is_neg (A4 _)).
  Add Ring generic_ring : ringify.

  Theorem mul_0_r : ∀ a, a * 0 = 0.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem mul_neg_1_l : ∀ a, (-1) * a = -a.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem mul_neg_1_r : ∀ a, a * (-1) = -a.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem mul_neg_neg : ∀ a b, (-a) * (-b) = a * b.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem mul_neg_l : ∀ a b, (-a) * b = - (a * b).
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem mul_neg_r : ∀ a b, a * (-b) = - (a * b).
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem neg_0 : 0 = -0.
  Proof.
    ring.
  Qed.

  Theorem mul_0_l : ∀ a, 0 * a = 0.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem A3_r : ∀ a, a + 0 = a.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem A4_l : ∀ a, -a + a = 0.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem M3_r : ∀ a, a * 1 = a.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem D1_l : ∀ a b c, a * (b + c) = a * b + a * c.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem D1_minus_l : ∀ a b c, a * (b - c) = a * b - a * c.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem D1_minus_r : ∀ a b c, (a - b) * c = a * c - b * c.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem neg_neg : ∀ a, --a = a.
  Proof.
    move=> *.
    ring.
  Qed.

  Theorem difference_of_squares : ∀ a b, a * a - b * b = (a - b) * (a + b).
  Proof.
    move=> *.
    ring.
  Qed.

  Definition divide x y := ∃ z, y = z * x.

  Notation "x ｜ y" :=
    (divide x y) (at level 60, format "x '｜' y") : Ring_scope.

  Theorem div_mul_r : ∀ a b c, a｜b → a｜b*c.
  Proof.
    move=> a b c [d H].
    exists (d*c).
    ring [H].
  Qed.

  Theorem div_mul_l : ∀ a b c, a｜c → a｜b*c.
  Proof.
    move=> a b c [d H].
    exists (d*b).
    ring [H].
  Qed.

  Theorem div_add : ∀ a b c, a｜b → a｜c → a｜b+c.
  Proof.
    move=> a b c [x H] [y H0].
    exists (x+y).
    ring [H H0].
  Qed.

  Theorem div_mul_add : ∀ a m n x y, a｜m → a｜n → a｜m*x + n*y.
  Proof.
    auto using div_add, div_mul_r.
  Qed.

  Theorem div_0_r : ∀ a, a｜0.
  Proof.
    exists 0.
    ring.
  Qed.

  Theorem div_0_l : ∀ a, 0｜a ↔ a = 0.
  Proof.
    split => [[? H] | H]; [ | exists 0 ]; ring [H].
  Qed.

  Theorem div_refl : ∀ a, a｜a.
  Proof.
    exists 1.
    ring.
  Qed.
  Definition divide_refl := div_refl.

  Theorem div_trans : ∀ a b c, a｜b → b｜c → a｜c.
  Proof.
    move=> a b c [x H] [y H0].
    exists (x*y).
    ring [H H0].
  Qed.

  Theorem div_1_l : ∀ a, 1｜a.
  Proof.
    move=> a.
    exists a.
    ring.
  Qed.

  Theorem div_sign_r : ∀ a b, a｜b ↔ a｜-b.
  Proof.
    split => [[x H] | [x H]]; exists (-x); ring [H].
  Qed.

  Theorem div_sign_neg_r : ∀ a b, a｜-b → a｜b.
  Proof.
    move=> *.
    rewrite div_sign_r //.
  Qed.

  Theorem div_sign_r_neg : ∀ a b, a｜b → a｜-b.
  Proof.
    move=> *.
    rewrite -div_sign_r //.
  Qed.

  Theorem div_sign_l : ∀ a b, a｜b ↔ -a｜b.
  Proof.
    split => [[x H] | [x H]]; exists (-x); ring [H].
  Qed.

  Theorem div_sign_neg_l : ∀ a b, -a｜b → a｜b.
  Proof.
    move=> *.
    rewrite div_sign_l //.
  Qed.

  Theorem div_sign_l_neg : ∀ a b, a｜b → -a｜b.
  Proof.
    move=> a b H.
    rewrite -div_sign_l //.
  Qed.

  Definition assoc a b := a｜b ∧ b｜a.
  Infix "~" := assoc (at level 70) : Ring_scope.
  Definition unit a := a｜1.

  Theorem assoc_refl : ∀ a, a ~ a.
  Proof.
    split; eauto using div_refl.
  Qed.

  Theorem assoc_sym : ∀ a b, a ~ b → b ~ a.
  Proof.
    move=> ? ? [? ?] //.
  Qed.

  Theorem assoc_sym_iff : ∀ a b, a ~ b ↔ b ~ a.
  Proof.
    split => [[] | []] //.
  Qed.

  Theorem assoc_trans : ∀ a b c, a ~ b → b ~ c → a ~ c.
  Proof.
    move=> ? ? ? [? ?] [? ?].
    split; eapply div_trans; eauto.
  Qed.

  Add Parametric Relation : (elts Ring) assoc
      reflexivity proved by (assoc_refl)
      symmetry proved by (assoc_sym)
      transitivity proved by (assoc_trans) as assoc_equivalence.

  Theorem assoc_zero : ∀ a, a ~ 0 ↔ a = 0.
  Proof.
    split => [[? /div_0_l] | ->]; auto using assoc_refl.
  Qed.

  Theorem assoc_sign : ∀ a b, a ~ b → a ~ -b.
  Proof.
    move=> ? ? [].
    split; auto using div_sign_l_neg, div_sign_r_neg.
  Qed.

  Theorem unit_closure : ∀ a b, unit a → unit b → unit (a * b).
  Proof.
    move=> a b [x H] [y H0].
    exists (x*y).
    rewrite -(M3 _ 1) {1}H H0 -M2 (M2 _ a) (M1 _ a) ? M2 //.
  Qed.

  Theorem unit_square : ∀ u, unit (u * u) → unit u.
  Proof.
    move=> u [x H].
    exists (x*u).
    rewrite H M2 //.
  Qed.

  Theorem unit_sign : ∀ a, unit a ↔ unit (-a).
  Proof.
    split; rewrite /unit -div_sign_l //.
  Qed.

  Theorem unit_sign_r : ∀ a, unit a → unit (-a).
  Proof.
    move=> *.
    apply /div_sign_l_neg => //.
  Qed.

  Theorem one_unit : unit 1.
  Proof.
    apply /div_refl.
  Qed.

  Theorem neg_one_unit : unit (-1).
  Proof.
    apply /unit_sign_r /one_unit.
  Qed.

  Theorem unit_cancel : ∀ a b c, unit a → a * b = a * c → b = c.
  Proof.
    move=> a b c [x H] H0.
    rewrite -(M3 _ b) H -M2 H0 M2 -H M3 //.
  Qed.

  Theorem cancellation_0_add : ∀ a b, a + b = 0 → b = -a.
  Proof.
    move=> a b H.
    rewrite -(A3 _ (-a)) -H -A2 A1 -A2 A4_l A3_r //.
  Qed.

  Theorem cancellation_add : ∀ a b c, a + b = a + c → b = c.
  Proof.
    move=> a b c H.
    rewrite -(A3 _ b) -(A4 _ a) (A1 _ a) -A2 H A2 A4_l A3 //.
  Qed.

  Theorem cancellation_add_r : ∀ a b c, b + a = c + a → b = c.
  Proof.
    move=> a b c.
    rewrite -? (A1 _ a) => /cancellation_add //.
  Qed.

  Lemma cancellation_ne0 : ∀ a b, a * b ≠ 0 → a ≠ 0 ∧ b ≠ 0.
  Proof.
    split; move: H => /[swap] ->; rewrite ? mul_0_l ? mul_0_r //.
  Qed.

  Definition sum f a b := iterate_with_bounds (add _) f 0 a b.
  Definition prod f a b := iterate_with_bounds (mul _) f 1 a b.

  Theorem sum_0 : ∀ f a, sum f a a = f a.
  Proof.
    move=> *.
    rewrite /sum iterate_0 //.
  Qed.

  Theorem sum_neg : ∀ f a b, b < a → sum f a b = 0.
  Proof.
    move=> f a b H.
    rewrite /sum ? iterate_neg //.
  Qed.

  Theorem sum_succ : ∀ f a b,
      a ≤ S b → (sum f a (S b)) = (sum f a b) + (f (S b)).
  Proof.
    move=> f a b H.
    apply /iterate_succ_lower_limit; auto; ring.
  Qed.

  Theorem prod_0 : ∀ f a, prod f a a = f a.
  Proof.
    move=> *.
    rewrite /prod iterate_0 //.
  Qed.

  Theorem prod_neg : ∀ f a b, b < a → prod f a b = 1.
  Proof.
    move=> f a b H.
    rewrite /prod ? iterate_neg //.
  Qed.

  Theorem prod_succ : ∀ f a b,
      a ≤ S b → (prod f a (S b)) = (prod f a b) * (f (S b)).
  Proof.
    move=> f a b H.
    apply /iterate_succ_lower_limit; auto; ring.
  Qed.

  Theorem sum_dist :
    ∀ f g a b, sum (λ n, (f n) + (g n)) a b = sum f a b + sum g a b.
  Proof.
    move=> f g a b.
    elim (classic (a ≤ b)) => [[c <-] | /lt_not_ge H].
    - induction c using Induction;
        rewrite ? add_0_r ? sum_0 ? add_succ_r ? sum_succ ? IHc; try ring;
          eauto using le_trans, le_add, le_succ.
    - rewrite ? sum_neg ? A3 //.
  Qed.

  Theorem sum_mul : ∀ f a b c, c * sum f a b = sum (λ n, c * (f n)) a b.
  Proof.
    move=> f a b c.
    elim (classic (a ≤ b)) => [[d <-] | /lt_not_ge H].
    - induction d using Induction;
        rewrite ? add_0_r ? sum_0 ? add_succ_r ? sum_succ ? D1_l ? IHd //;
                eauto using le_trans, le_add, le_succ.
    - rewrite ? sum_neg ? mul_0_r //.
  Qed.

  Theorem prod_dist :
    ∀ f g a b, prod (λ n, (f n) * (g n)) a b = prod f a b * prod g a b.
  Proof.
    move=> f g a b.
    elim (classic (a ≤ b)) => [[c <-] | /lt_not_ge H].
    - induction c using Induction;
        rewrite ? add_0_r ? prod_0 ? add_succ_r ? prod_succ ? IHc; try ring;
          eauto using le_trans, le_add, le_succ.
    - rewrite ? prod_neg ? M3 //.
  Qed.

  Theorem sum_of_0 : ∀ d, (sum (λ n, 0) 0 d) = 0.
  Proof.
    induction d using Induction;
      rewrite ? sum_0 ? sum_succ ? IHd; auto using zero_le; ring.
  Qed.

  Theorem prod_of_1 : ∀ d, (prod (λ n, 1) 0 d) = 1.
  Proof.
    induction d using Induction;
      rewrite ? prod_0 ? prod_succ ? IHd; auto using zero_le; ring.
  Qed.

  Theorem unit_prod_closure_0 :
    ∀ n f, (∀ i, 0 ≤ i ≤ n → unit (f i)) → unit (prod f 0 n).
  Proof.
    induction n using Induction =>
    f H; rewrite ? prod_0 ? prod_succ; try apply unit_closure; try apply IHn;
      intuition eauto using le_refl, zero_le, le_trans, le_succ.
  Qed.

  Theorem unit_prod_closure :
    ∀ a b f, (∀ i, a ≤ i ≤ b → unit (f i)) → unit (prod f a b).
  Proof.
    move=> a b f.
    elim (classic (a ≤ b)%N) => [[c <-] H | /lt_not_ge H0].
    - rewrite /prod iterate_shift.
      apply /unit_prod_closure_0 => i H0.
      apply H.
      rewrite -{1}(add_0_l a) (add_comm a).
      intuition eauto using O1_le.
    - rewrite prod_neg; auto using one_unit.
  Qed.

  Definition pow a n := prod (λ x, a) 1 n.

  Infix "^" := pow : Ring_scope.

  Theorem pow_0_r : ∀ x, x^0 = 1.
  Proof.
    move=> *.
    rewrite /pow prod_neg; eauto using lt_succ.
  Qed.

  Theorem pow_succ_r : ∀ x y, x^(S y) = x^y * x.
  Proof.
    move=> *.
    rewrite /pow prod_succ; auto using one_le_succ.
  Qed.

  Theorem pow_1_r : ∀ x, x^1 = x.
  Proof.
    move=> *.
    rewrite /naturals.one pow_succ_r pow_0_r M3 //.
  Qed.

  Theorem pow_1_l : ∀ x, 1^x = 1.
  Proof.
    induction x using Induction; rewrite ? pow_0_r ? pow_succ_r ? IHx ? M3 //.
  Qed.

  Theorem pow_0_l : ∀ x, x ≠ 0%N → 0^x = 0.
  Proof.
    induction x using Induction => H //.
    rewrite pow_succ_r mul_0_r //.
  Qed.

  Theorem pow_2_r : ∀ x, x^2 = x * x.
  Proof.
    move=> *.
    rewrite pow_succ_r pow_1_r //.
  Qed.

  Theorem pow_add_r : ∀ a b c, a^(b+c) = a^b * a^c.
  Proof.
    induction c using Induction;
      rewrite ? add_0_r ? pow_0_r ? M3_r ? add_succ_r ? pow_succ_r ? IHc ? M2//.
  Qed.

  Theorem pow_mul_l : ∀ a b c, (a*b)^c = a^c * b^c.
  Proof.
    induction c using Induction;
      rewrite ? pow_0_r ? M3 ? pow_succ_r -? M2 ? (M2 _ a)
              ? (M1 _ _ (b^c)) ? IHc ? M2 //.
  Qed.

  Theorem pow_mul_r : ∀ a b c, a^(b*c) = (a^b)^c.
  Proof.
    induction c using Induction;
      rewrite ? naturals.mul_0_r ? pow_0_r ? mul_succ_r
              ? pow_succ_r ? pow_add_r ? IHc //.
  Qed.

  Theorem prod_mul : ∀ f a b c,
      a ≤ b → c^(S (b-a)) * prod f a b = prod (λ n, c * (f n)) a b.
  Proof.
    move=> f a b c [d <-].
    elim/Induction: d => [ | n].
    - rewrite add_0_r sub_diag pow_1_r ? prod_0 //.
    - rewrite ? (add_comm a) ? sub_abba ? pow_succ_r add_succ_l ? prod_succ
              // => [ | | <-]; eauto using le_trans, le_add_l, le_succ; ring.
  Qed.

  Theorem unit_pow_closure : ∀ a n, 0 < n → unit (a^n) → unit a.
  Proof.
    move=> a n.
    elim (classic (n = 0%N)) => [-> /lt_irrefl | /succ_0 [m ->] H] //.
    rewrite pow_succ_r /unit /divide => [[x]].
    eauto using M2, eq_trans, eq_sym.
  Qed.

  Definition INR (n : N) := sum (λ n, 1) 1 n.
  Global Coercion INR : N >-> R.

  Theorem INR_zero : 0 = 0%N.
  Proof.
    rewrite /INR sum_neg; eauto using naturals.succ_lt.
  Qed.

  Theorem INR_one : 1 = 1%N.
  Proof.
    rewrite /INR sum_0 //.
  Qed.

  Theorem INR_add : ∀ a b : N, a + b = (a + b)%N.
  Proof.
    move=> a.
    (elim/Induction; try rewrite -INR_zero add_0_r A1 A3 //) => b H.
    rewrite /INR add_succ_r ? sum_succ -?/(INR (a+b)%N) -? H ? A2 //;
            [exists b | exists (a+b)%N]; rewrite -add_1_r naturals.add_comm //.
  Qed.

  Theorem INR_mul : ∀ a b : N, a * b = ((a * b)%N).
  Proof.
    move=> a.
    (elim/Induction; try rewrite naturals.mul_0_r -? INR_zero mul_0_r //) => b.
    rewrite /INR mul_succ_r sum_succ ? D1_l ? M3_r -/(INR (a*b+a))
            -? INR_add => [ | ->]; auto using one_le_succ.
  Qed.

  Section Subring_construction.

    Variable S : set.
    Hypothesis subset : S ⊂ Ring.
    Definition is_subring S := (∀ a b : R, a ∈ S → b ∈ S → a + b ∈ S) ∧
                               (∀ a b : R, a ∈ S → b ∈ S → a * b ∈ S) ∧
                               (∀ a : R, a ∈ S → -a ∈ S) ∧
                               (1 ∈ S).
    Hypothesis SR : is_subring S.
    Definition sub_R := elts S.

    Definition ISR : sub_R → R.
    Proof.
      move: (@elts_in_set) => /[swap] x /(_ _ x) /subset H.
      exact (mkSet H).
    Defined.

    Global Coercion ISR : sub_R >-> R.

    Definition sub_add : sub_R → sub_R → sub_R.
    Proof.
      move=> a b.
      have H: a + b ∈ S.
      { elim SR => [H [H0 [H1 H2]]].
        apply H; apply (@elts_in_set S). }
      exact (mkSet H).
    Defined.

    Definition sub_mul : sub_R → sub_R → sub_R.
    Proof.
      move=> a b.
      have H: a * b ∈ S.
      { elim SR => [H [H0 [H1 H2]]].
        apply H0; apply (@elts_in_set S). }
      exact (mkSet H).
    Defined.

    Definition sub_neg : sub_R → sub_R.
    Proof.
      move=> a.
      have H: -a ∈ S.
      { elim SR => [H [H0 [H1 H2]]].
        apply H1; apply (@elts_in_set S). }
      exact (mkSet H).
    Defined.

    Declare Scope Subring_scope.
    Delimit Scope Subring_scope with subring.
    Open Scope Subring_scope.
    Bind Scope Subring_scope with sub_R.

    Infix "+" := sub_add : Subring_scope.
    Infix "*" := sub_mul : Subring_scope.

    Notation "- a" := (sub_neg a) : Subring_scope.

    Definition sub_one : sub_R.
    Proof.
      elim SR => [H [H0 [H1 H2]]].
      exact (mkSet H2).
    Defined.
    Notation "1" := sub_one : Subring_scope.

    Theorem ISR_eq : ∀ a b : sub_R, (a : R) = (b : R) → a = b.
    Proof.
      move=> [a A] [b B].
      rewrite /ISR /= => H.
      apply /set_proj_injective.
      now inversion H.
    Qed.

    Theorem ISR_add : ∀ a b : sub_R, (a + b)%ring = a + b.
    Proof.
      auto using set_proj_injective.
    Qed.

    Theorem ISR_mul : ∀ a b : sub_R, (a * b)%ring = a * b.
    Proof.
      auto using set_proj_injective.
    Qed.

    Theorem ISR_neg : ∀ a : sub_R, (-a)%ring = -a.
    Proof.
      auto using set_proj_injective.
    Qed.

    Lemma zero_construction : 0 ∈ S.
    Proof.
      elim SR => [H [H0 [H1 H2]]].
      rewrite <-(A4 _ (1%ring)).
      auto.
    Qed.

    Definition sub_zero := (mkSet zero_construction) : sub_R.
    Notation "0" := sub_zero : Subring_scope.
    Theorem sub_A1 : ∀ a b, a + b = b + a.
    Proof.
      move=> a b.
      apply ISR_eq.
      rewrite -? ISR_add A1 //.
    Qed.

    Theorem sub_A2 : ∀ a b c, a + (b + c) = (a + b) + c.
    Proof.
      move=> a b c.
      apply ISR_eq.
      rewrite -? ISR_add A2 //.
    Qed.

    Theorem sub_zero_is_zero : 0%ring = 0.
    Proof.
      auto using set_proj_injective.
    Qed.

    Theorem sub_one_is_one : 1%ring = 1.
    Proof.
      rewrite /sub_one /and_rect.
      case SR, a, a.
      auto using set_proj_injective.
    Qed.

    Theorem sub_A3 : ∀ a, 0 + a = a.
    Proof.
      move=> a.
      apply ISR_eq.
      rewrite -? ISR_add -sub_zero_is_zero A3 //.
    Qed.

    Theorem sub_A4 : ∀ a, a + -a = 0.
    Proof.
      move=> a.
      apply ISR_eq.
      rewrite -? ISR_add -ISR_neg A4 sub_zero_is_zero //.
    Qed.

    Theorem sub_M1 : ∀ a b, a * b = b * a.
    Proof.
      move=> a b.
      apply ISR_eq.
      rewrite -? ISR_mul M1 //.
    Qed.

    Theorem sub_M2 : ∀ a b c, a * (b * c) = (a * b) * c.
    Proof.
      move=> a b c.
      apply ISR_eq.
      rewrite -? ISR_mul M2 //.
    Qed.

    Theorem sub_M3 : ∀ a, 1 * a = a.
    Proof.
      move=> a.
      apply ISR_eq.
      rewrite -? ISR_mul -sub_one_is_one M3 //.
    Qed.

    Theorem sub_D1 : ∀ a b c, (a + b) * c = a * c + b * c.
    Proof.
      move=> a b c.
      apply ISR_eq.
      rewrite -? ISR_mul -? ISR_add -? ISR_mul D1 //.
    Qed.

    Definition subring :=
      mkRing _ sub_zero sub_one sub_add sub_mul sub_neg sub_A3 sub_A1 sub_A2
             sub_M3 sub_M1 sub_M2 sub_D1 sub_A4.

  End Subring_construction.

  Definition subring_of_arbitrary_set (S : set) : rings.ring.
  Proof.
    elim (excluded_middle_informative (S ⊂ Ring)) => s.
    - elim (excluded_middle_informative (is_subring S)) => i.
      + exact (mkRing _ (sub_zero S i) (sub_one S i) (sub_add S s i)
                      (sub_mul S s i) (sub_neg S s i) (sub_A3 S s i)
                      (sub_A1 S s i) (sub_A2 S s i) (sub_M3 S s i)
                      (sub_M1 S s i) (sub_M2 S s i) (sub_D1 S s i)
                      (sub_A4 S s i)).
      + exact Ring.
    - exact Ring.
  Defined.

  Section Subring_generation.

    Variable S : set.

    Hypothesis subset : S ⊂ Ring.

    Definition subset_generated_by S :=
      ⋂ {s in P Ring | S ⊂ s ∧ is_subring s}.

    Lemma generated_nonempty : {s in P Ring | S ⊂ s ∧ is_subring s} ≠ ∅.
    Proof.
      apply /Nonempty_classification.
      exists Ring.
      rewrite Specify_classification Powerset_classification.
      repeat split; eauto using Set_is_subset, elts_in_set.
    Qed.

    Lemma generated_subset : subset_generated_by S ⊂ Ring.
    Proof.
      rewrite /subset_generated_by => x /Intersection_classification
      => /(_ generated_nonempty) H; move: generated_nonempty =>
      /Nonempty_classification [s /[dup] /Specify_classification
                                  [/Powerset_classification H1 [H2 H3]]]; auto.
    Qed.

    Lemma subring_generation_construction : is_subring (subset_generated_by S).
    Proof.
      ((repeat split) =>
       [? ? /Intersection_classification /[swap] /Intersection_classification |
        ? ? /Intersection_classification /[swap] /Intersection_classification |
        ? /Intersection_classification | ];
       (try move: generated_nonempty => /[swap] /[apply] H);
       (try move: generated_nonempty => /[swap] /[apply] H0);
       try apply Intersection_classification; auto using generated_nonempty) =>
      [s /[dup] /Specify_classification [?[?[?[?[??]]]]] /[dup] /H ? /H0 ? |
       s /[dup] /Specify_classification [?[?[?[?[??]]]]] /[dup] /H ? /H0 ? |
       s /[dup] /Specify_classification [?[?[?[?[??]]]]] /H ? |
       s /Specify_classification [?[?[?[?[??]]]]]]; auto.
    Qed.

    Definition subring_generated_by :=
      subring (subset_generated_by S) generated_subset
              subring_generation_construction.

    Theorem subset_generated_by_subring :
      is_subring S → S = subset_generated_by S.
    Proof.
      rewrite /subset_generated_by => H.
      apply Extensionality => z.
      split => [H0 | /Intersection_classification].
      - apply /Intersection_classification; auto using generated_nonempty =>
        s /Specify_classification [H1 [H2 H3]]; auto.
      - move: subset => /Powerset_classification H0 /(_ generated_nonempty).
        suff: (S ∈ {s in P Ring | S ⊂ s ∧ is_subring s}); auto.
        apply Specify_classification, conj, conj; auto using Set_is_subset.
    Qed.

  End Subring_generation.

  Theorem subring_wf :
    ∀ S T, S = T → subring_of_arbitrary_set S = subring_of_arbitrary_set T.
  Proof.
    move=> S T -> //.
  Qed.

  Section Subrings_match.

    Variable S : set.
    Hypothesis subset_S : S ⊂ Ring.
    Hypothesis subring_S : is_subring S.

    Theorem subrings_match :
      subring_of_arbitrary_set S = subring S subset_S subring_S.
    Proof.
      rewrite /subring_of_arbitrary_set /subring.
      (repeat elim excluded_middle_informative => /=; try tauto) => s i.
      suff -> : s = subset_S; auto using proof_irrelevance.
      suff -> : i = subring_S; auto using proof_irrelevance.
    Qed.

  End Subrings_match.

  Section Subrings_generated_by_subrings.

    Variable S : set.
    Hypothesis subset_S : S ⊂ Ring.
    Hypothesis subring_S : is_subring S.

    Theorem subring_generated_by_subring :
      subring S subset_S subring_S = subring_generated_by S subset_S.
    Proof.
      rewrite /subring_generated_by -? subrings_match
      -(subset_generated_by_subring S); auto.
    Qed.

  End Subrings_generated_by_subrings.

  Theorem zero_ring_degeneracy : 1 = 0 → ∀ a b : R, a = b.
  Proof.
    move=> H a b.
    ring [H].
  Qed.

  Theorem unit_nonzero : 1 ≠ 0 → ∀ a, unit a → a ≠ 0.
  Proof.
    move=> H a /[swap] -> [x H0].
    now ring_simplify in H0.
  Qed.

  Theorem singleton_sum :
    ∀ m n a, m ≤ n → sum (λ k, If k = m then a else 0) 0 n = a.
  Proof.
    move=> m /[swap] a.
    elim/Induction => [ | n].
    - rewrite sum_0.
      (elim excluded_middle_informative; auto) =>
      /neq_sym /succ_0 [k ->] /le_not_gt.
      move: lt_succ => /(_ k) //.
    - elim (classic (m = S n)) => [-> H H0 | H H0 H1].
      + rewrite sum_succ -1?{3} (A3 _ a) -1 ? (sum_of_0 n); auto using zero_le.
        f_equal; last by (elim excluded_middle_informative => /=; tauto).
        apply /iterate_extensionality => k.
        elim excluded_middle_informative; auto using sum_of_0
        => -> [H1] /not_succ_le //.
      + rewrite sum_succ ? H0; auto using zero_le.
        * apply le_lt_succ, conj => //.
        * elim excluded_middle_informative => [ /(@eq_sym N) | ] //.
          rewrite A3_r //.
  Qed.

  Theorem prod_sum_0 :
    ∀ k x f, prod (λ n, x^(f n)) 0 k = x^(sum_N (λ n, f n) 0 k).
  Proof.
    elim/Induction =>
    [ | k H] *; rewrite ? sum_N_0 ? prod_0 ? prod_succ ? sum_N_succ
                        ? H ? pow_add_r; auto using zero_le.
  Qed.

  Theorem prod_sum :
    ∀ a b x f, prod (λ n, x^(f n)) a b = x^(sum_N (λ n, f n) a b).
  Proof.
    move=> a b x f.
    elim (classic (a ≤ b)%N) => [[c <-] | /lt_not_ge H].
    - rewrite /prod /sum_N ? iterate_shift -prod_sum_0 //.
    - rewrite prod_neg ? sum_N_neg ? pow_0_r //.
  Qed.

  Theorem pow_neg_1_l : ∀ n, (-1)^n = 1 ∨ (-1)^n = -1.
  Proof.
    elim/Induction => [ | n].
    - apply /or_introl /pow_0_r.
    - elim; [ right | left ]; rewrite pow_succ_r H; ring.
  Qed.

  Theorem pow_sign_l : ∀ a n, (-a)^n = a^n ∨ (-a)^n = -a^n.
  Proof.
    move=> a n.
    rewrite -mul_neg_1_l ? pow_mul_l.
    case (pow_neg_1_l n) => [-> | ->]; rewrite ? M3 ? mul_neg_1_l; auto.
  Qed.

  Theorem add_move_l : ∀ a b c, a = b + -c ↔ a + c = b.
  Proof.
    split => [-> | <-]; ring.
  Qed.

  Theorem add_move_lr : ∀ a b c d, a + -b = c + -d ↔ a + d = b + c.
  Proof.
    split => [/add_move_l <- | /add_move_l ->]; ring.
  Qed.

  Section Ideals.

    Variable I : set.
    Hypothesis subset : I ⊂ Ring.
    Definition is_ideal I := (∀ a b : R, a ∈ I → b ∈ I → a + b ∈ I) ∧
                               (∀ a b : R, b ∈ I → a * b ∈ I).
    Hypothesis IR : is_ideal I.
    Definition Ideal := elts I.

  End Ideals.

End Ring_theorems.

Arguments assoc {Ring}.
Arguments unit {Ring}.

Section Homomorphisms.

  Local Reserved Notation " a ⊕ b " (at level 50, left associativity).
  Local Reserved Notation " a ⊗ b " (at level 40, left associativity).
  Local Reserved Notation " a ⊞ b " (at level 50, left associativity).
  Local Reserved Notation " a ⊠ b " (at level 40, left associativity).

  Record ringHom :=
    mkRingHom {
        dom : ring where "a ⊕ b" := (add dom a b) and "a ⊗ b" := (mul dom a b);
        ran : ring where "a ⊞ b" := (add ran a b) and "a ⊠ b" := (mul ran a b);
        func :> (elts dom) → (elts ran);
        add_hom : ∀ x y : elts dom, func (x ⊕ y) = func x ⊞ func y;
        mul_hom : ∀ x y : elts dom, func (x ⊗ y) = func x ⊠ func y;
        one_hom : func (one dom) = (one ran);
      }.

  Variable f : ringHom.

  Definition ker f := {r of type dom f | (func f) r = (zero (ran f))}.

  Theorem ker_is_ideal : is_ideal (dom f) (ker f).
  Proof.
    (((split => a b; rewrite ? Specify_classification /specify_lift) =>
        [[] ? /[swap] [[]] ? | [] ?]; repeat elim excluded_middle_informative
        => //=; auto using elts_in_set) => [? ? H H0 H1 | ? ? H]);
    [ rewrite -(A3 _ (zero _)) -{1}H1 -H0 -add_hom |
      rewrite -(mul_0_r _ (f a)) -H -mul_hom ];
    intuition repeat (repeat f_equal; apply set_proj_injective => /=).
  Qed.

End Homomorphisms.
