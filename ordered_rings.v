Set Warnings "-notation-overridden,-ambiguous-paths".
Require Export ssreflect ssrbool ssrfun integral_domains.

Record ordered_ring :=
  mkOR {
      ring :> rings.ring where
      "a + b" :=
        (add ring a b)
          and "a * b" :=
        (mul ring a b)
          and "0" :=
          (zero ring)
          and "1" :=
            (one ring);
      lt : elts ring → elts ring → Prop
      where "a < b" := (lt a b);
      lt_trans : ∀ a b c, a < b → b < c → a < c;
      T : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ b < a) ∨
                    (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
                    (¬ a < b ∧ a ≠ b ∧ b < a);
      O1 : ∀ a b c, b < c → a + b < a + c;
      O2 : ∀ a b, 0 < a → 0 < b → 0 < a * b;
      nontriviality : 1 ≠ 0;
    }.

Section Ordered_ring_theorems.

  Variable OR : ordered_ring.

  Notation Ring := (ring OR).
  Notation R := (elts Ring).
  Notation "0" := (zero Ring).
  Notation "1" := (one Ring).
  Infix "+" := (add Ring).
  Notation "2" := (1 + 1).
  Infix "*" := (mul Ring).
  Notation "- a" := (neg Ring a).
  Notation "- 1" := (neg Ring 1).
  Infix "-" := (sub Ring).
  Infix "^" := (pow Ring).
  Infix "<" := (lt OR).
  Notation lt_trans := (lt_trans OR).
  Notation O1 := (O1 OR).
  Notation O2 := (O2 OR).
  Notation T := (T OR).
  Notation "a > b" := (b < a) (only parsing).
  Definition le a b := a < b ∨ a = b.
  Infix "≤" := le.
  Notation "x < y < z" := (x < y ∧ y < z).
  Notation "a ≥ b" := (b ≤ a) (only parsing).
  Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level).
  Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level).
  Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level).

  Add Ring generic_ordered_ring : (ringify Ring).

  Theorem trichotomy : ∀ a b, a < b ∨ a = b ∨ b < a.
  Proof.
    move: T => /[swap] a /[swap] b /(_ a b); intuition.
  Qed.

  Theorem O1_r : ∀ a b c, b < c → b + a < c + a.
  Proof.
    move=> a b c H.
    rewrite ? (A1 _ _ a).
    auto using O1.
  Qed.

  Theorem add_le_r : ∀ a b c, b ≤ c → b + a ≤ c + a.
  Proof.
    move=> a b c [H | H].
    - left.
      auto using O1_r.
    - right.
      ring [H].
  Qed.

  Theorem add_le_l : ∀ a b c, b ≤ c → a + b ≤ a + c.
  Proof.
    move=> a b c.
    rewrite ? (A1 _ a) => /add_le_r //.
  Qed.

  Theorem O0 : ∀ a b, 0 < a → 0 < b → 0 < a + b.
  Proof.
    move=> a b /(O1 0) /[swap] /(O1 a).
    rewrite A3 A1 => /[swap] /lt_trans /[apply] //.
  Qed.

  Theorem lt_shift : ∀ a b, a < b ↔ 0 < b + -a.
  Proof.
    split => [/(O1_r (-a)) | /(O1_r a)];
               by rewrite ? A4 ? A3 -? A2 ? A4_l ? A3_r.
  Qed.

  Theorem le_shift : ∀ a b, a ≤ b ↔ 0 ≤ b + -a.
  Proof.
    split => [/(add_le_r (-a)) | /(add_le_r a)];
               by rewrite ? A4 ? A3 -? A2 ? A4_l ? A3_r.
  Qed.

  Theorem O3 : ∀ a b c, 0 < a → b < c → a * b < a * c.
  Proof.
    move=> a b c /lt_shift /[swap] /lt_shift /O2 /[apply].
    (have ->: (c + -b) * (a + -0) = a * c + -(a * b) by ring) =>
      /(iffRL (lt_shift _ _)) //.
  Qed.

  Theorem O3_r : ∀ a b c, 0 < a → b < c → b * a < c * a.
  Proof.
    move=> a b c.
    rewrite ? (M1 _ _ a) => /O3 /[apply] //.
  Qed.

  Definition mul_lt_l := O3.
  Definition mul_lt_r := O3_r.

  Theorem neg_lt_0 : ∀ a, 0 < a ↔ -a < 0.
  Proof.
    move: lt_shift => /[swap] a /(_ (-a)) ->.
      by have ->: 0 + --a = a by ring.
  Qed.

  Theorem lt_neg_0 : ∀ a, a < 0 ↔ 0 < -a.
  Proof.
    move: lt_shift => /[swap] a /(_ a) ->.
      by have ->: 0 + -a = -a by ring.
  Qed.

  Theorem neg_le_0 : ∀ a, 0 ≤ a ↔ -a ≤ 0.
  Proof.
    split => [/le_shift | /le_shift].
    - (have ->: a + -0 = 0 + --a by ring) => /(iffRL (le_shift _ _)) //.
    - have ->: 0 + --a = a => //; ring.
  Qed.

  Theorem le_neg_0 : ∀ a, a ≤ 0 ↔ 0 ≤ -a.
  Proof.
    move=> a.
    rewrite neg_le_0.
    have ->: --a = a => //; ring.
  Qed.

  Definition mul_pos_pos := O2.

  Theorem mul_pos_neg : ∀ a b, 0 < a → b < 0 → a * b < 0.
  Proof.
    move=> a b /[swap] /lt_neg_0 /O2 /[apply].
    (have ->: -b * a = -(a * b) by ring) => /lt_neg_0 //.
  Qed.

  Theorem mul_neg_pos : ∀ a b, a < 0 → 0 < b → a * b < 0.
  Proof.
    move=> a b /mul_pos_neg /[apply].
      by rewrite M1.
  Qed.

  Theorem mul_neg_neg : ∀ a b, a < 0 → b < 0 → 0 < a * b.
  Proof.
    move=> a b /lt_neg_0 /[swap] /lt_neg_0 /O2 /[apply].
    have ->: -b * -a = a * b => //; ring.
  Qed.

  Theorem pos_mul : ∀ a b, 0 < a * b → (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0).
  Proof.
    move=> a b H.
    case (T (a*b) 0), (T a 0), (T b 0); intuition; subst;
      rewrite -> ? mul_0_r, ? mul_0_l in *; auto; exfalso;
        eauto using mul_neg_pos, mul_pos_neg.
  Qed.

  Theorem pos_mul_iff : ∀ a b, 0 < a * b ↔ (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0).
  Proof.
    (split; auto using pos_mul) =>
    [[[] /mul_pos_pos /[apply] | [] /mul_neg_neg /[apply]]] //.
  Qed.

  Theorem neg_mul : ∀ a b, a * b < 0 → (0 < a ∧ b < 0) ∨ (a < 0 ∧ 0 < b).
  Proof.
    move=> a b H.
    case (T (a*b) 0), (T a 0), (T b 0); intuition; subst;
      rewrite -> ? mul_0_r, ? mul_0_l in *; exfalso;
        eauto using mul_neg_neg, mul_pos_pos.
  Qed.

  Theorem cancellation_0_mul : ∀ a b, a * b = 0 → a = 0 ∨ b = 0.
  Proof.
    move=> a b H.
    case (T (a*b) 0), (T a 0), (T b 0); intuition;
      eauto using pos_mul, neg_mul; exfalso;
        eauto using mul_neg_neg, mul_neg_pos, mul_pos_neg, mul_pos_pos.
  Qed.

  Definition integral_domain := mkID Ring cancellation_0_mul (nontriviality OR).

  Lemma zero_lt_1 : 0 < 1.
  Proof.
    elim (T 0 1) => [ | [[] /[swap] [[]] * |
                         [] /[swap] [[]] /[swap] /(O1_r (-1))]]; try tauto.
    - by contradiction (nontriviality OR).
    - rewrite A4 A3 -(M3 _ 1) -(rings.mul_neg_neg _ 1 1) => *.
      apply mul_pos_pos; refine (@eq_rect _ _ _ _ _ _); eauto; ring.
  Qed.

  Lemma lt_succ : ∀ m, m < m + 1.
  Proof.
    move=> m.
    rewrite -{1}(A3 _ m) A1.
    eauto using O1, zero_lt_1.
  Qed.

  Lemma succ_lt : ∀ n m, n < m → n < m + 1.
  Proof.
    eauto using lt_succ, lt_trans.
  Qed.

  Theorem lt_irrefl : ∀ a, ¬ a < a.
  Proof.
    move: T => /[swap] a /(_ a a); intuition.
  Qed.

  Theorem lt_antisym : ∀ a b, a < b → ¬ b < a.
  Proof.
    move: T => /[swap] a /[swap] b /(_ a b); intuition.
  Qed.

  Theorem O3_iff : ∀ a b c, 0 < a → b < c ↔ a * b < a * c.
  Proof.
    split => [H0 | ]; eauto using O3.
    elim (T b c) => [[H1 _] | [[_ [-> _] /lt_irrefl] |
                               [_ [_ /(O3 a _ _ H) /lt_antisym H1]]]] => //.
  Qed.

  Theorem le_antisymm : ∀ a b, a ≤ b → b ≤ a → a = b.
  Proof.
    move=> a b [/lt_antisym H | ->] // => [[H0 | ->]] //.
  Qed.

  Lemma square_ne0 : ∀ a, a ≠ 0 → a * a > 0.
  Proof.
    move: T => /[swap] a /(_ a 0) H H0; intuition; subst;
                 auto using mul_pos_pos, mul_neg_neg.
  Qed.

  Theorem le_trans : ∀ a b c, a ≤ b → b ≤ c → a ≤ c.
  Proof.
    move=> a b c [H | H] [H0 | H0]; subst; rewrite /le; eauto using lt_trans.
  Qed.

  Lemma pos_div_l : ∀ a b, 0 < a → 0 < a * b → 0 < b.
  Proof.
    move: pos_mul => /[swap] a /[swap] b /(_ a b) H H0.
    case (T 0 a), (T 0 b); intuition.
  Qed.

  Lemma pos_div_r : ∀ a b, 0 < a → 0 < b * a → 0 < b.
  Proof.
    move=> a b.
      by rewrite M1 => /pos_div_l /[apply].
  Qed.

  Lemma neg_div_l : ∀ a b, a < 0 → 0 < a * b → b < 0.
  Proof.
    move: pos_mul => /[swap] a /[swap] b /(_ a b) H H0.
    case (T 0 a), (T 0 b); intuition.
  Qed.

  Lemma neg_div_r : ∀ a b, a < 0 → 0 < b * a → b < 0.
  Proof.
    move=> a b.
      by rewrite M1 => /neg_div_l /[apply].
  Qed.

  Lemma pos_neg_div_l : ∀ a b, 0 < a → a * b < 0 → b < 0.
  Proof.
    move: neg_mul => /[swap] a /[swap] b /(_ a b) H H0.
    case (T 0 a), (T 0 b); intuition.
  Qed.

  Lemma pos_neg_div_r : ∀ a b, 0 < a → b * a < 0 → b < 0.
  Proof.
    move=> a b.
      by rewrite M1 => /pos_neg_div_l /[apply].
  Qed.

  Lemma neg_pos_div_l : ∀ a b, a < 0 → a * b < 0 → 0 < b.
  Proof.
    move: neg_mul => /[swap] a /[swap] b /(_ a b) H H0.
    case (T 0 a), (T 0 b); intuition.
  Qed.

  Lemma neg_pos_div_r : ∀ a b, a < 0 → b * a < 0 → 0 < b.
  Proof.
    move=> a b.
      by rewrite M1 => /neg_pos_div_l /[apply].
  Qed.

  Lemma one_lt : ∀ a, 1 < a → 0 < a.
  Proof.
    eauto using lt_trans, zero_lt_1.
  Qed.

  Theorem mul_le_l : ∀ a b c, 0 < a → b ≤ c → a * b ≤ a * c.
  Proof.
    move=> a b c H [/(mul_lt_l a _ _ H) | ->]; [left | right] => //.
  Qed.

  Theorem mul_le_r : ∀ a b c, a ≤ b → 0 < c → a * c ≤ b * c.
  Proof.
    move=> a b c.
      by rewrite ? (M1 _ _ c) => /mul_le_l /[apply].
  Qed.

  Theorem neg_neg_lt : ∀ a b, a < b → -b < -a.
  Proof.
    move=> a b /(O1 (-a+-b)) => H.
      by ring_simplify in H.
  Qed.

  Theorem lt_neq : ∀ a b, a < b → b ≠ a.
  Proof.
    move=> a b /[swap] -> /lt_irrefl //.
  Qed.

  Theorem lt_sub_pos : ∀ a b, 0 < b → a - b < a.
  Proof.
    move=> a b H.
    rewrite lt_shift.
    now ring_simplify.
  Qed.

  Theorem lt_cross_mul : ∀ a b c d,
      0 < a → 0 < c → a < b → c < d → a * c < b * d.
  Proof.
    move=> a b c d H H0 /[dup] H1 /(O3 c) => /(_ H0) /[swap] /[dup] H3 /(O3 b).
    rewrite ? (M1 _ c).
    eauto using lt_trans.
  Qed.

  Theorem lt_le_cross_mul : ∀ a b c d,
      0 < a → 0 < c → a < b → c ≤ d → a * c < b * d.
  Proof.
    move=> a b c d ? /[swap] ? /[swap] [[ | ->]]; auto using lt_cross_mul, O3_r.
  Qed.

  Theorem le_lt_cross_mul : ∀ a b c d,
      0 < a → 0 < c → a ≤ b → c < d → a * c < b * d.
  Proof.
    move=> a b c d /[swap] ? /[swap] [[? | ->]] *; auto using lt_cross_mul, O3.
  Qed.

  Theorem lt_or_ge : ∀ a b, a < b ∨ b ≤ a.
  Proof.
    move: T => /[swap] a /[swap] b /(_ a b) [[H _] | [[_ [H _]] | [_ [_ H]]]];
                 rewrite /le; intuition.
  Qed.

  Theorem lt_not_ge : ∀ a b, a < b ↔ ¬ b ≤ a.
  Proof.
    move: T => /[swap] a /[swap] b /(_ b a); rewrite /le; tauto.
  Qed.

  Theorem le_not_gt : ∀ a b, a ≤ b ↔ ¬ b < a.
  Proof.
    move: T => /[swap] a /[swap] b /(_ a b); rewrite /le; tauto.
  Qed.

  Theorem mul_le_l_iff : ∀ a b c, 0 < a → b ≤ c ↔ a * b ≤ a * c.
  Proof.
    split => H0; auto using mul_le_l.
    apply le_not_gt => /(O3 a) => /(_ H) /lt_not_ge [] //.
  Qed.

  Theorem mul_le_r_iff : ∀ a b c, 0 < a → b ≤ c ↔ b * a ≤ c * a.
  Proof.
    move=> a b c /mul_le_l_iff.
      by rewrite ? (M1 _ _ a).
  Qed.

  Theorem O0_opp : ∀ a b, 0 < a + b → 0 < a ∨ 0 < b.
  Proof.
    move: T => /[swap] a /(_ 0 a)
                [[H0 _] b | [[_ [<- _] b] | [_ [_ H0]] b /(lt_trans a 0 _ H0)
                                                       /lt_shift H1]]; auto.
    - rewrite A3 => /or_intror //.
    - ring_simplify in H1.
      right => //.
  Qed.

  Theorem pow_pos : ∀ a b, 0 < a → 0 < a^b.
  Proof.
    induction b using Induction.
    - move: pow_0_r zero_lt_1 -> => //.
    - move: pow_succ_r -> => /[dup] /IHb /O2 /[apply] //.
  Qed.

  Theorem pow_ge_1 : ∀ a n, 1 < a → 1 ≤ a^n.
  Proof.
    induction n using Induction.
    - move: pow_0_r (eq_refl 1) -> => /or_intror => /(_ (1 < 1)) //.
    - rewrite pow_succ_r -{2}(M3 _ 1) =>
      /[dup] /IHn /le_lt_cross_mul /[apply] /(_ zero_lt_1) /(_ zero_lt_1)
      => /or_introl => /(_ (1 * 1 = (a^n * a))) //.
  Qed.

  Theorem pow_gt_1 : ∀ a n, 1 < a → (0 < n)%N → 1 < a^n.
  Proof.
    induction n using Induction => [H /naturals.lt_irrefl | H H0] //.
    move: pow_succ_r (classic (n = 0%N)) -> => [[-> | /succ_0 [m H1]]].
      + rewrite pow_0_r M3 //.
      + move: (M3 _ 1) H1 IHn H0 => {3}<- =>
        -> /(_ H) /(_ (naturals.lt_succ m)) /(lt_cross_mul 1 (a^(S m)) 1 a) =>
        /(_ zero_lt_1) /(_ zero_lt_1) /(_ H) //.
  Qed.

  Theorem one_lt_2 : 1 < 1 + 1.
  Proof.
    rewrite -{1}(A3_r _ 1).
    apply /O1 /zero_lt_1.
  Qed.

  Definition min (a b : R) := If (a < b) then a else b.

  Theorem min_le_l : ∀ a b, min a b ≤ a.
  Proof.
    rewrite /min /le => a b.
    (case excluded_middle_informative; first by right) => /le_not_gt //.
  Qed.

  Theorem min_le_r : ∀ a b, min a b ≤ b.
  Proof.
    rewrite /min /le => a b.
    case excluded_middle_informative; intuition.
  Qed.

  Theorem min_eq : ∀ a b, min a b = a ∨ min a b = b.
  Proof.
    rewrite /min /le => a b.
    case excluded_middle_informative; intuition.
  Qed.

  Definition max (a b : R) := If (a < b) then b else a.

  Theorem max_le_l : ∀ a b, a ≤ max a b.
  Proof.
    rewrite /max /le => a b.
    case excluded_middle_informative; intuition.
  Qed.

  Theorem max_le_r : ∀ a b, b ≤ max a b.
  Proof.
    rewrite /max => a b.
    (case excluded_middle_informative; first by right) => /le_not_gt //.
  Qed.

  Theorem max_eq : ∀ a b, max a b = a ∨ max a b = b.
  Proof.
    rewrite /max /le => a b.
    case excluded_middle_informative; intuition.
  Qed.

  Theorem lt_cross_add : ∀ a b c d, a < b → c < d → a + c < b + d.
  Proof.
    move=> a b c d /(O1_r c) /[swap] /(O1 b) /[swap] /lt_trans /[apply] //.
  Qed.

  Theorem le_cross_add : ∀ a b c d, a ≤ b → c ≤ d → a + c ≤ b + d.
  Proof.
    move=> a b c d /(add_le_r c) /[swap] /(add_le_l b) /[swap]
             /le_trans /[apply] //.
  Qed.

  Lemma square_ge_1 : ∀ r, 0 < r → 1 < r * r → 1 < r.
  Proof.
    move: T => /[swap] r /(_ 1 r) =>
    [[[H _] | [[_ [<- _]] | [_ [_ H]] H0 /lt_antisym []]]];
      try tauto; first by rewrite M3.
    rewrite -(M3 _ 1).
      by apply lt_cross_mul.
  Qed.

  Theorem zero_lt_2 : 0 < 2.
  Proof.
    move: zero_lt_1 => /[dup] /(O1_r 1).
    rewrite A3 => /[swap] /lt_trans /[apply] //.
  Qed.

  Theorem zero_ne_2 : 2 ≠ 0.
  Proof.
    move: zero_lt_2 => /[swap] -> /lt_irrefl //.
  Qed.

  Theorem le_lt_trans : ∀ a b c, a ≤ b → b < c → a < c.
  Proof.
    move=> a b c [/lt_trans /[apply] | ->] //.
  Qed.

  Theorem lt_le_trans : ∀ a b c, a < b → b ≤ c → a < c.
  Proof.
    move=> a b c /[swap] [[/[swap] /lt_trans /[apply] | <-]] //.
  Qed.

  Theorem le_refl : ∀ a, a ≤ a.
  Proof.
    right => //.
  Qed.

  Theorem mul_le_l_nonneg : ∀ a b c, 0 ≤ a → b ≤ c → a * b ≤ a * c.
  Proof.
    move=> a b c [/[swap] /mul_le_l /[apply] | <-] //.
    move: (mul_0_l _ b) (mul_0_l _ c) (le_refl 0) -> => -> //.
  Qed.

  Theorem mul_le_r_nonneg : ∀ a b c, a ≤ b → 0 ≤ c → a * c ≤ b * c.
  Proof.
    move=> a b c H [/(mul_le_r _ _ _ H) | <-] //.
    move: (mul_0_r _ a) (mul_0_r _ b) (le_refl 0) -> => -> //.
  Qed.

  Theorem mul_nonneg_nonneg : ∀ a b, 0 ≤ a → 0 ≤ b → 0 ≤ a * b.
  Proof.
    move=> a b /mul_le_l_nonneg /[apply].
    rewrite mul_0_r //.
  Qed.

  Theorem add_nonneg_nonneg : ∀ a b, 0 ≤ a → 0 ≤ b → 0 ≤ a + b.
  Proof.
    move=> a b /[dup] H [/(O1_r 0) /lt_trans /[swap]
                          [[/(O1 a) /[swap] /[apply] | <-]] | <-];
             rewrite ? (A1 _ a) A3 // => /or_introl => /(_ (0 = b + a)) //.
  Qed.

  Theorem pos_ne_0 : ∀ a, 0 < a → a ≠ 0.
  Proof.
    move=> a /[swap] -> /lt_irrefl //.
  Qed.

  Theorem one_ne_minus_one : 1 ≠ -1.
  Proof.
    move: zero_ne_2 => /[swap] {2}-> [].
    apply A4.
  Qed.

  Theorem pos_mul_nonneg : ∀ a b, 0 < a → 0 ≤ a * b → 0 ≤ b.
  Proof.
    move=> a b /mul_pos_neg H /le_not_gt.
    rewrite le_not_gt => /[swap] /H //.
  Qed.

  Theorem le_sym : ∀ a b, a ≤ b ∨ b ≤ a.
  Proof.
    rewrite /le => a b.
    case (T a b); tauto.
  Qed.

  Theorem ne0_lt_gt : ∀ a, a ≠ 0 → 0 < a ∨ a < 0.
  Proof.
    move=> a /neq_sym H.
    case (T 0 a); intuition.
  Qed.

End Ordered_ring_theorems.
