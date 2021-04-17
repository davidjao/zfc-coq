Set Warnings "-notation-overridden,-uniform-inheritance".
Set Warnings "-fragile-hint-constr,-ambiguous-paths".
Require Export naturals rings ordered_rings List Permutation Setoid.

Definition integer_relation :=
  {z of type (ω × ω) × (ω × ω) | π1 (π1 z) + π2 (π2 z) = π2 (π1 z) + π1 (π2 z)}.

Theorem integer_equivalence : is_equivalence (ω × ω) integer_relation.
Proof.
  (repeat split) => [a H | x y H H0 /Specify_classification [H1] |
                     x y z H H0 H1 /Specify_classification [H2]
                     /[swap] /Specify_classification [H3]].
  - have H0: (a, a) ∈ (ω × ω) × (ω × ω) by apply Product_classification; eauto.
    rewrite (reify H0) Specify_classification despecify
            ? π2_action ? π1_action 1 ? add_comm //.
  - have H3: (y, x) ∈ (ω × ω) × (ω × ω) by apply Product_classification; eauto.
    rewrite Specify_classification (reify H) (reify H0) (reify H1) (reify H3)
            ? despecify ? π1_action ? π2_action 1 ? add_comm // => ->.
    rewrite add_comm //.
  - have H4: (x, z) ∈ (ω × ω) × (ω × ω) by apply Product_classification; eauto.
    rewrite Specify_classification (reify H3) ? (reify H2) (reify H4)
            ? despecify ? π1_action ? π2_action //.
    split; auto.
    apply (naturals.cancellation_add (π2 (mkSet H0))).
    ring_simplify [H5 H6].
    rewrite H6; ring_simplify [H5]; rewrite -H5 //.
Qed.

Definition Z := elts ((ω × ω) / integer_relation).

Declare Scope Z_scope.
Delimit Scope Z_scope with Z.
Open Scope Z_scope.
Bind Scope Z_scope with Z.

Definition IZS (a : Z) := elt_to_set a : set.
Coercion IZS : Z >-> set.

Definition embed : N → N → Z.
Proof.
  move=> [a A] [b B].
  have H: (a, b) ∈ ω × ω  by apply Product_classification; eauto.
  exact (quotient_map _ (mkSet H)).
Defined.

Infix "-" := embed : set_scope.

Theorem Zlift : ∀ z, ∃ a b, (a - b = z)%set.
Proof.
  move=> z.
  elim (quotient_lift z) => [y].
  elim (unique_set_element y) =>
  [x [[/Product_classification [a [b [H0 [H1 ->]]]] /[dup] H3 <-] H4]] <-.
  exists (mkSet H0 : N), (mkSet H1 : N).
  apply set_proj_injective => /=.
  rewrite -quotient_image H3 //.
Qed.

Theorem Zequiv : (∀ a b c d, a - b = c - d ↔ a + d = b + c)%set.
Proof.
  move=> [a A] [b B] [c C] [d D].
  have H: (a, b) ∈ ω × ω by apply Product_classification; eauto.
  have H0: (c, d) ∈ ω × ω by apply Product_classification; eauto.
  rewrite /embed /ssr_have.
  (split; rewrite ? quotient_equiv /=; auto using integer_equivalence) =>
  [ /Specify_classification [H1] | H1].
  - rewrite (reify H1) despecify ? π1_action ? π2_action ? π1_action //.
  - have H2: ((a, b), (c, d)) ∈ (ω × ω) × (ω × ω) by
        apply Product_classification; eauto.
    rewrite Specify_classification (reify H2) despecify
            ? π2_action ? π1_action ? π2_action //.
Qed.

Definition INZ a := (a - 0)%set.
Coercion INZ : N >-> Z.

Definition add : Z → Z → Z.
Proof.
  move=> x y.
  elim (constructive_indefinite_description (Zlift x)) =>
  [a /constructive_indefinite_description [b H]].
  elim (constructive_indefinite_description (Zlift y)) =>
  [c /constructive_indefinite_description [d H0]].
  exact ((a + c) - (b + d))%set.
Defined.

Definition mul : Z → Z → Z.
Proof.
  move=> x y.
  elim (constructive_indefinite_description (Zlift x)) =>
  [m /constructive_indefinite_description [n H]].
  elim (constructive_indefinite_description (Zlift y)) =>
  [p /constructive_indefinite_description [q H0]].
  exact ((m * p + n * q) - (n * p + m * q))%set.
Defined.

Definition neg : Z → Z.
Proof.
  move=> x.
  elim (constructive_indefinite_description (Zlift x)) =>
  [a /constructive_indefinite_description [b H]].
  exact (b - a)%set.
Defined.

Definition zero := 0%N : Z.
Definition one := 1%N : Z.

Infix "+" := add : Z_scope.
Infix "*" := mul : Z_scope.
Notation "- a" := (neg a) : Z_scope.
Notation "- 1" := (neg one) : Z_scope.
Notation "0" := zero : Z_scope.
Notation "1" := one : Z_scope.
Notation "2" := (1+1) : Z_scope.
Notation "3" := (2+1) : Z_scope.
Notation "4" := (3+1) : Z_scope.

Theorem add_wf : ∀ a b c d, ((a - b) + (c - d) = (a + c) - (b + d))%set.
Proof.
  rewrite /add /sig_rect => a b c d.
  (repeat elim constructive_indefinite_description) => x [y H] z [w H0].
  (repeat elim constructive_indefinite_description) => e /Zequiv H1 f /Zequiv.
  move: H H0 => /Zequiv H /Zequiv H0 H2.
  rewrite Zequiv.
  ring_simplify [H H1].
  rewrite -H1 -? add_assoc H2 //.
Qed.

Theorem INZ_add : ∀ a b : N, a + b = (a + b)%N.
Proof.
  rewrite /add /sig_rect /INZ => a b.
  (repeat elim constructive_indefinite_description) => x [y H] z [w H0].
  (repeat elim constructive_indefinite_description) => c H1 d H2.
  move: H H0 H1 H2.
  rewrite ? Zequiv ? add_0_r => -> -> -> ->.
  ring.
Qed.

Theorem INZ_mul : ∀ a b : N, a * b = (a * b)%N.
Proof.
  rewrite /mul /sig_rect /INZ => a b.
  (repeat elim constructive_indefinite_description) => x [y H] z [w H0].
  (repeat elim constructive_indefinite_description) => c H1 d H2.
  move: H H0 H1 H2.
  rewrite ? Zequiv ? add_0_r => -> -> -> ->.
  ring.
Qed.

Theorem INZ_eq : ∀ a b : N, (a : Z) = (b : Z) ↔ a = b.
Proof.
  split => [/Zequiv H | ->] //.
  ring [H].
Qed.

Theorem A1 : ∀ a b, a + b = b + a.
Proof.
  move=> a b.
  elim (Zlift a) => [a1 [a2 <-]].
  elim (Zlift b) => [b1 [b2 <-]].
  rewrite ? add_wf Zequiv.
  ring.
Qed.

Theorem A2 : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  move=> a b c.
  elim (Zlift a) => [a1 [a2 <-]].
  elim (Zlift b) => [b1 [b2 <-]].
  elim (Zlift c) => [c1 [c2 <-]].
  rewrite ? add_wf Zequiv.
  ring.
Qed.

Theorem A3 : ∀ a, 0 + a = a.
Proof.
  move=> a.
  elim (Zlift a) => [a1 [a2 <-]].
  rewrite add_wf Zequiv.
  ring.
Qed.

Theorem neg_wf : ∀ a b, - (a - b)%set = (b - a)%set.
Proof.
  move=> a b.
  rewrite /neg /sig_rect.
  elim constructive_indefinite_description => x [y H].
  elim constructive_indefinite_description => z /Zequiv H0.
  rewrite ? Zequiv //.
Qed.

Theorem A4 : ∀ a, a + -a = 0.
Proof.
  move=> a.
  elim (Zlift a) => [a1 [a2 <-]].
  rewrite neg_wf add_wf Zequiv.
  ring.
Qed.

Theorem mul_wf : ∀ a b c d,
    ((a - b) * (c - d) = (a * c + b * d) - (b * c + a * d))%set.
Proof.
  rewrite /mul /sig_rect => a b c d.
  (repeat elim constructive_indefinite_description) => x [y H] z [w H0].
  (repeat elim constructive_indefinite_description) => e H1 f H2.
  move: H H0 H1 H2.
  rewrite ? Zequiv ? (add_comm _ c) ? (add_comm _ a) => /[dup] H =>
  -> /[dup] H0 -> /naturals.cancellation_add <- /naturals.cancellation_add <-.
  apply (naturals.cancellation_add (a*x)).
  suff -> : (a*x+(z*x+w*y+(b*c+a*d)) = b*c+a*(x+d)+w*y+x*z)%N; last by ring.
  rewrite H; ring_simplify [H0]; rewrite -? add_assoc -? mul_distr_r -? H0.
  ring_simplify [H0]; f_equal; rewrite -? add_assoc -? mul_distr_l -? H //.
Qed.

Theorem M1 : ∀ a b, a * b = b * a.
Proof.
  move=> a b.
  elim (Zlift a) => [a1 [a2 <-]].
  elim (Zlift b) => [b1 [b2 <-]].
  rewrite ? mul_wf Zequiv.
  ring.
Qed.

Theorem M2 : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  move=> a b c.
  elim (Zlift a) => [a1 [a2 <-]].
  elim (Zlift b) => [b1 [b2 <-]].
  elim (Zlift c) => [c1 [c2 <-]].
  rewrite ? mul_wf Zequiv.
  ring.
Qed.

Theorem M3 : ∀ a, 1 * a = a.
Proof.
  move=> a.
  elim (Zlift a) => [a1 [a2 <-]].
  rewrite ? mul_wf Zequiv.
  ring.
Qed.

Theorem D1 : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  move=> a b c.
  elim (Zlift a) => [a1 [a2 <-]].
  elim (Zlift b) => [b1 [b2 <-]].
  elim (Zlift c) => [c1 [c2 <-]].
  rewrite ? mul_wf ? add_wf ? mul_wf Zequiv.
  ring.
Qed.

Definition lt : Z → Z → Prop.
Proof.
  move=> x y.
  elim (constructive_indefinite_description (Zlift x)) =>
  [a /constructive_indefinite_description [b H]].
  elim (constructive_indefinite_description (Zlift y)) =>
  [c /constructive_indefinite_description [d H0]].
  exact (a+d < b+c).
Defined.

Infix "<" := lt : Z_scope.

Theorem lt_wf : ∀ a b c d : N, (a - b < c - d)%set ↔ (a + d < b + c)%N.
Proof.
  rewrite /lt /sig_rect => a b c d.
  (repeat elim constructive_indefinite_description) => x [y H] z [w H0].
  (repeat elim constructive_indefinite_description) => e H1 f H2.
  move: H H0 H1 H2.
  rewrite ? Zequiv ? (add_comm _ c) ? (add_comm _ a) => /[dup] H =>
  -> /[dup] H0 -> /naturals.cancellation_add <- /naturals.cancellation_add <-.
  split => [/(naturals.O1_iff (b+c)) | /(naturals.O1_iff (w+x))].
  - rewrite -add_assoc (add_comm y) ? add_assoc H0 -add_assoc -H
    -(add_assoc a) (add_assoc w) (add_assoc a) (add_comm a) -? (add_assoc (w+x))
    -naturals.O1_l_iff (add_comm b) //.
  - rewrite (add_comm a) -(add_assoc d) (add_assoc a)
    -H0 add_comm -? add_assoc H (add_comm z) ? add_assoc (add_comm c)
        -? (add_assoc (b+c)) -naturals.O1_l_iff add_comm //.
Qed.

Definition sub a b := (a + -b).
Infix "-" := sub : Z_scope.

Definition ℤ := mkRing _ zero one add mul neg A3 A1 A2 M3 M1 M2 D1 A4.

Add Ring integer_ring_raw : (ringify ℤ).
Add Ring integer_ring : (ringify ℤ : ring_theory 0 1 add mul sub neg eq).
Infix "^" := (rings.pow ℤ) : Z_scope.


Theorem T : ∀ a b, (a < b ∧ a ≠ b ∧ ¬ b < a) ∨
                   (¬ a < b ∧ a = b ∧ ¬ b < a) ∨
                   (¬ a < b ∧ a ≠ b ∧ b < a).
Proof.
  move=> a b.
  elim (Zlift a) => [a1 [a2 <-]].
  elim (Zlift b) => [b1 [b2 <-]].
  rewrite ? lt_wf ? Zequiv ? (add_comm b1) ? (add_comm b2).
  auto using naturals.trichotomy.
Qed.

Theorem lt_def : ∀ a b, a < b ↔ ∃ c : N, 0 ≠ c ∧ b = a + c.
Proof.
  move=> a b.
  elim (Zlift a) => [a1 [a2 <-]].
  elim (Zlift b) => [b1 [b2 <-]].
  ((split; rewrite lt_wf ? lt_def) =>
   [[c [H H0]] | [c [H H0]]]; exists c; move: H0;
   rewrite add_wf Zequiv add_0_r (add_comm a2)) =>
  [<- | ->]; split; try ring; contradict H; rewrite -? INZ_eq -H //.
Qed.

Theorem lt_trans : ∀ a b c, a < b → b < c → a < c.
Proof.
  move=> a b c.
  rewrite ? lt_def => [[x [/neq_sym /INZ_eq ? ->]] [y [/neq_sym /INZ_eq ? ->]]].
  exists (x+y)%N.
  rewrite -{2} INZ_add A2.
  (split; try ring) => /(@eq_sym Z) /INZ_eq /naturals.cancellation_0_add [*] //.
Qed.

Theorem O1 : ∀ a b c, b < c → a + b < a + c.
Proof.
  move=> a b c.
  rewrite ? lt_def => [[x [H ->]]].
  repeat esplit; eauto; ring.
Qed.

Theorem O2 : ∀ a b, 0 < a → 0 < b → 0 < a * b.
Proof.
  move=> a b.
  elim (Zlift a) => [a1 [a2 <-]].
  elim (Zlift b) => [b1 [b2 <-]].
  rewrite mul_wf ? lt_wf ? add_0_l ? naturals.lt_def => [[x [? <-]] [y [? <-]]].
  exists (x*y)%N.
  split => [/(@eq_sym N) /naturals.cancellation_0_mul
             [/(@eq_sym N) | /(@eq_sym N)] | ] //; ring.
Qed.

Theorem zero_lt_1 : 0 < 1.
Proof.
  rewrite lt_wf ? add_0_l.
  eauto using naturals.lt_succ.
Qed.

Theorem zero_ne_1 : 1 ≠ 0.
Proof.
  move /INZ_eq /(@eq_sym N) /PA4 => //.
Qed.

Definition ℤ_order := mkOR ℤ lt lt_trans T O1 O2 zero_ne_1.
Definition ℤ_ID := integral_domain ℤ_order.
Definition le := (le ℤ_order) : Z → Z → Prop.

Infix "≤" := le : Z_scope.
Notation "a > b" := (b < a) (only parsing) : Z_scope.
Notation "a ≥ b" := (b ≤ a) (only parsing) : Z_scope.
Notation "x < y < z" := (x < y ∧ y < z) : Z_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level): Z_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level): Z_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level): Z_scope.

Theorem le_def : ∀ a b, a ≤ b ↔ ∃ c : N, b = a + c.
Proof.
  split => [[/lt_def [c [H0 H1]] | ->] | [c]]; eauto.
  - exists 0%N; rewrite A1 A3 //.
  - case (classic (0 = c)) => [<- -> | ].
    + right; rewrite A1 A3 //.
    + left => /=; rewrite lt_def; exists c => //.
Qed.

Theorem INZ_lt : ∀ a b : N, a < b ↔ (a < b)%N.
Proof.
  split => [/lt_def [c [H]] | /naturals.lt_def [c [H]]];
             rewrite ? lt_def ? naturals.lt_def; exists c; split;
               [ contradict H | | contradict H | ];
               rewrite -? H -? INZ_eq -? H0 -? INZ_add //.
Qed.

Theorem INZ_le : ∀ a b : N, a ≤ b ↔ (a ≤ b)%N.
Proof.
  split => [/le_def [c H] | [c H]]; rewrite ? le_def; exists c;
             rewrite -? INZ_eq -? INZ_add // ? INZ_add ? INZ_eq //.
Qed.

Theorem lt_0_1 : ∀ a, 0 < a → ¬ a < 1.
Proof.
  move=> a /[dup] /lt_def [c [H ->]].
  rewrite A3 ? INZ_lt => H0 H1.
  contradiction (naturals.lt_0_1 c) => //.
Qed.

Theorem lt_n_Sn : ∀ x n, x < S n → x < n ∨ x = n.
Proof.
  move=> x n.
  case (T x n) => [H | [H | [H [H0]]]]; try tauto.
  rewrite ? lt_def => [[a [H1 ->]]] [b [H2]].
  rewrite ? INZ_add INZ_eq -add_1_r -add_assoc =>
  /naturals.cancellation_add /[dup] /(@eq_sym N) /cancellation_1_add =>
  [[/INZ_eq /(@eq_sym Z) | /INZ_eq /(@eq_sym Z)]] //.
Qed.

Theorem strong_induction : ∀ P : Z → Prop,
    (∀ x : Z, (∀ y : Z, 0 < y < x → P y) → P x) → ∀ a : Z, P a.
Proof.
  move=> P H x.
  case (T x 0) =>
  [[? [? ?]] | [[? [? ?]] | [H0 [H1 /lt_def [c [H2 H3]]]]]];
    try now apply H => y [] /lt_trans /[apply] // => _.
  move: H3 H0 H1 H2 => ->; rewrite A3 => H0 H1 _.
  (apply (Induction (λ x : N, P x ∧ ∀ y : N, 0 < y < x → P y))%N =>
   [ | n [? ?]]; (split; [ apply H | ])) =>
  [y [/(lt_antisym ℤ_order)] |
   y [] /INZ_lt /(lt_antisym ℤ_order) /[swap] /INZ_lt |
   y [/[swap] /lt_n_Sn [/[swap] /[dup] /lt_def [d [? ->]] | ->]] |
   y [/[swap] /INZ_lt /lt_n_Sn [/INZ_lt ? | ->]]]
    //; rewrite ? A3 ? INZ_lt; auto.
Qed.

Definition divide := divide ℤ : Z → Z → Prop.

Notation "x ｜ y" := (divide x y) (at level 60, format "x '｜' y") : Z_scope.

Theorem N_ge_0 : ∀ a : N, 0 ≤ a.
Proof.
  induction a using Induction; rewrite /le; auto using ordered_rings.le_refl.
  (case IHa; rewrite <-add_1_r, <-INZ_add) =>
  [/succ_lt | <-] //; rewrite ? A3; left => //.
  now apply zero_lt_1.
Qed.

Theorem lt_0_le_1 : ∀ a, 0 < a ↔ 1 ≤ a.
Proof.
  move=> a.
  ((case (T a 1) =>
    [[H _] | [[_ [-> _]] | [_ [_ H]]]]; split; try move: zero_lt_1 H) =>
   [_ /lt_0_1 /[apply] | /[swap] _ /[swap] /lt_le_trans /[apply] | | | |
    /lt_trans /[apply]] //; auto using zero_lt_1 => * ); [right | left] => //.
Qed.

Theorem div_le : ∀ a b, 0 < b → a｜b → a ≤ b.
Proof.
  move=> a b /[swap] [[]] /=.
  rewrite -/Z => [d ->].
  rewrite /le (le_not_gt ℤ_order) /= =>
  /[dup] H /[swap] /[dup] H0 /[swap] /lt_trans /[apply] H1.
  move: H => /(pos_div_r ℤ_order a d) /lt_0_le_1 => /(_ H1) /mul_le_r /(_ H1).
  rewrite rings.M3 le_not_gt //.
Qed.

Definition assoc := @assoc ℤ : Z → Z → Prop.
Infix "~" := assoc (at level 70) : Z_scope.
Definition unit := @unit ℤ : Z → Prop.

Definition pm a b := (a = b ∨ a = -b).
Notation " a = ± b " := (pm a b) (at level 60) : Z_scope.
Global Hint Unfold assoc unit pm : Z.

Theorem pm_refl : ∀ a, a = ± a.
Proof.
  left => //.
Qed.

Theorem pm_sym : ∀ a b, a = ± b → b = ± a.
Proof.
  move=> a b [H | H].
  - left => //.
  - right; ring [H].
Qed.

Theorem pm_trans : ∀ a b c, a = ± b → b = ± c → a = ± c.
Proof.
  move=> a b c [<- | ->] [<- | ->]; intuition.
  left; ring.
Qed.

Add Parametric Relation : Z pm
      reflexivity proved by (pm_refl)
      symmetry proved by (pm_sym)
      transitivity proved by (pm_trans) as pm_equivalence.

Add Morphism mul with signature pm ==> pm ==> pm as pm_mul.
Proof.
  move=> x y [-> | ->] x0 y0 [-> | ->]; rewrite /pm;
           [left | right | right | left]; ring.
Qed.

Theorem neg_pm : ∀ x, x = ± - x.
Proof.
  move=> x.
  apply /pm_sym /or_intror => //.
Qed.

Add Morphism neg with signature pm ==> pm as pm_neg.
Proof.
  move=> x y [-> | ->]; intuition.
Qed.

Theorem assoc_N : ∀ a b : N, a ~ b → a = b.
Proof.
  rewrite /assoc /rings.assoc -/divide => a b [] /[dup] H; rewrite -INZ_eq.
  elim (N_ge_0 b) => [/div_le /[apply] | <- /[swap] /div_0_l ->] // /[swap].
  elim (N_ge_0 a) => [/div_le /[apply] /le_antisymm /[apply] | ] //.
  move: H => /[swap] <- /div_0_l -> //.
Qed.

Theorem assoc_unit : ∀ a b, a ~ b → ∃ u, unit u ∧ b = a * u.
Proof.
  move=> a b [[c] /[swap] [[d]]].
  case (classic (b = 0)) => [-> -> | /= H -> /[dup] H1 {1}->].
  - esplit; split; eauto using (one_unit ℤ) with Z.
    rewrite mul_0_r M1 M3 //.
  - exists c.
    split; try ring.
    exists d => /=.
    apply (cancellation_mul_r ℤ_ID b) => /= //.
    rewrite {1}H1 M3 M2 (M1 c) //.
Qed.

Theorem assoc_pm : ∀ a b, a ~ b → a = ± b.
Proof.
  have: ∀ a b, 0 < a → 0 < b → a ~ b → a = b => [a b | H a b].
  { rewrite ? lt_def => [[c [H ->]]] [d [H0 ->]].
    rewrite ? A3 INZ_eq => /assoc_N //. }
  wlog: b / 0 < b => [H0 | H0].
  - move: (trichotomy ℤ_order b 0) =>
    [/lt_neg_0 /H0 /[swap] /assoc_sign /[swap] /[apply] -> |
     [-> /assoc_zero -> | ]]; auto using pm_sym, neg_pm, pm_refl.
  - move: (trichotomy ℤ_order a 0) =>
    [/lt_neg_0 /H /(_ H0) /[swap] /assoc_sym /assoc_sign /assoc_sym
      /[swap] /[apply] <- | [-> /assoc_sym /assoc_zero -> | /H /[apply] ->]];
      auto using neg_pm, pm_refl.
Qed.

Theorem unit_pm_1 : ∀ a, unit a → a = ± 1.
Proof.
  move=> a H.
  apply assoc_pm; split; auto using (div_1_l ℤ) with Z.
Qed.

Theorem division_algorithm : ∀ a b, 0 < b → ∃ q r, b * q + r = a ∧ 0 ≤ r < b.
Proof.
  move=> a b H.
  wlog: a H / 0 < a => [x | H0].
  - case (trichotomy ℤ_order a 0) => [ | [-> | ]]; auto.
    + rewrite (lt_neg_0 ℤ_order) /= => /x =>
      /(_ H) [q [r [] /[swap] [[[H0 | <-] H1] /(f_equal (mul (-1))) H2]]];
      ring_simplify in H2; move: H2 <-.
      * exists (-q-1), (b+-r).
        rewrite ((lt_shift ℤ_order) : ∀ a b, a < b ↔ 0 < b + -a)
                /le -(le_shift ℤ_order) /ordered_rings.le.
        suff <- : r = b + - (b + - r); intuition ring.
      * exists (-q), 0.
        intuition auto using (le_refl ℤ_order : ∀ a : Z, a ≤ a); ring.
    + exists 0, 0.
      intuition auto using (le_refl ℤ_order : ∀ a : Z, a ≤ a); ring.
  - induction a as [a IHa] using strong_induction.
    case (trichotomy ℤ_order a b) =>
    [ | [-> | ]]; [ exists 0, a | exists 1, 0 | ];
      try now repeat split; try ring; rewrite /le /ordered_rings.le; intuition.
    rewrite lt_shift => /= /[dup] H1 /IHa.
    elim => [q [r [H2 H3]] | ].
    + exists (q+1), r.
      rewrite -M1 D1 (M1 _ b) -A2 (A1 _ r) A2 H2.
      intuition ring.
    + rewrite ((lt_shift ℤ_order (a+-b) a) : a+-b < a ↔ 0 < a + -(a+-b)).
      suff <- : b =  a + -(a + - b); intuition ring.
Qed.

Definition is_gcd a b d := d｜a ∧ d｜b ∧ ∀ x, x｜a → x｜b → x｜d.

Notation "'gcd(' a , b ) = d" :=
  (is_gcd a b d) (at level 80, format "'gcd(' a ','  b ')'  '='  d").

Global Hint Resolve (div_add ℤ : ∀ a b c, a｜b → a｜c → a｜b+c)
       (div_1_l ℤ : ∀ a, 1｜a) (div_refl ℤ : ∀ a, a｜a) (div_0_r ℤ : ∀ a, a｜0)
       (div_mul_l ℤ : ∀ a b c, a｜c → a｜b * c)
       (div_mul_r ℤ : ∀ a b c, a｜b → a｜b * c)
      (div_sign_neg_r ℤ : ∀ a b, a｜-b → a｜b)
      (div_sign_l_neg ℤ : ∀ a b, a｜b → -a｜b)
      (div_trans ℤ : ∀ a b c, a｜b → b｜c → a｜c)
      (mul_pos_pos ℤ_order : ∀ a b, 0 < a → 0 < b → 0 < a * b)
      (O0 ℤ_order : ∀ a b, 0 < a → 0 < b → 0 < a + b)
      (square_ne0 ℤ_order : ∀ a : Z, a ≠ 0 → 0 < a * a) : Z.

Lemma gcd_0_l : ∀ a d, gcd(0, a) = d → a ~ d.
Proof.
  move=> a d [H [H0 H1]].
  split; rewrite -/divide; auto using (div_0_r ℤ), (div_refl ℤ) with Z.
Qed.

Lemma is_gcd_sym : ∀ a b d, gcd(a, b) = d → gcd(b, a) = d.
Proof.
  move=> a b d [H [H0 H1]].
  repeat split; auto.
Qed.

Lemma gcd_0_r : ∀ a d, gcd(a, 0) = d → a ~ d.
Proof.
  auto using gcd_0_l, is_gcd_sym.
Qed.

Lemma gcd_1_l : ∀ a, gcd(1, a) = 1.
Proof.
  repeat split; auto using (div_1_l ℤ) with Z.
Qed.

Lemma gcd_1_r : ∀ a, gcd(a, 1) = 1.
Proof.
  repeat split; auto using (div_1_l ℤ) with Z.
Qed.

Lemma gcd_neg : ∀ a b d, gcd(a, b) = d ↔ gcd(a, -b) = d.
Proof.
  (rewrite /is_gcd => a b d; split =>
   [[/[swap] [[]] /(div_sign_r ℤ)] H H0 H1 |
    [/[swap] [[]] /(div_sign_neg_r ℤ) H H0 H1]]; repeat split; auto)
  => x H2 => [/(div_sign_neg_r ℤ) | /(div_sign_r ℤ)]; auto.
Qed.

Lemma neg_gcd : ∀ a b d, gcd(a, b) = d ↔ gcd(a, b) = -d.
Proof.
  (rewrite /is_gcd => a b d; split =>
   [[] /(div_sign_l ℤ) H [] /(div_sign_l ℤ) H0 H1 |
    [] /(div_sign_neg_l ℤ) H [] /(div_sign_neg_l ℤ) H0 H1]; repeat split; auto)
  => x /H1 /[apply] [/(div_sign_r_neg ℤ) | /(div_sign_neg_r ℤ)] //.
Qed.

Theorem Euclidean_algorithm :
  ∀ a b, gcd(a, b) = 1 → ∃ x y, 1 = a * x + b * y.
Proof.
  have EA_pos: ∀ a b, 0 < a → 0 < b → gcd(a, b) = 1 → ∃ x y, 1 = a * x + b * y
  => [a /[swap] H | a b].
  { induction a as [a IHa] using strong_induction => b H0 [H1 [H2]].
    elim (division_algorithm b a) => [q [r [<- [[H3 | <-] ]]] | ] //
    => [H4 H5 | /lt_def [c [_] ->]].
    - elim (IHa r (conj H3 H4) H3 a) =>
      [x [y ->] | | ] //; repeat split; auto using (div_mul_r ℤ) with Z.
      exists (y+-(q*x)), x; ring.
    - rewrite A3 A1 A3 /one /divide.
      exists 1, 0.
      rewrite M1 M3 (mul_0_r ℤ : ∀ a, a * 0 = 0) A1 A3 INZ_eq.
      apply assoc_N, conj; auto using (div_1_l ℤ), div_refl, (div_mul_r ℤ). }
  wlog: b / 0 < b => [H | H].
  - elim (trichotomy ℤ_order b 0) =>
    [/(lt_neg_0 ℤ_order) /H /[swap] /gcd_neg /[swap] /[apply] [[x [y]]] -> |
     [-> /gcd_0_r [[x]] -> | /H /[apply]]]
      /= //; [exists x, (-y) | exists x, 0]; ring.
  - elim (trichotomy ℤ_order a 0) =>
    [/(lt_neg_0 ℤ_order) /[swap] /is_gcd_sym /gcd_neg /EA_pos
      /[apply] /(_ H) [x [y]] -> |
     [-> /gcd_0_l [[x]] -> | /[swap] /EA_pos /[apply] /(_ H)]]
      /= //; [exists (-y), x | exists 0, x]; ring.
Qed.

Theorem FTA : ∀ a b c, gcd(a, b) = 1 → a｜b * c → a｜c.
Proof.
  move=> a b c H [d] /= H0.
  elim (Euclidean_algorithm a b H) => [x [y H1]].
  exists (c*x + d*y) => /=.
  rewrite -{1}(M3 c) H1 ? D1 ? (M1 _ a) ? M2 ? (M1 a) -H0; now ring_simplify.
Qed.

Definition prime p := ¬ unit p ∧ ∀ d : Z, d｜p → unit d ∨ d ~ p.

Fixpoint product L :=
  match L with
    | nil => 1
    | p :: L => p * product L
  end.

Notation "∏ L" := (product L) (at level 50) : Z_scope.

Definition prime_factorization n L :=
  n = ∏ L ∧ (∀ p, List.In p L → 0 < p ∧ prime p).

Notation "n = ∏' L" := (prime_factorization n L) (at level 50) : Z_scope.

Lemma prod_lemma : ∀ t1 t2 p,
    ∏ (t1 ++ p :: t2) = p * (∏ (t1 ++ t2)).

Proof.
  induction t1 as [| a t1 IHt1]; auto => t2 p /=.
  rewrite IHt1 ? M2 (M1 a) //.
Qed.

Theorem not_prime_divide :
  ∀ p, 1 < p → ¬ prime p → ∃ n, 1 < n < p ∧ n｜p.
Proof.
  intros p H H0.
  apply NNPP; contradict H0.
  (split; auto) => [/div_le [ | /lt_antisym | ] | d]; auto using zero_lt_1;
                     first by move: H => /[swap] -> /(lt_irrefl ℤ_order) //.
  wlog: d / 0 < d => [x | /[swap] /[dup] /div_le].
  - elim (trichotomy ℤ_order d 0) =>
    [/(lt_neg_0 ℤ_order) /x /[swap] /div_sign_l_neg /[swap] /[apply] /=
      [[/unit_sign | /assoc_sym /assoc_sign /assoc_sym]] |
     [-> /div_0_l -> | ]]; rewrite ? neg_neg; auto using (assoc_refl ℤ) with Z.
  - (elim; eauto using lt_trans, zero_lt_1) =>
    [H1 H2 /lt_0_le_1 [H3 | <-] | -> ];
      auto using (one_unit ℤ), (assoc_refl ℤ) with Z.
    exfalso; eauto.
Qed.

Theorem exists_prime_divisor :
  ∀ n, 1 < n → ∃ p, 0 < p ∧ prime p ∧ p｜n.
Proof.
  induction n as [n IH] using strong_induction => H.
  (case (classic (prime n)) => [H0 | H0]);
    [ (exists n; split) |
      elim (not_prime_divide n H H0) => [x] [] [] /[dup] /IH H1 ? ? ?; elim H1
      => [p [] ? [] | ]]; eauto using (div_trans ℤ), lt_trans, zero_lt_1 with Z.
Qed.

Lemma prime_factors_in_interval :
  ∀ p x, 0 < p → 0 < x → prime p → p｜x → ∃ k, k * p = x ∧ 0 < k < x.
Proof.
  move=> p x /[dup] H /lt_0_le_1 H0 /[swap] [[H1 H2]] /[swap] [[k ->]] /=
           /[dup] H3 /(pos_div_r ℤ_order p k H) H4.
  repeat esplit; eauto.
  move: H0 H1 H4 =>
  [/[swap] _ /(O3 ℤ_order k) /[apply] | <- /(_ (one_unit ℤ))] //.
  rewrite rings.M3_r /= //.
Qed.

Theorem exists_prime_factorization : ∀ n, 0 < n → ∃ L : list Z, n = ∏' L.
Proof.
  intros n H.
  induction n as [n H0] using strong_induction.
  destruct (T 1 n) as [[H1 [H2 H3]] | [[H1 [H2 H3]] | [H1 [H2 H3]]]].
  - apply exists_prime_divisor in H1 as [p [H4 [H5 H6]]].
    apply prime_factors_in_interval in H6 as [k [H6 H7]]; auto.
    apply H0 in H7 as [L [H7 H8]]; intuition.
    exists (p::L).
    split; auto; simpl.
    + now rewrite <-H6, H7, M1.
    + intros p0 [H1 | H1]; subst; auto.
  - now (exists nil).
  - contradiction (lt_0_1 n).
Qed.

Lemma prime_rel_prime : ∀ p a, prime p → ¬ p｜a → gcd(p,a) = 1.
Proof.
  intros p a H H0.
  repeat split; auto using (div_1_l ℤ) with Z.
  intros d H1 H2.
  apply H in H1 as [H1 | [H1 H3]]; auto.
  exfalso; eauto using (div_trans ℤ) with Z.
Qed.

Theorem Euclid's_lemma : ∀ a b p, prime p → p｜a * b → p｜a ∨ p｜b.
Proof.
  intros a b p H H0.
  destruct (classic (p｜a)); eauto using prime_rel_prime, FTA.
Qed.

Theorem Euclid_power : ∀ k a p, prime p → p｜a^k → p｜a.
Proof.
  intros k a p H H0.
  induction k using Induction.
  - rewrite -> pow_0_r in H0.
    now destruct H.
  - rewrite -> pow_succ_r in H0.
    apply Euclid's_lemma in H0; intuition.
Qed.

Theorem divisors_are_factors :
  ∀ L p x, 0 < p → 0 < x → x = ∏' L → prime p → p｜x → In p L.
Proof.
  intro L.
  induction L as [| a L IHL]; intros p x H H0 [H1 H2] [H3 H4] H5;
    subst; try now contradict H3.
  destruct (H2 a (in_eq a L)) as [H1 [H6 H7]].
  destruct (Euclid's_lemma a (∏ L) p) as [H8 | H8]; repeat split; auto.
  - apply H7 in H8 as [H8 | H8]; try contradiction.
    apply assoc_pm in H8 as [H8 | H8]; subst; try now left.
    rewrite <-(lt_neg_0 ℤ_order) in H.
    contradiction (lt_antisym ℤ_order 0 a).
  - assert (0 < (∏ L)) as H9 by (eapply (pos_div_l ℤ_order) in H0; eauto).
    apply in_cons.
    eapply IHL; unfold prime; try split; eauto using in_cons.
Qed.

Lemma one_has_unique_factorization : ∀ L, 1 = ∏' L → L = nil.
Proof.
  intros L [H H0].
  induction L as [| a L IHL]; auto.
  destruct (H0 a) as [H1 [H2 H3]]; try now intuition.
  contradict H2.
  exists (∏ L).
  now rewrite -> M1.
Qed.

Theorem unique_prime_factorization :
  ∀ x, 0 < x → ∀ L1 L2 : list Z, x = ∏' L1 → x = ∏' L2 → Permutation L1 L2.
Proof.
  intros x H.
  induction x as [x H0] using strong_induction.
  intros L1 L2 [H1 H2] [H3 H4].
  induction L1 as [ | q L1 IHL1]; simpl in *.
  - subst.
    now rewrite -> (one_has_unique_factorization _ (conj H3 H4)).
  - destruct (H2 q) as [H5 H6]; try apply in_eq.
    assert (q｜x) as H7 by
          (subst; eauto using (div_mul_r ℤ), (div_refl ℤ) with Z).
    eapply divisors_are_factors in H as H8; eauto; try (split; eauto).
    apply in_split in H8 as [l1 [l2 H8]].
    subst.
    apply prime_factors_in_interval in H7 as [k [H8 H9]]; auto.
    rewrite -> (M1 k), <-H8, prod_lemma in *.
    apply (cancellation_mul_l ℤ_ID) in H3;
      apply (cancellation_mul_l ℤ_ID) in H8;
      try now (intro; subst; contradiction (lt_irrefl ℤ_order 0)).
    apply Permutation_cons_app, (H0 k); intuition; split; auto.
    intros p H9.
    apply H4.
    rewrite -> in_app_iff in *.
    intuition.
Qed.

Theorem WOP : ∀ S : Z → Prop,
    (∀ x, S x → 0 < x) → (∃ x, 0 < x ∧ S x) → ∃ s, S s ∧ ∀ t, S t → s ≤ t.
Proof.
  intros S H [s [H0 H1]].
  apply NNPP.
  intros H2.
  revert s H0 H1.
  induction s as [s IHs] using strong_induction.
  intros H3 H4.
  contradict H2.
  exists s.
  split; auto.
  intros t H0.
  unfold le, ordered_rings.le.
  destruct (T s t) as [H1 | [H1 | [H1 [H2 H5]]]]; try tauto.
  contradiction (IHs t); auto.
Qed.

Theorem common_factor_N : ∀ a b, 0 < a → 0 < b → ∃ d, 0 < d ∧ gcd(a,b) = d.
Proof.
  intros a b H H0.
  destruct (WOP (λ z, 0 < z ∧ ∃ x y, z = a*x + b*y))
    as [d [[H1 [x [y H2]]] H3]]; try tauto.
  - exists b.
    repeat split; auto.
    exists 0, 1.
    ring.
  - exists d.
    repeat split; auto.
    + destruct (division_algorithm a d) as [q [r [H4 [[H5 | H5] H6]]]]; auto.
      replace a with (d*q + (a - d*q)) in H4 by ring.
      apply (cancellation_add ℤ) in H4.
      * destruct (H3 r); auto.
        -- split; auto.
           exists (1-x*q), (-y*q).
           rewrite -> H4, H2.
           ring.
        -- contradiction (lt_antisym ℤ_order d r).
        -- rewrite -> H7 in *.
           contradiction (lt_irrefl ℤ_order r).
      * rewrite <-H5 in *.
        exists q; simpl.
        rewrite <-H4.
        now ring_simplify.
    + destruct (division_algorithm b d) as [q [r [H4 [[H5 | H5] H6]]]]; auto.
      replace b with (d*q + (b - d*q)) in H4 by ring.
      apply (cancellation_add ℤ) in H4.
      * destruct (H3 r); auto.
        -- split; auto.
           exists (-x*q), (1-y*q).
           rewrite -> H4, H2.
           ring.
        -- contradiction (lt_antisym ℤ_order d r).
        -- rewrite -> H7 in *.
           contradiction (lt_irrefl ℤ_order r).
      * rewrite <-H5 in *.
        exists q; simpl.
        rewrite <-H4.
        now ring_simplify.
    + intros z H4 H5.
      subst.
      now apply div_mul_add.
Qed.

Theorem common_factor : ∀ a b, b ≠ 0 → ∃ d, 0 < d ∧ gcd(a,b) = d.
Proof.
  intros a b H.
  destruct (T a 0), (T b 0); intuition; rewrite -> (lt_neg_0 ℤ_order) in *.
  - destruct (common_factor_N (-a) (-b)) as [d [D1 D2]]; auto.
    exists d.
    split; auto.
    now apply gcd_neg, is_gcd_sym, gcd_neg, is_gcd_sym.
  - destruct (common_factor_N (-a) b) as [d [D1 D2]]; auto.
    exists d.
    split; auto.
    now apply is_gcd_sym, gcd_neg, is_gcd_sym.
  - exists (-b).
    repeat split; subst; auto using (div_0_r ℤ) with Z.
    + rewrite <-(div_sign_l ℤ).
      auto using (div_refl ℤ) with Z.
    + intros x H3 H5.
      now rewrite <-(div_sign_r ℤ).
  - destruct (common_factor_N a (-b)) as [d [D1 D2]]; auto.
    exists d.
    split; auto.
    now apply gcd_neg.
  - exists b.
    repeat split; subst;
      auto using (div_0_r ℤ), (div_refl ℤ) with Z.
  - destruct (common_factor_N a b) as [d [D1 D2]]; eauto.
Qed.

Theorem two_is_prime : prime 2.
Proof.
  split.
  - intros H.
    apply div_le in H as [H | H]; auto using zero_lt_1; simpl in *.
    + rewrite -> lt_def in H.
      destruct H as [c [H H0]].
      rewrite /one /INZ A1 A2 ? add_wf in H0.
      rewrite -> Zequiv, ? add_0_r, ? add_0_l, ? add_1_r in H0.
      now apply PA5, PA4 in H0.
    + unfold one, INZ in H.
      rewrite -> ? add_wf, Zequiv, ? add_0_r, add_0_l, add_1_r in H.
      now apply PA5, eq_sym, PA4 in H.
  - assert (∀ d : Z, 0 < d → d｜2 → unit d ∨ d ~ 2) as H.
    { intros d H H0.
      apply div_le in H0 as [H0 | H0].
      - apply lt_0_le_1 in H as [H | H].
        + contradiction (lt_0_1 (d+-1)).
          * rewrite <-(A4 1), ? (A1 _ (-1)).
            now apply O1.
          * rewrite <-(A3_r ℤ 1) at 2; simpl.
            rewrite <-(A4 1), A2, ? (A1 _ (-1)).
            now apply O1.
        + subst.
          left.
          now apply div_refl.
      - subst.
        auto using (assoc_refl ℤ) with Z.
      - eapply lt_trans; try exact zero_lt_1.
        rewrite <-(A3_r ℤ 1) at 1.
        eauto using O1, zero_lt_1. }
    intros d H0.
    destruct (T d 0) as [[H1 [H2 H3]] | [[H1 [H2 H3]] | [H1 [H2 H3]]]]; auto.
    + destruct (H (-d)); auto using (div_sign_l_neg ℤ) with Z.
      * now rewrite <-(lt_neg_0 ℤ_order).
      * now apply or_introl, unit_sign.
      * replace d with (--d) by ring.
        now apply or_intror, assoc_sym, assoc_sign, assoc_sym.
    + subst.
      apply div_0_l, eq_sym in H0; simpl in *.
      unfold zero, one in *.
      rewrite -> INZ_add, add_1_r in H0.
      now apply INZ_eq, PA4 in H0.
Qed.

Theorem zero_not_prime : ¬ prime 0.
Proof.
  intros [H H0].
  destruct (H0 2) as [H1 | [H1 H2]].
  - apply div_0_r.
  - now destruct two_is_prime as [H2 H3].
  - apply div_0_l in H2.
    now apply (zero_ne_2 ℤ_order).
Qed.

Theorem not_exists_prime_divisor : ∀ n, 0 ≤ n → (¬ ∃ p, prime p ∧ p｜n) → n = 1.
Proof.
  intros n [H | H] H0; simpl in *; subst.
  - destruct (T n 1) as [[H1 _] | [[_ [H1 _]] | [_ [_ H1]]]]; auto;
      try now contradiction (lt_0_1 n).
    apply exists_prime_divisor in H1 as [p [H1 [H2 H3]]].
    exfalso; eauto.
  - contradict H0.
    exists 2.
    eauto using div_0_r, two_is_prime with Z.
Qed.

Theorem prime_neg : ∀ p, prime p → prime (-p).
Proof.
  intros p [H H0].
  split.
  - contradict H.
    now apply div_sign_l in H.
  - intros d H1.
    apply div_sign_r, H0 in H1.
    intuition.
    right.
    now apply assoc_sign.
Qed.

Theorem INZ_sub : ∀ a b : N, b ≤ a → a - b = (a - b)%N.
Proof.
  intros a b H.
  unfold sub.
  replace (a : Z) with ((a-b)%N + b); try ring.
  rewrite -> INZ_add.
  f_equal.
  apply INZ_le in H.
  now rewrite -> add_comm, sub_abab.
Qed.

Section IZR.

  Variable Ring : rings.ring.
  Notation R := (elts Ring).
  Add Ring generic_ring : (ringify Ring).

  Definition IZR : Z → R.
  Proof.
    intros x.
    destruct (excluded_middle_informative (0 ≤ x)).
    - apply le_def in l.
      destruct (constructive_indefinite_description l) as [c H].
      exact (INR _ c).
    - apply lt_not_ge, lt_shift in n.
      simpl in n.
      rewrite -> A3 in n.
      apply lt_def in n.
      destruct (constructive_indefinite_description n) as [c H].
      exact (rings.neg _ (INR _ c)).
  Defined.

  Coercion IZR : Z >-> R.

  Theorem IZR_INZ : ∀ n : N, INR _ n = (n : Z).
  Proof.
    intros n.
    unfold IZR.
    destruct excluded_middle_informative;
      destruct constructive_indefinite_description.
    - ring_simplify in e.
      apply INZ_eq in e.
      congruence.
    - contradict n0.
      apply INZ_le, zero_le.
  Qed.

  Theorem IZR_zero : rings.zero _ = 0.
  Proof.
    unfold IZR.
    destruct excluded_middle_informative, constructive_indefinite_description.
    - rewrite -> A3 in e.
      apply INZ_eq in e.
      subst.
      now rewrite -> INR_zero.
    - contradict n.
      apply le_refl.
  Qed.

  Theorem IZR_one : rings.one _ = 1.
  Proof.
    unfold IZR.
    destruct excluded_middle_informative, constructive_indefinite_description.
    - rewrite -> A3 in e.
      apply INZ_eq in e.
      subst.
      now rewrite -> INR_one.
    - contradict n.
      apply or_introl, zero_lt_1.
  Qed.

  Theorem IZR_add : ∀ a b : Z, rings.add _ a b = a + b.
  Proof.
    intros a b.
    unfold IZR.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description; rewrite -> A3 in *;
        repeat destruct a0; repeat destruct a1; repeat destruct a2.
    - subst.
      rewrite -> INR_add, INZ_add in *.
      now apply f_equal, INZ_eq.
    - contradict n.
      rewrite <-(A3 0).
      now apply le_cross_add.
    - replace (INR _ x) with (rings.add Ring (INR _ x0) (INR _ x1)); try ring.
      rewrite -> ? INR_add.
      f_equal.
      rewrite <-INZ_eq, <-INZ_add, <-e0, <-e, <-H0 in *.
      ring.
    - replace (INR _ x0) with (rings.add Ring (INR _ x) (INR _ x1)); try ring.
      rewrite -> ? INR_add.
      f_equal.
      rewrite <-INZ_eq, <-INZ_add, <-e, <-H0, <-H2.
      ring.
    - replace (INR _ x0) with (rings.add Ring (INR _ x) (INR _ x1)); try ring.
      rewrite -> ? INR_add.
      f_equal.
      rewrite <-INZ_eq, <-INZ_add, <-H0, <-e, <-e0.
      ring.
    - replace (INR _ x) with (rings.add Ring (INR _ x0) (INR _ x1)); try ring.
      rewrite -> ? INR_add.
      f_equal.
      rewrite <-INZ_eq, <-INZ_add, <-H0, <-e, <-H2.
      ring.
    - rewrite <-(ordered_rings.lt_not_ge ℤ_order) in n, n0; simpl in *.
      apply le_not_gt in l; simpl in *.
      contradict l.
      rewrite <-(A3 0).
      now apply (lt_cross_add ℤ_order).
    - replace (INR _ x1) with (rings.add Ring (INR _ x) (INR _ x0)); try ring.
      rewrite -> ? INR_add.
      f_equal.
      rewrite <-INZ_eq, <-INZ_add, <-H0, <-H2, <-H4.
      ring.
  Qed.

  Theorem IZR_mul : ∀ a b : Z, rings.mul _ a b = a * b.
  Proof.
    intros a b.
    unfold IZR.
    repeat destruct excluded_middle_informative;
      repeat destruct constructive_indefinite_description; rewrite -> A3 in *;
        repeat destruct a0; repeat destruct a1; repeat destruct a2.
    - subst.
      rewrite -> INR_mul, INZ_mul in *.
      now apply f_equal, INZ_eq.
    - contradict n.
      now apply mul_nonneg_nonneg.
    - apply lt_not_ge in n; simpl in *.
      apply le_not_gt in l0; simpl in *.
      destruct l as [l | l]; simpl in *.
      + contradict l0.
        now apply (mul_pos_neg ℤ_order).
      + subst.
        rewrite -> (rings.mul_0_l ℤ) in e0; simpl in *.
        rewrite -> ? IZR_INZ, <-e, <-e0, <-IZR_zero.
        ring.
    - rewrite <-mul_neg_1_l, rings.M1, <-rings.M2, mul_neg_1_l, INR_mul.
      apply f_equal, f_equal, INZ_eq.
      rewrite <-INZ_mul, <-e, <-H0, <-H2.
      ring.
    - apply lt_not_ge in n; simpl in *.
      apply le_not_gt in l0; simpl in *.
      destruct l as [l | l]; simpl in *.
      + contradict l0.
        now apply (mul_neg_pos ℤ_order).
      + subst.
        rewrite -> (rings.mul_0_r ℤ) in e0; simpl in *.
        rewrite -> ? IZR_INZ, <-e, <-e0, <-IZR_zero.
        ring.
    - rewrite <-mul_neg_1_l, <-rings.M2, mul_neg_1_l, INR_mul.
      apply f_equal, f_equal, INZ_eq.
      rewrite <-INZ_mul, <-e, <-H0, <-H2.
      ring.
    - rewrite -> rings.mul_neg_neg, INR_mul.
      apply f_equal, INZ_eq.
      rewrite <-INZ_mul, <-H0, <-H2, <-e.
      ring.
    - contradict n1.
      left; simpl.
      apply (ordered_rings.mul_neg_neg ℤ_order); now rewrite -> lt_not_ge.
  Qed.

  Theorem IZR_neg : ∀ a : Z, rings.neg _ a = -a.
  Proof.
    intros a.
    unfold IZR.
    repeat destruct excluded_middle_informative,
    constructive_indefinite_description.
    - destruct l as [l | l], l0 as [l0 | l0]; subst; simpl in *.
      + ring_simplify in e0.
        apply (lt_neg_0 ℤ_order) in l0; simpl in *.
        contradiction (lt_antisym ℤ_order 0 (0 + INZ x)).
      + apply (lt_not_ge ℤ_order) in l.
        contradict l.
        right.
        now rewrite -> l0, A3, A1, A4 at 1.
      + contradiction (lt_irrefl ℤ_order 0).
        now replace 0 with (-0) at 2 by ring.
      + rewrite -> A3 in *.
        replace (-0) with 0 in * by ring.
        rewrite -> ? IZR_INZ, <-e, <-e0, <-IZR_zero.
        ring.
    - destruct a0 as [H H0].
      replace (--a) with a in * by ring.
      now rewrite -> A3, ? IZR_INZ, <-e, <-H0 in *.
    - destruct a0 as [H H0].
      rewrite -> A3, ? IZR_INZ, <-e, <-H0 in *.
      ring.
    - contradict n0.
      left; simpl.
      now apply (lt_neg_0 ℤ_order), (lt_not_ge ℤ_order).
  Qed.

End IZR.

Theorem INZ_pow : ∀ a b : N, ((a : Z)^b) = ((a^b)%N : Z).
Proof.
  intros a b.
  induction b using Induction.
  - now rewrite -> pow_0_r, naturals.pow_0_r.
  - now rewrite -> pow_succ_r, naturals.pow_succ_r, IHb, INZ_mul.
Qed.

Theorem INZ_sum_0 : ∀ m (f : N → N),
    (sum ℤ (λ n, f n : Z) 0 m : Z) = sum_N f 0 m.
Proof.
  intros m f.
  induction m using Induction.
  - now rewrite -> sum_0, sum_N_0.
  - rewrite -> sum_succ, sum_N_succ, IHm, INZ_add; auto using zero_le.
Qed.

Theorem INZ_sum : ∀ a b (f : N → N),
    (sum ℤ (λ n, f n : Z) a b : Z) = sum_N f a b.
Proof.
  intros a b f.
  destruct (classic (a ≤ b)%N) as [[c H] | H]; subst.
  - unfold sum, sum_N.
    rewrite -> ? iterate_shift.
    apply INZ_sum_0.
  - now rewrite <-naturals.lt_not_ge, sum_neg, sum_N_neg in *.
Qed.

Theorem INZ_prod_0 : ∀ m (f : N → N),
    (prod ℤ (λ n, f n : Z) 0 m : Z) = prod_N f 0 m.
Proof.
  intros m f.
  induction m using Induction.
  - now rewrite -> prod_0, prod_N_0.
  - rewrite -> prod_succ, prod_N_succ, IHm, INZ_mul; auto using zero_le.
Qed.

Theorem INZ_prod : ∀ a b (f : N → N),
    (prod ℤ (λ n, f n : Z) a b : Z) = prod_N f a b.
Proof.
  intros a b f.
  destruct (classic (a ≤ b)%N) as [[c H] | H]; subst.
  - unfold prod, prod_N.
    rewrite -> ? iterate_shift.
    apply INZ_prod_0.
  - now rewrite <-naturals.lt_not_ge, prod_neg, prod_N_neg in *.
Qed.

Definition even (x : Z) := 2｜x.
Definition odd (x : Z) := ¬ even x.

Theorem odd_classification : ∀ x, odd x ↔ ∃ k, x = 2 * k + 1.
Proof.
  split; intros H.
  - destruct (division_algorithm x 2) as [q [r [H0 H1]]];
      try apply (ordered_rings.zero_lt_2 ℤ_order).
    exists q.
    rewrite <-H0.
    f_equal.
    destruct (integers.T r 1) as [[H2 _] | [[_ [H2_]] | [_ [_ H2]]]].
    + destruct H1 as [[H1 | H1] _]; simpl in *.
      * contradiction (lt_0_1 r).
      * subst.
        contradiction H.
        exists q; simpl.
        now replace (2*q+0) with (q*2) by ring.
    + congruence.
    + destruct H1 as [_ H1].
      contradiction (lt_0_1 (r+(-1%Z))%Z).
      * now rewrite <-(ordered_rings.lt_shift ℤ_order).
      * rewrite <-(integers.A3 1) at 2.
        rewrite -> (integers.A1 0), <-(integers.A4 1), integers.A2,
        ? (integers.A1 _ (-1)).
        now apply (ordered_rings.O1 ℤ_order).
  - destruct H as [k H].
    subst.
    intros [x H]; simpl in *.
    destruct two_is_prime as [H0 H1].
    contradict H0.
    exists (x+-k); simpl.
    rewrite -> integers.D1, <-H.
    now ring_simplify.
Qed.

Theorem odd_add : ∀ a b, odd a → odd b → even (a+b).
Proof.
  intros a b H H0.
  apply odd_classification in H as [k H], H0 as [l H0].
  subst.
  exists (k+l+1).
  simpl.
  now replace ((k+l+1)*2) with (2*k+1+(2*l+1)) by ring.
Qed.

Definition div : Z → Z → Z.
Proof.
  intros a b.
  destruct (excluded_middle_informative (b｜a)).
  - destruct (constructive_indefinite_description d) as [k].
    exact k.
  - exact 0.
Defined.

Infix "/" := div : Z_scope.

Theorem div_inv_refl : ∀ a, a ≠ 0 → a/a = 1.
Proof.
  intros a H.
  unfold div.
  destruct excluded_middle_informative.
  - destruct constructive_indefinite_description.
    rewrite <-(M3 a), ? (M1 a) in e at 1.
    apply (cancellation_mul_r ℤ_ID) in e; auto.
  - contradict n.
    auto using div_refl with Z.
Qed.

Theorem div_inv_l : ∀ a b, b｜a → b * (a/b) = a.
Proof.
  intros a b H.
  unfold div.
  destruct excluded_middle_informative; try tauto.
  destruct constructive_indefinite_description.
  now rewrite -> M1.
Qed.

Theorem div_inv_r : ∀ a b, b｜a → (a/b) * b = a.
Proof.
  intros a b H.
  now rewrite -> M1, div_inv_l.
Qed.

Theorem div_spec : ∀ a b k, b｜a → b ≠ 0 → a/b = k ↔ a = k * b.
Proof.
  intros a b k H H0.
  unfold div.
  split; intros H1; destruct excluded_middle_informative; try tauto;
    try destruct constructive_indefinite_description; subst; auto.
  now apply (cancellation_mul_r ℤ_ID) in e.
Qed.

Theorem mul_div : ∀ a b d, d｜b → d ≠ 0 → a * (b / d) = (a * b) / d.
Proof.
  intros a b d H H0.
  apply eq_sym, div_spec; auto.
  - destruct H as [k H].
    exists (k*a).
    rewrite -> H.
    simpl; now ring_simplify.
  - now rewrite <-M2, div_inv_r.
Qed.

Theorem div_nonneg : ∀ a b, 0 ≤ a → 0 < b → 0 ≤ a / b.
Proof.
  intros a b H H0.
  unfold div.
  destruct excluded_middle_informative; try apply (le_refl ℤ_order).
  destruct constructive_indefinite_description; subst; simpl in *.
  rewrite -> M1 in H.
  eapply pos_mul_nonneg; eauto.
Qed.

Theorem div_pos : ∀ a b, b｜a → 0 < a → 0 < b → 0 < a / b.
Proof.
  intros a b H H0 H1.
  unfold div.
  destruct excluded_middle_informative; try tauto.
  destruct constructive_indefinite_description; simpl in *; subst.
  eapply (pos_div_r ℤ_order); eauto.
Qed.

Theorem div_div : ∀ a b, b｜a → a ≠ 0 → b ≠ 0 → a / (a / b) = b.
Proof.
  intros a b H H0 H1.
  apply div_spec; auto using eq_sym, div_inv_l.
  - exists b.
    now apply eq_sym, div_inv_l.
  - contradict H0.
    rewrite <-(div_inv_l a b); auto.
    now rewrite -> H0, (mul_0_r ℤ).
Qed.

Theorem gcd_exists : ∀ a b, ∃ d, gcd(a, b) = d.
Proof.
  intros a b.
  wlog: a b / 0 < a ∧ 0 < b.
  - intros x.
    destruct (T 0 a) as [[H _] | [[_ [H _]] | [_ [_ H]]]], (T 0 b)
        as [[H0 _] | [[_ [H0 _]] | [_ [_ H0]]]]; subst; auto;
      try (now (exists a; repeat split; auto using div_0_r with Z));
      try (now (exists b; repeat split; auto using div_0_r with Z));
      try (now (exists 0; repeat split; auto using div_0_r with Z));
      rewrite -> (lt_neg_0 ℤ_order) in *;
      destruct (x _ _ (conj H H0)) as [d H1]; exists d.
    + now rewrite -> gcd_neg.
    + now apply is_gcd_sym; rewrite -> gcd_neg; apply is_gcd_sym.
    + now rewrite gcd_neg; apply is_gcd_sym; rewrite gcd_neg; apply is_gcd_sym.
  - revert b.
    induction a using strong_induction.
    intros b [H0 H1].
    apply (division_algorithm b) in H0 as H2.
    destruct H2 as [q [r [H2 [[H3 | H3] H4]]]]; simpl in *; subst.
    + destruct (H r (conj H3 H4) a) as [d [H5 [H6 H7]]]; auto.
      exists d.
      repeat split; auto.
      * apply div_add; try apply div_mul_r; auto.
      * intros x H2 H8.
        apply H7; auto.
        replace r with ((a*q+r) + a*(-q)) by ring.
        apply div_add; try apply div_mul_r; auto.
    + exists a.
      repeat split; try intros; try ring_simplify; auto using div_refl with Z.
Qed.

Theorem pos_gcd_exists : ∀ a b, ∃ d, 0 ≤ d ∧ gcd(a, b) = d.
Proof.
  intros a b.
  destruct (gcd_exists a b) as [d H], (classic (0 ≤ d)) as [H0 | H0]; eauto.
  exists (-d).
  rewrite <-neg_gcd.
  split; auto.
  now apply or_introl, lt_neg_0, lt_not_ge.
Qed.

Definition gcd : Z → Z → Z.
Proof.
  intros a b.
  destruct (constructive_indefinite_description (pos_gcd_exists a b)) as [d].
  exact d.
Defined.

Theorem is_gcd_gcd : ∀ a b, gcd(a, b) = gcd a b.
Proof.
  intros a b.
  unfold gcd.
  now destruct constructive_indefinite_description.
Qed.

Theorem gcd_l_div : ∀ a b, gcd a b｜a.
Proof.
  intros a b.
  unfold gcd.
  now destruct constructive_indefinite_description as [d [H [H0 [H1 H2]]]].
Qed.

Theorem gcd_r_div : ∀ a b, gcd a b｜b.
Proof.
  intros a b.
  unfold gcd.
  now destruct constructive_indefinite_description as [d [H [H0 [H1 H2]]]].
Qed.

Theorem gcd_spec : ∀ a b x, x｜a → x｜b → x｜gcd a b.
Proof.
  intros a b.
  unfold gcd.
  now destruct constructive_indefinite_description as [d [H [H0 [H1 H2]]]].
Qed.

Theorem gcd_nonneg : ∀ a b, 0 ≤ gcd a b.
Proof.
  intros a b.
  unfold gcd.
  now destruct constructive_indefinite_description as [d [H [H0 [H1 H2]]]].
Qed.

Theorem pm_pos : ∀ a b, a = ± b → 0 ≤ a → 0 ≤ b → a = b.
Proof.
  intros a b [H | H] H0 H1; auto; subst.
  replace b with 0; try ring.
  apply (ordered_rings.le_antisymm ℤ_order); auto.
  now apply le_neg_0.
Qed.

Theorem gcd_is_gcd : ∀ a b d, gcd(a, b) = d → 0 ≤ d → gcd a b = d.
Proof.
  intros a b d [H [H0 H1]] H2.
  apply pm_pos; auto using gcd_nonneg.
  apply assoc_pm, conj; fold divide; auto using gcd_l_div, gcd_r_div, gcd_spec.
Qed.

Theorem gcd_refl : ∀ a, 0 ≤ a → gcd a a = a.
Proof.
  intros a H.
  apply gcd_is_gcd; auto.
  repeat split; auto using div_refl with Z.
Qed.

Theorem gcd_l_0 : ∀ a, gcd 0 a = ± a.
Proof.
  intros a.
  destruct (classic (0 ≤ a)).
  - apply or_introl, gcd_is_gcd; auto.
    repeat split; auto using div_0_r with Z.
  - apply or_intror, gcd_is_gcd; auto.
    repeat split; rewrite <-? (div_sign_l ℤ); auto using div_refl, (div_0_r ℤ).
    + intros x H0 H1.
      now rewrite <-(div_sign_r ℤ).
    + left.
      now apply lt_neg_0, lt_not_ge.
Qed.

Theorem gcd_sym : ∀ a b, gcd a b = gcd b a.
Proof.
  intros a b.
  apply pm_pos; auto using gcd_nonneg.
  apply assoc_pm.
  split; apply gcd_spec; auto using gcd_l_div, gcd_r_div.
Qed.

Theorem gcd_r_0 : ∀ a, gcd a 0 = ± a.
Proof.
  intros a.
  rewrite -> gcd_sym.
  apply gcd_l_0.
Qed.

Theorem gcd_l_1 : ∀ a, gcd 1 a = 1.
Proof.
  intros a.
  apply gcd_is_gcd; auto using gcd_1_l.
  apply or_introl, zero_lt_1.
Qed.

Theorem gcd_r_1 : ∀ a, gcd a 1 = 1.
Proof.
  intros a.
  now rewrite -> gcd_sym, gcd_l_1.
Qed.

Theorem gcd_pos : ∀ a b, a ≠ 0 → gcd a b ≠ 0.
Proof.
  intros a b H.
  contradict H.
  pose proof gcd_l_div a b.
  rewrite -> H in H0.
  now apply div_0_l in H0.
Qed.

Theorem gcd_rel_prime :
  ∀ a b, a ≠ 0 → b ≠ 0 → gcd(a / gcd a b, b / gcd a b) = 1.
Proof.
  intros a b H H0.
  repeat split; auto using div_1_l with Z.
  intros x [k H1] [l H2]; simpl in *.
  apply (div_spec a (gcd a b)) in H1; apply (div_spec b (gcd a b)) in H2;
    auto using gcd_l_div, gcd_r_div, gcd_pos.
  rewrite <-M2 in H1, H2.
  assert (x * gcd a b｜gcd a b) as [z H3].
  { apply is_gcd_gcd; [ now (exists k) | now (exists l) ]. }
  exists z.
  apply (cancellation_mul_r ℤ_ID (gcd a b)); simpl in *.
  - now apply gcd_pos.
  - now rewrite -> M3, <-M2.
Qed.

Theorem Euclidean_gcd : ∀ a b, ∃ x y, a * x + b * y = gcd a b.
Proof.
  intros a b.
  destruct (classic (a = 0)) as [H | H], (classic (b = 0)) as [H0 | H0]; subst.
  - exists 0, 0.
    rewrite -> (mul_0_l ℤ), A3.
    destruct (gcd_l_0 0) as [H | H]; replace (-0) with 0 in * by ring; auto.
  - destruct (gcd_l_0 b) as [H | H]; rewrite -> H.
    + exists 0, 1; ring.
    + exists 0, (-1); ring.
  - destruct (gcd_r_0 a) as [H0 | H0]; rewrite -> H0.
    + exists 1, 0; ring.
    + exists (-1), 0; ring.
  - eapply gcd_rel_prime in H; eauto.
    apply Euclidean_algorithm in H as [x [y H]].
    rewrite -> gcd_sym in H.
    exists y, x.
    rewrite <-(M3 (gcd a b)), H, D1, ? (M1 _ (gcd a b)), ? M2, ? div_inv_l;
      auto using gcd_l_div, gcd_r_div; ring.
Qed.

Theorem rel_prime_mul : ∀ a b c, gcd(a, b) = 1 → a｜c → b｜c → a * b｜c.
Proof.
  intros a b c H [m H0] [n H1].
  apply Euclidean_algorithm in H as [x [y H]].
  rewrite <-(M3 c), H, D1, ? (M1 _ c), ? M2.
  apply div_add; apply div_mul_r;
    [ exists n; rewrite H1 | exists m; rewrite H0 ]; simpl; now ring_simplify.
Qed.

Lemma gcd_mul_rel_prime : ∀ a b c, gcd(b, c) = 1 → gcd(gcd a b, gcd a c) = 1.
Proof.
  intros a b c H.
  repeat split; auto using div_1_l with Z.
  intros x H0 H1.
  apply H.
  - clear H1; eapply div_trans; eauto; apply gcd_r_div.
  - clear H0; eapply div_trans; eauto; apply gcd_r_div.
Qed.

Theorem gcd_r_mul :
  ∀ a b c, gcd(b, c) = 1 → gcd(a, b * c) = gcd a b * gcd a c.
Proof.
  intros a b c H.
  repeat split;
    try (apply rel_prime_mul; auto using gcd_mul_rel_prime, gcd_l_div);
    [ apply div_mul_r | apply div_mul_l | ]; try apply gcd_r_div.
  intros x H0 H1.
  destruct (Euclidean_gcd a b) as
      [x1 [y1 H2]], (Euclidean_gcd a c) as [x2 [y2 H3]]; rewrite <-H2, <-H3.
  replace ((a*x1+b*y1)*(a*x2+c*y2)) with
      (a*(a*x1*x2+b*x2*y1+c*x1*y2)+(b*c)*(y1*y2)) by ring.
  now apply div_add; apply div_mul_r.
Qed.

Theorem gcd_mul_r : ∀ a b c, gcd(b, c) = 1 → gcd a (b*c) = gcd a b * gcd a c.
Proof.
  intros a b c H.
  apply gcd_is_gcd; auto using gcd_r_mul.
  apply mul_nonneg_nonneg; apply gcd_nonneg.
Qed.

Theorem gcd_l_mul :
  ∀ a b c, gcd(a, b) = 1 → gcd(a * b, c) = gcd a c * gcd b c.
Proof.
  intros a b c H.
  apply is_gcd_sym.
  rewrite -> ? (gcd_sym _ c).
  now apply gcd_r_mul.
Qed.

Theorem gcd_mul_l : ∀ a b c, gcd(a, b) = 1 → gcd (a*b) c = gcd a c * gcd b c.
Proof.
  intros a b c H.
  now rewrite -> gcd_sym, gcd_mul_r, ? (gcd_sym c).
Qed.

Theorem gcd_pow_l : ∀ a b k, gcd(a, b) = 1 → gcd (a^k) b = 1.
Proof.
  intros a b k H.
  apply not_exists_prime_divisor; auto using gcd_nonneg.
  intros [p [H0 H1]].
  pose proof H0 as [H2 H3].
  contradict H2.
  apply H; [ eapply Euclid_power; auto | ];
    eapply div_trans; eauto; fold divide; auto using gcd_l_div, gcd_r_div.
Qed.

Theorem gcd_pow_r : ∀ a b k, gcd(a, b) = 1 → gcd a (b^k) = 1.
Proof.
  intros a b k H.
  rewrite -> gcd_sym.
  now apply gcd_pow_l, is_gcd_sym.
Qed.

Theorem div_l_gcd : ∀ a b, 0 ≤ a → a｜b → gcd a b = a.
Proof.
  intros a b H H0.
  apply gcd_is_gcd; auto.
  repeat split; auto using (div_refl ℤ) with Z.
Qed.

Theorem div_r_gcd : ∀ a b, 0 ≤ b → b｜a → gcd a b = b.
Proof.
  intros a b H H0.
  apply gcd_is_gcd; auto.
  repeat split; auto using (div_refl ℤ) with Z.
Qed.

Definition is_lcm (a b m : Z) := a｜m ∧ b｜m ∧ ∀ x, a｜x → b｜x → m｜x.

Notation "'lcm(' a , b ) = m" :=
  (is_lcm a b m) (at level 80, format "'lcm(' a ','  b ')'  '='  m").

Lemma lcm_0_l : ∀ a, lcm(0, a) = 0.
Proof.
  intros a.
  split; fold divide; auto using (div_0_r ℤ), (div_refl ℤ) with Z.
Qed.

Lemma is_lcm_sym : ∀ a b m, lcm(a, b) = m → lcm(b, a) = m.
Proof.
  intros a b d [H [H0 H1]].
  repeat split; auto.
Qed.

Lemma lcm_0_r : ∀ a, lcm(a, 0) = 0.
Proof.
  auto using is_lcm_sym, lcm_0_l.
Qed.

Lemma lcm_1_l : ∀ a, lcm(1, a) = a.
Proof.
  intros a.
  repeat split; auto using (div_1_l ℤ) with Z.
Qed.

Lemma lcm_1_r : ∀ a, lcm(a, 1) = a.
Proof.
  intros a.
  repeat split; auto using (div_1_l ℤ) with Z.
Qed.

Lemma lcm_neg : ∀ a b m, lcm(a, b) = m ↔ lcm(a, -b) = m.
Proof.
  intros a b m.
  split; intros [H [H0 H1]].
  - repeat split; try rewrite <-(div_sign_l ℤ); auto.
    intros x H2 H3.
    rewrite <-(div_sign_l ℤ) in *.
    auto.
  - repeat split; try rewrite <-(div_sign_l ℤ) in H0; auto.
    intros x H2 H3.
    rewrite -> (div_sign_l ℤ) in H3.
    auto.
Qed.

Lemma neg_lcm : ∀ a b m, lcm(a, b) = m ↔ lcm(a, b) = -m.
Proof.
  intros a b d.
  split; intros [H [H0 H1]]; repeat split; try (now rewrite <-(div_sign_r ℤ));
    try (now rewrite -> (div_sign_r ℤ)); intros x H2 H3;
      [ rewrite <-(div_sign_l ℤ) | rewrite -> (div_sign_l ℤ) ]; now apply H1.
Qed.

Theorem lcm_gcd_ident : ∀ a b, a ≠ 0 → b ≠ 0 → lcm(a, b) = (a*b) / gcd a b.
Proof.
  intros a b H H0.
  assert (gcd a b ≠ 0) as H1.
  { contradict H.
    pose proof gcd_l_div a b.
    rewrite -> H in H1.
    now apply div_0_l in H1. }
  unfold div.
  destruct excluded_middle_informative as [y | n].
  2: { contradict n.
       apply div_mul_r, gcd_l_div. }
  destruct constructive_indefinite_description as [k]; simpl in *.
  repeat split; rewrite -> (M1 k) in e.
  - exists (b / gcd a b); simpl.
    rewrite -> M1, mul_div; auto using gcd_r_div.
    apply eq_sym, div_spec; auto.
    now rewrite -> e, M1.
  - exists (a / gcd a b); simpl.
    rewrite -> M1, mul_div; auto using gcd_l_div.
    apply eq_sym, div_spec; try rewrite -> M1; auto.
    now rewrite -> e, M1.
  - intros x H2 H3.
    set (d := gcd a b) in *.
    assert (d｜x) as H4.
    { clear y; eapply div_trans; eauto; apply gcd_r_div. }
    assert ((a/d) * (b/d)｜x/d) as [z H5].
    { apply rel_prime_mul; try apply gcd_rel_prime; auto.
      - destruct H2 as [z H2].
        exists z.
        apply div_spec; auto.
        rewrite <-M2, div_inv_r; auto.
        apply gcd_l_div.
      - destruct H3 as [z H3].
        exists z.
        apply div_spec; auto.
        rewrite <-M2, div_inv_r; auto.
        apply gcd_r_div. }
    apply (div_spec x d) in H5; auto.
    rewrite <-? M2, div_inv_r, (M1 _ b), mul_div, (M1 b), e, (M1 _ k),
    <-mul_div, div_inv_refl, (M1 k), M3 in H5; try (now (exists z));
      eauto using gcd_l_div, gcd_r_div, div_refl with Z.
Qed.

Theorem lcm_exists : ∀ a b, ∃ m, lcm(a, b) = m.
Proof.
  intros a b.
  destruct (classic (a = 0)) as [H | H], (classic (b = 0)) as [H0 | H0];
    subst; eauto using lcm_0_l, lcm_0_r, lcm_gcd_ident.
Qed.

Theorem pos_lcm_exists : ∀ a b, ∃ m, 0 ≤ m ∧ lcm(a, b) = m.
Proof.
  intros a b.
  destruct (lcm_exists a b) as [m H], (classic (0 ≤ m)) as [H0 | H0]; eauto.
  exists (-m).
  rewrite <-neg_lcm.
  split; auto.
  now apply or_introl, lt_neg_0, lt_not_ge.
Qed.

Definition lcm : Z → Z → Z.
Proof.
  intros a b.
  destruct (constructive_indefinite_description (pos_lcm_exists a b)) as [m].
  exact m.
Defined.

Theorem is_lcm_lcm : ∀ a b, lcm(a, b) = lcm a b.
Proof.
  intros a b.
  unfold lcm.
  now destruct constructive_indefinite_description.
Qed.

Theorem lcm_div_l : ∀ a b, a｜lcm a b.
Proof.
  intros a b.
  unfold lcm.
  now destruct constructive_indefinite_description as [d [H [H0 [H1 H2]]]].
Qed.

Theorem lcm_div_r : ∀ a b, b｜lcm a b.
Proof.
  intros a b.
  unfold lcm.
  now destruct constructive_indefinite_description as [d [H [H0 [H1 H2]]]].
Qed.

Theorem lcm_l_0 : ∀ a, lcm 0 a = 0.
Proof.
  intros a.
  apply (div_0_l ℤ), lcm_div_l.
Qed.

Theorem lcm_r_0 : ∀ a, lcm a 0 = 0.
Proof.
  intros a.
  apply (div_0_l ℤ), lcm_div_r.
Qed.

Theorem lcm_spec : ∀ a b x, a｜x → b｜x → lcm a b｜x.
Proof.
  intros a b.
  unfold lcm.
  now destruct constructive_indefinite_description as [d [H [H0 [H1 H2]]]].
Qed.

Theorem lcm_nonneg : ∀ a b, 0 ≤ lcm a b.
Proof.
  intros a b.
  unfold lcm.
  now destruct constructive_indefinite_description as [d [H [H0 [H1 H2]]]].
Qed.

Theorem lcm_is_lcm : ∀ a b m, lcm(a, b) = m → 0 ≤ m → lcm a b = m.
Proof.
  intros a b d [H [H0 H1]] H2.
  apply pm_pos; auto using lcm_nonneg.
  apply assoc_pm, conj; fold divide; auto using lcm_div_l, lcm_div_r, lcm_spec.
Qed.

Theorem lcm_sym : ∀ a b, lcm a b = lcm b a.
Proof.
  intros a b.
  apply pm_pos; auto using lcm_nonneg.
  apply assoc_pm.
  split; apply lcm_spec; auto using lcm_div_l, lcm_div_r.
Qed.

Theorem lcm_l_1 : ∀ a, 0 ≤ a → lcm 1 a = a.
Proof.
  intros a H.
  apply lcm_is_lcm; auto using lcm_1_l.
Qed.

Theorem lcm_r_1 : ∀ a, 0 ≤ a → lcm a 1 = a.
Proof.
  intros a H.
  apply lcm_is_lcm; auto using lcm_1_r.
Qed.

Theorem lcm_prod : ∀ a b, lcm a b｜a * b.
Proof.
  intros a b.
  apply lcm_spec; auto using div_mul_r, div_refl with Z.
Qed.

Theorem lcm_pos : ∀ a b, a ≠ 0 → b ≠ 0 → lcm a b ≠ 0.
Proof.
  intros a b H H0.
  intros H1.
  eapply (ne0_cancellation ℤ_ID) in H; eauto.
  contradict H.
  rewrite -> M1; apply (div_0_l ℤ); simpl.
  rewrite <-H1.
  apply lcm_spec; auto using div_mul_l, div_mul_r, div_refl with Z.
Qed.

Theorem gcd_lcm_ident : ∀ a b, 0 ≤ a → 0 ≤ b → a * b = gcd a b * lcm a b.
Proof.
  intros a b [H | H] [H0 | H0]; subst;
    rewrite -> ? lcm_l_0, ? lcm_r_0, ? (mul_0_r ℤ), ? (mul_0_l ℤ); auto.
  pose proof is_lcm_lcm a b as H1.
  pose proof lcm_gcd_ident a b as H2.
  rewrite -> (M1 (gcd a b)).
  apply div_spec.
  - apply div_mul_r, gcd_l_div.
  - now apply gcd_pos, (pos_ne_0 ℤ_order).
  - apply pm_pos; auto using lcm_nonneg.
    + apply assoc_pm, conj.
      * apply H2; try (now apply (pos_ne_0 ℤ_order));
          auto using lcm_div_l, lcm_div_r.
      * apply H1; apply H2; now apply (pos_ne_0 ℤ_order).
    + rewrite <-mul_div;
        auto using (pos_ne_0 ℤ_order a H : a ≠ 0), gcd_pos, gcd_r_div.
      apply mul_nonneg_nonneg; try (now left; intuition).
      apply div_nonneg; try (now left).
      destruct (gcd_nonneg a b); auto; contradiction (gcd_pos a b); auto.
      intros H4.
      subst.
      contradiction (ordered_rings.lt_irrefl ℤ_order 0).
Qed.

Lemma prime_quotients :
  ∀ p x, 0 < p → 0 < x → prime p → p｜x → 0 < x/p < x.
Proof.
  intros p x H H0 H1 H2.
  unfold div.
  destruct excluded_middle_informative; try tauto.
  destruct constructive_indefinite_description; simpl in *.
  apply prime_factors_in_interval in H2 as [k [H2 H3]]; auto.
  replace x0 with k; auto; subst.
  eapply (cancellation_mul_r ℤ_ID); eauto.
  intros H4; subst; simpl in *.
  contradiction (lt_irrefl ℤ_order 0).
Qed.

Theorem valuation_construction :
  ∀ p m, prime p → m ≠ 0 → exists ! k : N, p^k｜m ∧ ¬ p^(k+1)｜m.
Proof.
  move=> p m; wlog: p m / 0 < p.
  { intros x H H0.
    destruct (T 0 p) as [[H1 _] | [[_ [H1 _]] | [_ [_ H1]]]]; subst; try tauto;
      auto; try now contradiction zero_not_prime.
  apply (ordered_rings.lt_neg_0 ℤ_order) in H1; simpl in *.
  eapply x in H1 as [k [[H1 H2] H3]]; eauto using prime_neg.
  exists k.
  repeat split.
    - destruct (pow_sign_l ℤ p k) as [H4 | H4]; simpl in *; rewrite -> H4 in *;
        auto; now apply div_sign_l.
    - contradict H2.
      destruct (pow_sign_l ℤ p (k+1)) as [H4 | H4]; simpl in *;
        rewrite -> H4 in *; auto; now apply div_sign_l in H2.
    - intros x' [H4 H5].
      apply H3, conj.
      + destruct (pow_sign_l ℤ p x') as [H6 | H6]; simpl in *;
          rewrite -> H6 in *; auto; now apply div_sign_l in H4.
      + contradict H5.
        destruct (pow_sign_l ℤ p (x'+1)) as [H6 | H6]; simpl in *;
          rewrite -> H6 in *; auto; now apply div_sign_l. }
  wlog: m / 0 < m.
  { intros x H H0 H1.
    destruct (T 0 m) as [[H2 _] | [[_ [H2 _]] | [_ [_ H2]]]]; subst;
      try tauto; auto.
    apply (ordered_rings.lt_neg_0 ℤ_order) in H2; simpl in *.
    eapply x in H2 as [k [[H2 H3] H4]]; eauto.
    exists k.
    repeat split.
    - now apply div_sign_r.
    - contradict H3.
      now apply div_sign_r in H3.
    - intros x' [H5 H6].
      rewrite -> (div_sign_r ℤ) in H5, H6.
      now apply H4.
    - contradict H1; ring [H1]. }
  move: p m.
  induction m using strong_induction.
  intros H0 H1 H2 H3.
  destruct (classic (p｜m)) as [H4 | H4].
  - apply prime_quotients in H4 as H5; auto.
    apply H in H5 as [k [[H5 H6]]]; auto using div_pos.
    2: { apply (pos_ne_0 ℤ_order); tauto. }
    exists (k+1)%N.
    assert (p^(k+1)｜m) as H8.
    { destruct H5 as [d H5]; simpl in *.
      exists d.
      rewrite -> add_1_r, pow_succ_r, M2, <-H5, div_inv_r; auto. }
    assert (¬ p ^ (k + 1 + 1)｜m) as H9.
    { contradict H6.
      destruct H6 as [d H6].
      exists d.
      rewrite -> H6, add_1_r, pow_succ_r, <-? mul_div, div_inv_refl, (M1 _ 1),
      M3; auto using (pos_ne_0 ℤ_order p H1 : p ≠ 0), div_refl with Z. }
    repeat split; auto.
    intros x' [H10 H11].
    apply naturals.le_antisymm; apply naturals.le_not_gt.
    + contradict H11; clear H10.
      eapply div_trans; eauto.
      rewrite -> add_1_r, <-le_lt_succ in H11.
      destruct H11 as [z H11]; subst.
      exists (p^z).
      rewrite -> ? pow_add_r; simpl; now ring_simplify.
    + contradict H9.
      eapply div_trans; eauto.
      rewrite -> S_lt, <-le_lt_succ, <-add_1_r in H9.
      destruct H9 as [z H9]; subst.
      exists (p^z).
      rewrite -> ? pow_add_r; simpl; now ring_simplify.
  - exists 0%N.
    repeat split; rewrite -> ? pow_0_r, ? add_0_l, ? pow_1_r;
      auto using div_1_l with Z.
    intros x' [H5 H6].
    apply naturals.le_antisymm; auto using zero_le.
    rewrite -> naturals.le_not_gt.
    contradict H4.
    eapply div_trans; eauto.
    apply nonzero_lt, succ_0 in H4 as [z H4]; subst.
    rewrite -> pow_succ_r.
    apply div_mul_l, div_refl.
Qed.

Definition v : Z → Z → N.
Proof.
  intros p m.
  destruct (excluded_middle_informative (prime p)).
  - destruct (excluded_middle_informative (m = 0)).
    + exact 0%N.
    + destruct
        (constructive_definite_description _ (valuation_construction _ _ p0 n))
        as [k].
      exact k.
  - exact 0%N.
Defined.

Section Valuations.

  Variable p : Z.
  Hypothesis prime_p : prime p.

  Theorem prime_power_nonzero : ∀ n, p^n ≠ 0.
  Proof.
    intros n.
    apply (pow_ne_0 ℤ_ID).
    intros H.
    subst.
    contradiction zero_not_prime.
  Qed.

  Theorem val_mul : ∀ a b, a ≠ 0 → b ≠ 0 → v p (a * b) = (v p a + v p b)%N.
  Proof.
    intros a b H H0.
    unfold v.
    repeat destruct excluded_middle_informative; try tauto;
      try (apply (integral_domains.cancellation ℤ_ID) in e; tauto).
    repeat destruct constructive_definite_description; intuition.
    apply naturals.le_antisymm; apply naturals.le_not_gt; intros H7;
      rewrite -> S_lt, <-le_lt_succ, <-add_1_r in H7;
      destruct H7 as [z H7].
    - absurd (p^(x0+x1+1)｜a*b).
      + intros [k H8].
        rewrite <-(div_inv_r a (p^x0)), <-(div_inv_r b (p^x1)), ? pow_add_r,
        pow_1_r, <-M2, (M1 _ p), (M2 (p^x0)), (M1 (p^x0)), ? M2 in H8; auto.
        do 2 apply (cancellation_mul_r ℤ_ID) in H8;
          auto using prime_power_nonzero.
        assert (p｜(a / p ^ x0) * (b / p ^ x1)) as H9 by now (exists k).
        apply Euclid's_lemma in H9 as [[d H9] | [d H9]]; auto; simpl in *;
          [ contradict H4 | contradict H6 ]; exists d;
            rewrite -> add_1_r, pow_succ_r, (M1 _ p), M2, <-H9, div_inv_r; auto.
      + eapply div_trans; eauto.
        exists (p^z).
        rewrite <-H7, ? pow_add_r; simpl; now ring_simplify.
    - contradict H2.
      exists (p^z * (a/(p^x0)) * (b/(p^x1))).
      rewrite -> (M1 _ (p^(x+1))), ? M2, <-(pow_add_r ℤ), H7, pow_add_r, <-? M2,
      (M2 (p^x1)), (M1 (p^x1)), ? M2, div_inv_l, <-M2, div_inv_l; auto.
  Qed.

  Theorem val_lower_bound : ∀ x m, m ≠ 0 → p^x｜m ↔ (x ≤ v p m)%N.
  Proof.
    split; intros H0; unfold v in *;
      repeat destruct excluded_middle_informative; try tauto;
        destruct constructive_definite_description; intuition.
    - apply naturals.le_not_gt.
      contradict H2.
      rewrite -> S_lt, <-le_lt_succ, <-add_1_r in H2.
      destruct H2 as [z H2].
      clear H1; eapply div_trans; eauto.
      exists (p^z).
      rewrite <-H2, ? pow_add_r; simpl; now ring_simplify.
    - destruct H0 as [z H0].
      exists (p^z * (m/p^x0)).
      rewrite -> M1, M2, <-(pow_add_r ℤ), H0, div_inv_l; auto.
  Qed.

  Theorem val_upper_bound : ∀ x m, m ≠ 0 → ¬ p^x｜m ↔ (v p m < x)%N.
  Proof.
    split; intros H0; unfold v in *;
      repeat destruct excluded_middle_informative; try tauto;
        destruct constructive_definite_description; intuition.
    - apply naturals.lt_not_ge.
      contradict H0.
      destruct H0 as [z H0].
      exists (p^z * (m/p^x0)).
      rewrite -> M1, M2, <-(pow_add_r ℤ), H0, div_inv_l; auto.
    - contradict H3.
      rewrite -> S_lt, <-le_lt_succ, <-add_1_r in H0.
      destruct H0 as [z H0].
      exists (p^z * (m/p^x)).
      rewrite -> M1, M2, <-(pow_add_r ℤ), H0, div_inv_l; auto.
  Qed.

  Theorem val_div : ∀ m, p^(v p m)｜m.
  Proof.
    intros m.
    destruct (classic (m = 0)); subst; auto using div_0_r with Z.
    apply val_lower_bound; auto using naturals.le_refl.
  Qed.

  Theorem val_ineq : ∀ a b, a ≠ 0 → b｜a → (v p b ≤ v p a)%N.
  Proof.
    intros a b H [k H0]; simpl in *; subst.
    apply (cancellation_ne0 ℤ) in H as [H H0]; simpl.
    rewrite -> val_mul, add_comm; auto.
    now (exists (v p k)).
  Qed.

  Theorem val_inv : ∀ a b, a ≠ 0 → b｜a → v p (a / b) = (v p a - v p b)%N.
  Proof.
    intros a b H H0.
    unfold div.
    destruct excluded_middle_informative; try tauto.
    destruct constructive_indefinite_description; simpl in *; subst.
    apply (cancellation_ne0 ℤ) in H as [H H1]; simpl.
    rewrite -> val_mul, sub_abba; auto.
  Qed.

  Theorem val_p : v p p = 1%N.
  Proof.
    apply naturals.le_antisymm.
    - apply le_lt_succ, val_upper_bound; intros H; subst.
      + contradiction zero_not_prime.
      + destruct prime_p as [H0 H1], H as [k H].
        contradiction H0.
        exists k.
        apply (cancellation_mul_r ℤ_ID p).
        * intros H2.
          subst.
          contradiction zero_not_prime.
        * now rewrite <-M2, <-(pow_2_r ℤ), M3.
    - apply val_lower_bound.
      + intros H; subst.
        contradiction zero_not_prime.
      + rewrite -> pow_1_r.
        apply div_refl.
  Qed.

  Theorem val_1 : v p 1 = 0%N.
  Proof.
    apply naturals.le_antisymm; auto using zero_le.
    apply le_lt_succ.
    apply val_upper_bound; try apply zero_ne_1.
    rewrite -> pow_1_r.
    now destruct prime_p.
  Qed.

  Theorem val_0 : v p 0 = 0%N.
  Proof.
    unfold v.
    repeat destruct excluded_middle_informative; try tauto; exfalso; tauto.
  Qed.

  Theorem val_pow : ∀ a k, v p (a^k) = (k * v p a)%N.
  Proof.
    intros a.
    destruct (classic (a = 0)) as [H | H]; subst.
    - intros k.
      destruct (classic (k = 0%N)) as [H | H]; subst.
      + now rewrite -> pow_0_r, val_0, naturals.mul_0_l, <-val_1.
      + now rewrite -> pow_0_l, val_0, naturals.mul_0_r, <-val_0.
    - induction k using Induction.
      + now rewrite -> pow_0_r, naturals.mul_0_l, <-val_1.
      + rewrite -> pow_succ_r, val_mul; auto.
        * now rewrite -> IHk, <-add_1_r, mul_distr_r, mul_1_l.
        * now apply (pow_ne_0 ℤ_ID).
  Qed.

  Lemma val_quotient : ∀ m, m ≠ 0 → ¬ p｜m / p ^ v p m.
  Proof.
    intros m H.
    rewrite <-(pow_1_r ℤ p) at 1.
    apply val_upper_bound.
    - contradict H.
      apply div_spec in H; auto using val_div.
      + now rewrite -> (mul_0_l ℤ) in *.
      + apply (pow_ne_0 ℤ_ID).
        intros H1.
        subst.
        contradiction zero_not_prime.
    - rewrite -> val_inv, val_pow, val_p, mul_1_r, sub_diag; auto using val_div.
      apply naturals.lt_succ.
  Qed.

  Theorem val_quot_positive : ∀ m, 0 < m → 0 < p → 0 < m / p ^ v p m.
  Proof.
    intros m H H0.
    rewrite <-(div_inv_l m (p^(v p m))) in H; auto using val_div.
    apply (pos_div_l ℤ_order) in H; eauto using (pow_pos ℤ_order).
  Qed.

  Theorem quot_le_bound : ∀ m x, 0 < m → 0 < p → p ^ x｜m → m / p ^ x ≤ m.
  Proof.
    intros m x H H0 H1.
    apply (mul_le_l_iff ℤ_order (p^x)); simpl; fold le.
    - now apply (pow_pos ℤ_order).
    - rewrite -> div_inv_l, <-(M3 m) at 1; auto.
      apply mul_le_r; auto; fold le.
      now apply lt_0_le_1, (pow_pos ℤ_order).
  Qed.

  Theorem val_quot_le_bound : ∀ m, 0 < m → 0 < p → m / p ^ v p m ≤ m.
  Proof.
    intros m H H0.
    apply quot_le_bound; auto using val_div.
  Qed.

  Theorem val_quot_bound : ∀ m, 0 < m → 0 < p → p｜m → m / p ^ v p m < m.
  Proof.
    intros m H H0 H1.
    pose proof H as H2.
    eapply val_quot_le_bound in H2 as [H2 | H2]; eauto.
    apply (f_equal (mul (p^v p m))) in H2.
    rewrite -> div_inv_l, <-(M3 m) in H2 at 1; auto using val_div.
    apply (cancellation_mul_r ℤ_ID) in H2; try now apply pos_ne_0.
    rewrite <-(rings.pow_1_r ℤ p) in H1.
    apply val_lower_bound in H1; auto using (pos_ne_0 ℤ_order).
    destruct prime_p as [H3 H4], H1 as [c H1].
    contradict H3.
    rewrite <-H1 in H2.
    exists (p^c).
    now rewrite -> pow_add_r, pow_1_r, M1 in H2.
  Qed.

  Theorem val_gcd : ∀ x m, m ≠ 0 → gcd (p^x) (m / p^v p m) = 1.
  Proof.
    intros x m H.
    apply not_exists_prime_divisor; auto using gcd_nonneg.
    intros [q [H0 H1]].
    destruct (classic (q ~ p)) as [H2 | H2].
    - assert (q｜m / p ^ v p m) as H3.
      { eapply div_trans; fold divide; eauto using gcd_r_div. }
      apply assoc_pm in H2 as [H2 | H2]; subst; contradiction (val_quotient m).
      now apply div_sign_l in H3.
    - assert (q｜p^x) as H3.
      { eapply div_trans; fold divide; eauto using gcd_l_div. }
      apply Euclid_power in H3; auto.
      destruct prime_p as [H4 H5].
      apply H5 in H3 as [H3 | H3]; now destruct H0.
  Qed.

  Theorem val_is_gcd : ∀ x m, m ≠ 0 → gcd(p^x, m / p^v p m) = 1.
  Proof.
    intros x m H.
    erewrite <-val_gcd; eauto using is_gcd_gcd.
  Qed.

  Theorem gcd_val : ∀ m, m ≠ 0 → 0 < p → gcd (p^v p m) m = p^v p m.
  Proof.
    intros m H H0.
    rewrite <-(div_inv_l m (p^v p m)) at 2; auto using val_div.
    rewrite -> gcd_mul_r, val_gcd, gcd_refl, M1, M3; auto using val_is_gcd.
    now apply or_introl, pow_pos.
  Qed.

  Theorem val_lcm_l : ∀ m n,
      0 < m → 0 < n → 0 < p →
      (v p m ≤ v p n)%N → p^v p n * lcm (m / p^v p m) (n / p^v p n) = lcm m n.
  Proof.
    intros m n H H0 H1 H2.
    eapply (cancellation_mul_l ℤ_ID (gcd m n));
      auto using gcd_pos, (pos_ne_0 ℤ_order); simpl.
    rewrite <-gcd_lcm_ident, <-(div_inv_r m (p^v p m)), gcd_mul_l at 1;
      auto using val_div; unfold le, ordered_rings.le; intuition.
    2: { erewrite <-val_gcd, gcd_sym; eauto using is_gcd_gcd.
         auto using (pos_ne_0 ℤ_order). }
    rewrite <-(div_inv_r n (p^v p n)), gcd_mul_r at 1; auto using val_div.
    2: { erewrite <-val_gcd, gcd_sym; eauto using is_gcd_gcd.
         auto using (pos_ne_0 ℤ_order). }
    rewrite -> ? M2, M1, ? M2, (M1 (lcm (m / p ^ v p m) (n / p ^ v p n))),
    <-gcd_lcm_ident, (M1 (m / p^v p m)), M1, ? M2, div_inv_l, (M1 _ n), <-? M2;
      try (apply div_nonneg; unfold le, ordered_rings.le; intuition;
           now apply (pow_pos ℤ_order)); auto using val_div.
    f_equal.
    rewrite -> gcd_sym, val_gcd, M3; auto using (pos_ne_0 ℤ_order).
    rewrite <-(div_inv_r m (p^v p m)) at 4; auto using val_div.
    apply f_equal, div_l_gcd; try now apply or_introl, (pow_pos ℤ_order).
    apply val_lower_bound; auto; now apply (pos_ne_0 ℤ_order).
  Qed.

  Theorem val_lcm_r : ∀ m n,
      0 < m → 0 < n → 0 < p →
      (v p n ≤ v p m)%N → p^v p m * lcm (m / p^v p m) (n / p^v p n) = lcm m n.
  Proof.
    intros m n H H0 H1 H2.
    rewrite -> lcm_sym, val_lcm_l; auto using lcm_sym.
  Qed.

  Theorem val_lcm_l_gcd : ∀ m n,
      0 < m → 0 < n → 0 < p →
      (v p m ≤ v p n)%N → gcd (p^v p n) (lcm (m / p^v p m) (n / p^v p n)) = 1.
  Proof.
    intros m n H H0 H1 H2.
    apply gcd_pow_l.
    repeat split; auto using div_1_l with Z.
    intros x H3 H4.
    pose proof prime_p as [H5 H6].
    apply H6 in H3 as [H3 | [H3 H7]]; fold divide in *; auto.
    eapply div_trans in H4; eauto; fold divide in *.
    assert (p｜(m / p ^ v p m) * (n / p ^ v p n)) as H8.
    { eapply div_trans; fold divide; eauto using lcm_prod. }
    apply Euclid's_lemma in H8 as [H8 | H8]; auto.
    - destruct (val_is_gcd 1 m) as [_ [_ H9]]; try now apply (pos_ne_0 ℤ_order).
      rewrite -> pow_1_r in H9.
      eauto using div_trans with Z.
    - destruct (val_is_gcd 1 n) as [_ [_ H9]]; try now apply (pos_ne_0 ℤ_order).
      rewrite -> pow_1_r in H9.
      eauto using div_trans with Z.
  Qed.

  Theorem val_lcm_r_gcd : ∀ m n,
      0 < m → 0 < n → 0 < p →
      (v p n ≤ v p m)%N → gcd (p^v p m) (lcm (m / p^v p m) (n / p^v p n)) = 1.
  Proof.
    intros m n H H0 H1 H2.
    rewrite -> lcm_sym.
    auto using val_lcm_l_gcd.
  Qed.

  Theorem val_lcm_l_rel_prime : ∀ m n,
      0 < m → 0 < n → 0 < p →
      (v p m ≤ v p n)%N → gcd(p^v p n, lcm (m / p^v p m) (n / p^v p n)) = 1.
  Proof.
    intros m n H H0 H1 H2.
    erewrite <-val_lcm_l_gcd; eauto using is_gcd_gcd.
  Qed.

  Theorem val_lcm_r_rel_prime : ∀ m n,
      0 < m → 0 < n → 0 < p →
      (v p n ≤ v p m)%N → gcd(p^v p m, lcm (m / p^v p m) (n / p^v p n)) = 1.
  Proof.
    intros m n H H0 H1 H2.
    erewrite <-val_lcm_r_gcd; eauto using is_gcd_gcd.
  Qed.

End Valuations.

Theorem inv_div_l : ∀ a b c, b｜a → b ≠ 0 → a/b｜c ↔ a｜b*c.
Proof.
  split; intros [k H1]; exists k.
  - rewrite -> H1, M1, <-M2, div_inv_r; auto.
  - apply (cancellation_mul_l ℤ_ID b); auto; simpl.
    rewrite -> H1, (M1 b), <-M2, div_inv_r; auto.
Qed.

Definition abs (a : Z) := If 0 ≤ a then a else (-a).

Notation " '|' a '|' " := (abs a) (at level 30, format "'|' a '|'") : Z_scope.

Theorem abs_pos : ∀ a, 0 ≤ |a|.
Proof.
  intros a.
  unfold abs.
  destruct excluded_middle_informative; auto.
  apply or_introl, lt_not_ge.
  contradict n.
  now apply neg_le_0.
Qed.

Theorem abs_zero : ∀ a, |a| = 0 ↔ a = 0.
Proof.
  unfold abs.
  split; intros H; destruct excluded_middle_informative; ring [H].
Qed.

Theorem gcd_sign : ∀ a b, gcd a b = gcd a (-b).
Proof.
  intros a b.
  apply eq_sym, gcd_is_gcd.
  - rewrite <-gcd_neg.
    apply is_gcd_gcd.
  - apply gcd_nonneg.
Qed.

Theorem lcm_sign : ∀ a b, lcm a b = lcm a (-b).
Proof.
  intros a b.
  apply eq_sym, lcm_is_lcm.
  - rewrite <-lcm_neg.
    apply is_lcm_lcm.
  - apply lcm_nonneg.
Qed.

Theorem gcd_abs : ∀ a b, gcd a b = gcd (|a|) (|b|).
Proof.
  intros a b.
  unfold abs.
  repeat destruct excluded_middle_informative; auto.
  - now rewrite -> gcd_sign.
  - now rewrite -> gcd_sym, gcd_sign, gcd_sym.
  - now rewrite -> gcd_sign, gcd_sym, gcd_sign, gcd_sym.
Qed.

Theorem lcm_abs : ∀ a b, lcm a b = lcm (|a|) (|b|).
Proof.
  intros a b.
  unfold abs.
  repeat destruct excluded_middle_informative; auto.
  - now rewrite -> lcm_sign.
  - now rewrite -> lcm_sym, lcm_sign, lcm_sym.
  - now rewrite -> lcm_sign, lcm_sym, lcm_sign, lcm_sym.
Qed.

Theorem lcm_0 : ∀ a b, lcm a b = 0 → a = 0 ∨ b = 0.
Proof.
  intros a b H.
  rewrite <-(abs_zero a), <-(abs_zero b), lcm_abs in *.
  apply (cancellation ℤ_ID); simpl.
  rewrite -> gcd_lcm_ident, H, (mul_0_r ℤ); auto using abs_pos.
Qed.

Theorem lcm_bound : ∀ a b, 0 < a → b ≤ lcm a b.
Proof.
  intros a b H.
  destruct (classic (b = 0)); subst.
  - rewrite -> lcm_r_0.
    apply le_refl.
  - apply div_le.
    + destruct (lcm_nonneg a b) as [H1 | H1]; auto.
      apply eq_sym, lcm_0 in H1 as [H1 | H1]; subst; try tauto.
      contradiction (lt_irrefl ℤ_order 0).
    + apply lcm_div_r.
Qed.
