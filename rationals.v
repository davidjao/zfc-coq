Set Warnings "-ambiguous-paths".
Require Export ssreflect ssrbool ssrfun ordered_fields Field.

Definition ℤ0 := {z in ℤ × ℤ | (proj2 ℤ ℤ z) ≠ 0}.

Definition rational_relation :=
  {z in ℤ0 × ℤ0 | ∃ a b c d : Z, z = ((a, b), (c, d)) ∧ a * d = b * c}.

Theorem rational_equivalence : is_equivalence ℤ0 rational_relation.
Proof.
  (repeat split; rewrite /rational_relation) =>
  [a /[dup] /Specify_classification
     [/Product_classification [x [y [H [H0 -> {a}]]]]] |
   x y H H0 /Specify_classification
     [H1 [a [b [c [d [/Ordered_pair_iff [H2 H3] H4]]]]]] |
   x y z H H0 H1 /Specify_classification
     [H2 [a [b [c [d [/Ordered_pair_iff [H3 /[dup] H4 ->] H5]]]]]]
     /Specify_classification
     [H6 [a' [b' [c' [d' [/Ordered_pair_iff
                           [/Ordered_pair_iff
                             [/set_proj_injective <-
                               /set_proj_injective <-] H7] H8]]]]]]];
    rewrite Specify_classification Product_classification ? proj2_eval //;
            split; eauto.
  - exists (mkSet H : Z), (mkSet H0 : Z), (mkSet H : Z), (mkSet H0 : Z).
    rewrite integers.M1 //.
  - exists c, d, a ,b.
    rewrite Ordered_pair_iff M1 (M1 d) //.
  - exists a, b, c', d'.
    rewrite H3 H7.
    split; auto.
    apply (cancellation_mul_l (integral_domain ℤ_order) d) => /=.
    + move: H4 H0 -> => /Specify_classification [] H0.
      (rewrite proj2_eval; eauto using elts_in_set) => /[swap] -> //.
    + rewrite (M1 b) ? M2 -H8 (M1 _ b) M2 -H5 (M1 _ a) //.
Qed.

Definition Q := elts (ℤ0 / rational_relation)%set.

Definition IQS (a : Q) := elt_to_set a : set.
Coercion IQS : Q >-> set.

Declare Scope Q_scope.
Delimit Scope Q_scope with Q.
Open Scope Q_scope.
Bind Scope Q_scope with Q.

Lemma embed_zero : (0, 1) ∈ ℤ0.
Proof.
  apply Specify_classification, conj;
    rewrite ? Product_classification ? proj2_eval; eauto using elts_in_set
  => /set_proj_injective /zero_ne_1 //.
Qed.

Lemma embed_nonzero : ∀ a b : Z, b ≠ 0 → (a, b) ∈ ℤ0.
Proof.
  move=> a b H.
  apply Specify_classification, conj;
    rewrite ? Product_classification ? proj2_eval; eauto using elts_in_set
  => /set_proj_injective /H => //.
Qed.

Definition embed (a b : Z) : Q.
Proof.
  case (excluded_middle_informative (b = 0)) => [H | H].
  - exact (quotient_map rational_relation (mkSet embed_zero)).
  - exact (quotient_map rational_relation (mkSet (embed_nonzero a b H))).
Defined.

Infix "/" := embed : Q_scope.

Theorem Qlift : ∀ q, ∃ a b, b ≠ 0 ∧ a / b = q.
Proof.
  move=> q.
  elim (quotient_lift q) => [y].
  elim (unique_set_element y) =>
  [x [[/[swap] -> {x} /Specify_classification
                      [/Product_classification [a [b [H [H0 H1]]]] H2]] H3 H4]].
  exists (mkSet H : Z), (mkSet H0 : Z).
  have H5: mkSet H0 ≠ 0 by move: H1 proj2_eval H2 -> => -> // /[swap] <- //.
  split; auto.
  rewrite /embed -H4.
  elim excluded_middle_informative => [ | H6] //.
    by apply /f_equal /set_proj_injective.
Qed.

Theorem Qequiv : ∀ a b c d, b ≠ 0 → d ≠ 0 → a / b = c / d ↔ a * d = b * c.
Proof.
  ((split; rewrite /embed; repeat elim excluded_middle_informative => //) =>
  {}H0 {}H; rewrite quotient_equiv; auto using rational_equivalence => /=) =>
  [/Specify_classification
    [H1 [a' [b' [c' [d' [/Ordered_pair_iff
                          [/Ordered_pair_iff
                            [/set_proj_injective -> /set_proj_injective ->]
                            /Ordered_pair_iff
                            [/set_proj_injective ->
                             /set_proj_injective ->]] H3]]]]]] | H1] //.
  rewrite Specify_classification Product_classification.
  repeat esplit; eauto;
    rewrite ? (Specify_classification (ℤ × ℤ)) ? Product_classification
            ? proj2_eval; repeat split; eauto using elts_in_set
  => /set_proj_injective //.
Qed.

Definition IZQ a := a / 1.
Coercion IZQ : Z >-> Q.

Definition zero := 0 / 1.
Definition one := 1 / 1.
Notation "0" := zero : Q_scope.
Notation "1" := one : Q_scope.

Definition add (x y : Q) : Q.
Proof.
  elim (constructive_indefinite_description (Qlift x)) =>
  [a /constructive_indefinite_description [b [e e0]]].
  elim (constructive_indefinite_description (Qlift y)) =>
  [c /constructive_indefinite_description [d [e1 e2]]].
  exact ((a * d + c * b) / (b * d)).
Defined.

Definition mul (x y : Q) : Q.
Proof.
  elim (constructive_indefinite_description (Qlift x)) =>
  [a /constructive_indefinite_description [b [e e0]]].
  elim (constructive_indefinite_description (Qlift y)) =>
  [c /constructive_indefinite_description [d [e1 e2]]].
  exact ((a * c) / (b * d)).
Defined.

Definition neg (x : Q) : Q.
Proof.
  elim (constructive_indefinite_description (Qlift x)) =>
  [a /constructive_indefinite_description [b [e e0]]].
  exact (-a / b).
Defined.

Definition inv (x : Q) : Q.
Proof.
  elim (constructive_indefinite_description (Qlift x)) =>
  [a /constructive_indefinite_description [b [e e0]]].
  exact (b / a).
Defined.

Infix "+" := add : Q_scope.
Infix "*" := mul : Q_scope.
Notation "- a" := (neg a) : Q_scope.
Notation "- 1" := (neg one) : Q_scope.
Notation "a '^-1' " := (inv a) (at level 30, format "a '^-1'") : Q_scope.

Definition sub a b := a + -b.
Definition div a b := a * b^-1.

Infix "-" := sub : Q_scope.

Theorem add_wf : ∀ a b c d : Z,
    b ≠ 0%Z → d ≠ 0%Z → (a / b) + (c / d) = (a * d + c * b) / (b * d).
Proof.
  rewrite /add /sig_rect => a b c d H H0.
  elim constructive_indefinite_description => a' [b' [H1 H2]].
  elim constructive_indefinite_description => b'' [H3 H4].
  elim constructive_indefinite_description => c' [d' [H5 H6]].
  elim constructive_indefinite_description => d'' [H7 H8].
  move: H2 H4 H6 H8; (rewrite ? Qequiv; auto);
    (try by apply (ne0_cancellation ℤ_ID)) => H2 H4 H6 H8.
  ring_simplify [H2 H4 H6 H8]; rewrite -? M2 -H4 H2 ? (M2 _ c) -H8 H6; ring.
Qed.

Theorem mul_wf : ∀ a b c d : Z,
    b ≠ 0%Z → d ≠ 0%Z → (a / b) * (c / d) = (a * c) / (b * d).
Proof.
  rewrite /mul /sig_rect => a b c d H H0.
  elim constructive_indefinite_description => a' [b' [H1 H2]].
  elim constructive_indefinite_description => b'' [H3 H4].
  elim constructive_indefinite_description => c' [d' [H5 H6]].
  elim constructive_indefinite_description => d'' [H7 H8].
  move: H2 H4 H6 H8; (rewrite ? Qequiv; auto);
    (try by apply (ne0_cancellation ℤ_ID)) => H2 H4 H6 H8.
  ring_simplify [H2 H4 H6 H8]; rewrite -H8 H6 -? M2 -H4 H2; ring.
Qed.

Theorem neg_wf : ∀ a b : Z, b ≠ 0%Z → -(a / b) = (-a) / b.
Proof.
  rewrite /neg /sig_rect => a b H.
  elim constructive_indefinite_description => [a' [b' [H0 H1]]].
  elim constructive_indefinite_description => b'' [H2 H3].
  move: H1 H3; (rewrite ? Qequiv; auto) => H1 H3.
  have -> : (-a' * b = -(a' * b))%Z by ring.
  rewrite H3; ring.
Qed.

Theorem inv_wf : ∀ a b : Z, a ≠ 0%Z → b ≠ 0%Z → (a / b)^-1 = b / a.
Proof.
  rewrite /inv /sig_rect => a b H H0.
  elim constructive_indefinite_description => [a' [b' [H1 H2]]].
  elim constructive_indefinite_description => b'' [H3 H4].
  move: (H2) (H4); rewrite ? Qequiv; auto => H5.
  move: H5 H2 -> => /Qequiv => /(_ H1) /(_ H0).
  rewrite (mul_0_l ℤ b : 0 * b = 0)%Z =>
  /(@eq_sym Z) /(integral_domains.cancellation ℤ_ID); tauto.
Qed.

Theorem A3 : ∀ x, 0 + x = x.
Proof.
  move=> x.
  case (Qlift x) => [a [b [H <-]]].
  (rewrite add_wf ? Qequiv //; try ring) => [/zero_ne_1 | ] //.
  rewrite M3 //.
Qed.

Theorem A1 : ∀ a b, a + b = b + a.
Proof.
  move=> a b.
  case (Qlift a) as [a1 [a2 [H <-]]], (Qlift b) as [b1 [b2 [H0 <-]]].
  (rewrite ? add_wf // Qequiv; try ring) =>
  /(cancellation_0_mul ℤ_order); tauto.
Qed.

Theorem A2 : ∀ a b c, a + (b + c) = (a + b) + c.
Proof.
  move=> a b c.
  case (Qlift a) as [a1 [a2 [H <-]]], (Qlift b) as
        [b1 [b2 [H0 <-]]], (Qlift c) as [c1 [c2 [H1 <-]]].
  (rewrite ? add_wf // ? Qequiv; try ring);
    repeat apply (ne0_cancellation ℤ_ID) => //.
Qed.

Theorem M3 : ∀ x, 1 * x = x.
Proof.
  move=> x.
  case (Qlift x) as [a [b [H <-]]].
  (rewrite mul_wf ? Qequiv //; try ring) => [/zero_ne_1 | ] //.
  rewrite M3 //.
Qed.

Theorem M1 : ∀ a b, a * b = b * a.
Proof.
  move=> a b.
  case (Qlift a) as [a1 [a2 [H <-]]], (Qlift b) as [b1 [b2 [H0 <-]]].
  (rewrite ? mul_wf // Qequiv; try ring) =>
  /(cancellation_0_mul ℤ_order); tauto.
Qed.

Theorem M2 : ∀ a b c, a * (b * c) = (a * b) * c.
Proof.
  move=> a b c.
  case (Qlift a) as [a1 [a2 [H <-]]], (Qlift b) as
        [b1 [b2 [H0 <-]]], (Qlift c) as [c1 [c2 [H1 <-]]].
  (rewrite ? mul_wf // ? Qequiv; try ring);
    repeat apply (ne0_cancellation ℤ_ID) => //.
Qed.

Theorem D1 : ∀ a b c, (a + b) * c = a * c + b * c.
Proof.
  move=> a b c.
  case (Qlift a) as [a1 [a2 [H <-]]], (Qlift b) as
        [b1 [b2 [H0 <-]]], (Qlift c) as [c1 [c2 [H1 <-]]].
  (rewrite ? add_wf ? mul_wf ? add_wf // ? Qequiv; try ring);
    repeat apply (ne0_cancellation ℤ_ID) => //.
Qed.

Theorem sub_neg : ∀ a b, a - b = a + -b.
Proof.
  auto.
Qed.

Theorem A4 : ∀ a, a + -a = 0.
Proof.
  move=> a.
  case (Qlift a) as [a1 [a2 [H <-]]].
  (rewrite neg_wf ? add_wf // Qequiv; try ring) =>
  [/(ne0_cancellation ℤ_ID) | /zero_ne_1] //; tauto.
Qed.

Theorem zero_ne_1 : 1 ≠ 0.
Proof.
  rewrite Qequiv ? integers.M3 => /zero_ne_1 //.
Qed.

Theorem div_inv : ∀ a b, div a b = a * b^-1.
Proof.
  auto.
Qed.

Theorem inv_l : ∀ a, a ≠ 0 → a^-1 * a = 1.
Proof.
  move=> a.
  case (Qlift a) => [a1 [a2 [H <-]]] /Qequiv => /(_ H) /(_ integers.zero_ne_1).
  rewrite integers.M1 integers.M3 (mul_0_r ℤ a2 : a2 * 0 = 0)%Z => H0.
  (rewrite inv_wf // mul_wf // Qequiv; try ring) =>
  [/(ne0_cancellation ℤ_ID) | /integers.zero_ne_1] //; tauto.
Qed.

Definition ℚ_ring := mkRing _ 0 1 add mul neg A3 A1 A2 M3 M1 M2 D1 A4.

Definition ℚ := mkField ℚ_ring inv inv_l zero_ne_1.

Add Field rational_field_raw : (fieldify ℚ).
Add Field rational_field :
  (fieldify ℚ : field_theory 0 1 add mul sub neg div inv eq).

Definition positive (x : Q) : Prop.
Proof.
  elim (constructive_indefinite_description (Qlift x)) =>
  [a /constructive_indefinite_description [b [e e0]]].
  exact (a * b > 0).
Defined.

Lemma pos_wf : ∀ a b, b ≠ 0%Z → positive (a / b) ↔ a * b > 0.
Proof.
  rewrite /positive /sig_rect => a b H.
  elim constructive_indefinite_description => [a' [b' [H0 H1]]].
  elim constructive_indefinite_description => b0 [H2 H3].
  move: H1 H3; rewrite ? Qequiv // => /[dup] H1 /[swap] /[dup] H3.
  case (classic (a = 0%Z)) => [-> | /(cancellation_mul_r ℤ_ID a b0 b')
                                     /[swap] /= <- /[swap] <- -> // {b0 H2 H3}].
  { rewrite (mul_0_r ℤ b' : b' * 0 = 0)%Z (mul_0_r ℤ b0 : b0 * 0 = 0)%Z
            (mul_0_l ℤ b : 0 * b = 0)%Z =>
    /(integral_domains.cancellation ℤ_ID) => [[-> | ]] //=.
    rewrite (mul_0_l ℤ b0 : 0 * b0 = 0)%Z //. }
  ((suff: (∀ x y z w, y ≠ 0 → w ≠ 0 → x * w = y * z → 0 < x * y → 0 < z * w)%Z
    => [H2 | ]; first by split; apply H2; eauto; ring [H1]) =>
   [{a b H a' b' H0 H1}
      x y z w H /(ne0_lt_gt ℤ_order) [H0 | H0] H1
      /(pos_mul_iff ℤ_order) [[H2 H3] | [H2 H3]]]; apply (pos_mul_iff ℤ_order);
   try (have: 0 < x * w by apply (mul_pos_pos ℤ_order));
   try (have: x * w < 0 by apply (mul_neg_pos ℤ_order));
   try (have: x * w < 0 by apply (mul_pos_neg ℤ_order));
   try (have: 0 < x * w by apply (mul_neg_neg ℤ_order)); rewrite H1) =>
  [/(pos_div_l ℤ_order _ _ H3) | /(neg_pos_div_l ℤ_order _ _ H3) |
   /(pos_neg_div_l ℤ_order _ _ H3) | /(neg_div_l ℤ_order _ _ H3)]; tauto.
Qed.

Theorem T_pos : ∀ x, positive x ∧ x ≠ 0 ∧ ¬ positive (-x) ∨
                     ¬ positive x ∧ x = 0 ∧ ¬ positive (-x) ∨
                     ¬ positive x ∧ x ≠ 0 ∧ positive (-x).
Proof.
  move=> x.
  case (Qlift x) => [a [b [H <-]]].
  rewrite ? neg_wf // ? pos_wf // Qequiv // ? (integers.M1 _ 1) ? integers.M3
          ? (mul_0_r ℤ b : b * 0 = 0)%Z; auto using integers.zero_ne_1.
  have -> : (-a*b = -(a*b))%Z by ring.
  suff -> : (a = 0 ↔ a * b = 0)%Z.
  - rewrite -(lt_neg_0 ℤ_order : ∀ a, a < 0 ↔ 0 < -a)%Z /=.
    case (integers.T (a*b) 0); tauto.
  - split => [-> | /(integral_domains.cancellation ℤ_ID) H0]; try ring; tauto.
Qed.

Definition lt x y := positive (y - x).

Infix "<" := lt : Q_scope.

Theorem T : ∀ a b, a < b ∧ a ≠ b ∧ ¬ b < a
                   ∨ ¬ a < b ∧ a = b ∧ ¬ b < a
                   ∨ ¬ a < b ∧ a ≠ b ∧ b < a.
Proof.
  rewrite /lt => a b.
  have -> : (a-b = -(b-a)) by ring.
  have -> : (a=b ↔ b-a=0); eauto using T_pos.
  split => [-> | H]; [ | rewrite -(A3 a) -H]; ring.
Qed.

Theorem O0 : ∀ a b, 0 < a → 0 < b → 0 < a + b.
Proof.
  rewrite /lt /sub => x y.
  rewrite -(neg_0 ℚ : 0 = -0) ? (A3_r ℚ : ∀ x, x + 0 = x).
  case (Qlift x) as [a [b [H <-]]], (Qlift y) as [c [d [H0 <-]]].
  rewrite add_wf // ? pos_wf //;
          auto using (ne0_cancellation (integral_domain ℤ_order)) =>
  /(pos_mul ℤ_order) /[swap] /(pos_mul ℤ_order) /= /[swap].
  rewrite ? (lt_neg_0 ℤ_order : ∀ a, a < 0 ↔ 0 < -a)%Z =>
  [[[H1 H2] | [H1 H2]]] [[H3 H4] | [H3 H4]];
    [ | have -> : ((a*d+c*b)*(b*d) = (a*-d+-c*b)*(b*-d))%Z
      | have -> : ((a*d+c*b)*(b*d) = (-a*d+c*-b)*(-b*d))%Z
      | have -> : ((a*d+c*b)*(b*d) = (-a*-d+-c*-b)*(-b*-d))%Z ];
    eauto 6 using (mul_pos_pos ℤ_order), (O0 ℤ_order) with Z; ring.
Qed.

Theorem lt_trans : ∀ a b c, a < b → b < c → a < c.
Proof.
  rewrite /lt => a b c.
  have -> : b-a = (b-a)-0; try have -> : c-b = (c-b)-0; try ring.
  (have -> : c-a = (b-a)+(c-b)-0 by ring) => /O0 /[apply] //.
Qed.

Theorem O1 : ∀ a b c, b < c → a + b < a + c.
Proof.
  rewrite /lt => a b c H.
  suff -> : (a + c - (a + b) = c - b) => //; ring.
Qed.

Theorem O2 : ∀ a b, 0 < a → 0 < b → 0 < a * b.
Proof.
  rewrite /lt /sub => x y.
  rewrite -(neg_0 ℚ : 0 = -0) ? (A3_r ℚ : ∀ x, x + 0 = x).
  case (Qlift x) as [a [b [H <-]]], (Qlift y) as [c [d [H0 <-]]].
  rewrite mul_wf ? pos_wf;
    auto using (ne0_cancellation (integral_domain ℤ_order)) =>
  /(mul_pos_pos ℤ_order) /[apply] /=.
  suff -> : (a*b*(c*d) = a*c*(b*d))%Z => //; ring.
Qed.

Definition ℚ_ring_order := mkOR ℚ_ring lt lt_trans T O1 O2 zero_ne_1.
Definition ℚ_order := mkOF ℚ lt lt_trans T O1 O2.

Notation "a > b" := (b < a) (only parsing) : Q_scope.

Definition le := ordered_rings.le ℚ_ring_order : Q → Q → Prop.
Infix "≤" := le : Q_scope.
Notation "a ≥ b" := (b ≤ a) (only parsing) : Q_scope.
Notation "a < b < c" := (a < b ∧ b < c) (at level 70, b at next level): Q_scope.
Notation "a ≤ b < c" := (a ≤ b ∧ b < c) (at level 70, b at next level): Q_scope.
Notation "a < b ≤ c" := (a < b ∧ b ≤ c) (at level 70, b at next level): Q_scope.
Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) (at level 70, b at next level): Q_scope.

Theorem lt_dense : ∀ a b, a < b → ∃ c, a < c ∧ c < b.
Proof.
  move=> x y H.
  case (Qlift x) as [a [b [H0 <-]]], (Qlift y) as [c [d [H1 <-]]].
  have H2: (2 ≠ 0)%Z by apply (ordered_rings.zero_ne_2 ℤ_order).
  exists ((b*c + a*d)/(2*b*d)); split; move: H;
    rewrite /lt /sub ? neg_wf ? add_wf ? pos_wf //;
            auto using (ne0_cancellation (integral_domain ℤ_order));
  [ suff -> : (((b*c+a*d)*b+-a*(2*b*d))*(2*b*d*b) =
               2*(b*b)*((c*b+-a*d)*(d*b)))%Z |
    suff -> : ((c*(2*b*d)+-(b*c+a*d)*d)*(d*(2*b*d)) =
               2*(d*d)*((c*b+-a*d)*(d*b)))%Z ];
    eauto using (mul_pos_pos ℤ_order), (ordered_rings.O0 ℤ_order),
    (square_ne0 ℤ_order), (ordered_rings.zero_lt_1 ℤ_order) with Z; ring.
Qed.

Theorem lt_dense2 : ∀ a b, 0 < a → 0 < b → ∃ c, 0 < c ∧ c < a ∧ c < b.
Proof.
  move=> a b H H0.
  case (lt_or_ge ℚ_ring_order a b) => [H1 | H1] /=.
  - case (lt_dense 0 a) => [ | c [H2 H3]] //.
    eauto using lt_trans.
  - case (lt_dense 0 b) => [ | c [H2 H3]] //.
    repeat esplit; eauto.
    eapply (lt_le_trans (ordered_ring_from_field ℚ_order)); eauto.
Qed.

Theorem pos_denom : ∀ x, ∃ a b, (0 < b)%Z ∧ x = a / b.
Proof.
  move=> x.
  case (Qlift x) as [a [b [H <-]]], (integers.T b 0); intuition; eauto.
  exists (-a)%Z, (-b)%Z.
  (rewrite -(lt_neg_0 ℤ_order b : b < 0 ↔ 0 < -b)%Z Qequiv //);
  repeat (esplit; eauto; ring).
  contradict H0; ring [H0].
Qed.

Theorem reduced_form : ∀ x, ∃ a b, gcd(a, b) = 1 ∧ x = a / b ∧ b ≠ 0%Z.
Proof.
  move=> x.
  case (Qlift x) => [a [b /and_comm [<- /[dup] H]]].
  case (common_factor a b) => // [d [H0 [[m ->] [[n ->] /= H1]]]]
                                 /[dup] H2 /(cancellation_ne0 ℤ) [H3 H4].
  exists m, n.
  rewrite Qequiv //.
  (repeat split; auto using (div_1_l ℤ) with Z; try ring) => z [k H5] [l H6].
  move: H5 H6 H1 -> => -> /= /(_ (z*d)%Z).
  elim => [c | | ]; rewrite -? integers.M2 ? rings.M2;
            try (rewrite -{1}(integers.M3 d) => /(cancellation_mul_r ℤ_ID) =>
                 /(_ H4) ->); auto using (div_mul_l ℤ), (div_refl ℤ) with Z.
Qed.

Theorem Rudin_1_1 : ¬ ∃ p : Q, p * p = 2.
Proof.
  rewrite /IZQ => [[p]].
  case (reduced_form p) => [m [n [H [-> H0]]]].
  rewrite mul_wf ? Qequiv ? (integers.M1 _ 1) ? (integers.M1 _ 2) ? integers.M3;
    auto using (ne0_cancellation ℤ_ID), integers.zero_ne_1 => H1.
  have [k /= H2]: 2｜m by (have: 2｜m*m by exists (n*n)%Z; rewrite rings.M1) =>
  /Euclid's_lemma => /(_ two_is_prime) => [[ | ]] //.
  move: H2 H H1 -> => {m} H.
  (have -> : (k*2*(k*2) = 2*(2*(k*k)))%Z by ring) =>
  /(cancellation_mul_l ℤ_ID) => /(_ (zero_ne_2 ℤ_order)) => H1.
  have H2: 2｜n by (have: 2｜n*n by exists (k*k)%Z; rewrite rings.M1) =>
  /Euclid's_lemma => /(_ two_is_prime) => [[ | ]] //.
  move: H two_is_prime => [] _ [] _ /[swap] [[]] /[swap] _ /[swap] H [].
    by apply H; auto; exists k.
Qed.

Theorem IZQ_add : ∀ a b : Z, a + b = (a + b)%Z.
Proof.
  rewrite /IZQ => a b.
  rewrite add_wf ? Qequiv ? integers.M3; auto using integers.zero_ne_1; ring.
Qed.

Theorem IZQ_mul : ∀ a b : Z, a * b = (a * b)%Z.
Proof.
  rewrite /IZQ => a b.
  rewrite mul_wf ? Qequiv ? integers.M3; auto using integers.zero_ne_1; ring.
Qed.

Theorem IZQ_neg : ∀ a : Z, -a = (-a)%Z.
Proof.
  rewrite /IZQ => a.
  rewrite neg_wf ? Qequiv; auto using integers.zero_ne_1; ring.
Qed.

Theorem IZQ_lt : ∀ a b, (a < b)%Z ↔ a < b.
Proof.
  (split; rewrite /lt /IZQ /sub neg_wf ? add_wf ? pos_wf ? integers.M3
                 ? (M3_r ℤ : ∀ a, a * 1 = a)%Z; auto using integers.zero_ne_1)
  => /(lt_shift ℤ_order a b) //.
Qed.

Theorem IZQ_eq : ∀ a b : Z, (a : Q) = (b : Q) ↔ a = b.
Proof.
  split => [ | ->] // /Qequiv.
  rewrite (integers.M1 _ 1) ? integers.M3 => ->; auto using integers.zero_ne_1.
Qed.

Theorem IZQ_le : ∀ a b, (a ≤ b)%Z ↔ a ≤ b.
Proof.
  rewrite /le /integers.le /ordered_rings.le => a b.
  split => [[/IZQ_lt | /IZQ_eq] | [/IZQ_lt | /IZQ_eq]]; tauto.
Qed.

Lemma canonical_form_uniq : ∀ a b c d,
    a / b = c / d → b ≠ 0%Z → d ≠ 0%Z →
    gcd(a, b) = 1 → gcd(c, d) = 1 → a ~ c ∧ b ~ d.
Proof.
  move=> a b c d /[swap] H /[swap] H0.
  rewrite Qequiv // => H1 H2 H3.
  repeat split; eapply FTA; eauto using is_gcd_sym;
    [ rewrite -? H1 | rewrite 1 ? integers.M1 ? H1 |
      rewrite ? H1 | rewrite 1 ? integers.M1 -? H1 ];
    auto using (div_mul_l ℤ), (div_mul_r ℤ), (div_refl ℤ) with Z.
Qed.

Theorem canonical_form : ∀ x, exists ! a b, gcd(a, b) = 1 ∧ x = a / b ∧ b > 0%Z.
Proof.
  move=> x.
  case (reduced_form x) as [a [b [H [-> H0]]]], (classic (a = 0)%Z)
      as [-> | H1].
  - exists 0%Z.
    split => [ | x' [y [[H1 [/[swap] /IZQ_lt /[dup] H2 /(pos_ne_0 ℤ_order)]]
                          H3 /Qequiv ]] /(_ H0) /(_ H3)].
    + exists 1%Z.
      (repeat split; auto using zero_lt_1, (div_0_r ℤ), (div_refl ℤ) with Z)
      => [ | | x' [H1 [H2 H3]]].
      * rewrite Qequiv; auto using integers.zero_ne_1; ring.
      * apply IZQ_lt, zero_lt_1.
      * move: H1 H3 => /gcd_0_l /assoc_pm [-> | ->] // /IZQ_lt.
        rewrite -[(0 < -1)%Z]/(ordered_rings.lt ℤ_order 0 (-1))%Z =>
        /lt_neg_0 /lt_antisym => /(_ zero_lt_1) //.
    + rewrite (mul_0_l ℤ y : 0 * y = 0)%Z =>
      /(@eq_sym Z) /(integral_domains.cancellation ℤ_ID) => [[ | ]] //.
  - move: H0 => /(ne0_lt_gt ℤ_order) /= =>
    [[/[dup] H0 /IZQ_lt H2 | /[dup] H0 /(lt_neg_0 ℤ_order b : b < 0 ↔ 0 < -b)%Z
                              /[dup] H2 /(pos_ne_0 ℤ_order) H3]].
    + exists a.
      split => [ | x' [y [[H3 [H4 /IZQ_lt H5]] H6]]].
      * exists b.
        split; auto using (div_1_l ℤ) with Z =>
        x' [H3 [/[swap]]] /IZQ_lt /(pos_ne_0 ℤ_order) H4 /Qequiv.
        move: integers.M1 H0 -> => /(pos_ne_0 ℤ_order) /[swap] /[apply] /(_ H4)
                                    /(cancellation_mul_r ℤ_ID) -> //.
      * move: {H2} H0 H5 H H3 H6 H4 => /lt_def [b'] /[swap] /lt_def [y'].
        rewrite ? integers.A3 =>
        [[]] /neq_sym H -> {y} [] /neq_sym H0 -> {b} H2 H3 H4 /[dup]
        /Qequiv /[swap] /canonical_form_uniq /(_ H0) /(_ H) /(_ H2) /(_ H3)
        /[swap] /(_ H0) /(_ H) /[swap] [[]] /[swap] /assoc_N -> _.
        rewrite integers.M1 => /(cancellation_mul_l ℤ_ID) -> //.
    + exists (-a)%Z.
      have H4: b ≠ 0%Z by
          move: H2 => /(pos_ne_0 ℤ_order) /[swap] -> []; rewrite neg_0 //.
      split => [ | x' [y [[H5 [H6 /IZQ_lt H7]] H8]]].
      * exists (-b)%Z.
        (apply conj; try apply conj, conj;
         rewrite -? gcd_neg ? Qequiv -? IZQ_lt //; try ring) =>
        [ | x' [H5 [/[swap] /IZQ_lt H6]]].
        -- move: H => /is_gcd_sym /gcd_neg /is_gcd_sym //.
        -- move: (H6) => /(pos_ne_0 ℤ_order) H7 /Qequiv => /(_ H4) /(_ H7).
           (have -> : (b*-a = a*-b)%Z by ring) =>
           /(cancellation_mul_l ℤ_ID) -> //.
      * move: H2 H7 H5 H6 H8 => /lt_def [b'] /[swap] /lt_def [y'].
        rewrite ? integers.A3 =>
        [[]] /neq_sym H2 -> [] /neq_sym H5 H6 H7 /[dup]
             /Qequiv /[swap] /canonical_form_uniq /(_ H4) /(_ H2) /(_ H) /(_ H7)
             /[swap] /(_ H4) /(_ H2) /[swap] [[]] _ /assoc_sym /assoc_sign /=.
        move: H6 => /[dup] {2}-> /[swap] /assoc_N -> <-.
        (have -> : (a*-b = b*-a)%Z by ring) =>
        /(cancellation_mul_l ℤ_ID) -> //.
Qed.

Theorem inv_div : ∀ a b : Z, b ≠ 0%Z → a / b = a * b^-1.
Proof.
  rewrite /IZQ => a b H.
  rewrite inv_wf // ? mul_wf ? Qequiv ? integers.M3;
    auto using integers.zero_ne_1; ring.
Qed.

Theorem Z_archimedean : ∀ x, ∃ z : Z, z ≤ x < z + 1.
Proof.
  move: pos_denom => /[swap] x /(_ x) =>
  [[a [b [/(division_algorithm a)
           [q [r [<- [/[dup] H /(le_lt_trans ℤ_order)
                       /[swap] /[dup] /IZQ_lt H0 /[swap] /[apply] /=
                       /[dup] /IZQ_lt H1 /(pos_ne_0 ℤ_order) /= H2]]]] ->]]]].
  exists q.
  have -> : (b * q + r) / b = q + r/b.
  { rewrite ? inv_div // -IZQ_add -IZQ_mul.
    field => /IZQ_eq //. }
  split.
  - move: H1 H =>
    /(inv_lt ℚ_order) /= /(mul_le_r ℚ_ring_order) /[swap] /IZQ_le
     /[swap] /[apply] /= /(add_le_l ℚ_ring_order (IZQ q)) /=.
    rewrite (mul_0_l ℚ : ∀ x, 0*x = 0) A1 A3 inv_div //.
  - rewrite -(inv_l b) 1 ? M1 ? inv_div // => [/IZQ_eq | ] //.
    apply /O1 /(O3_r ℚ_ring_order) => //.
    apply /(inv_lt ℚ_order) => //.
Qed.

Definition floor (x : Q) : Z.
Proof.
  elim (constructive_indefinite_description (Z_archimedean x)) => [z H]; auto.
Defined.

Notation "'⌊' x '⌋'" := (floor x) (format "'⌊' x '⌋'").

Theorem floor_refl : ∀ x, ⌊x⌋ ≤ x.
Proof.
  rewrite /floor /sig_rect => x.
  case constructive_indefinite_description.
  tauto.
Qed.

Theorem floor_upper : ∀ x (z : Z), z ≤ x → z ≤ ⌊x⌋.
Proof.
  rewrite /floor /sig_rect => x z H.
  case constructive_indefinite_description => [y [H0 H1]].
  apply le_not_gt => /= => H2.
  contradiction (lt_0_1 (z+-y)).
  - move: H2 => /(lt_shift ℚ_ring_order) /=.
    rewrite IZQ_neg IZQ_add IZQ_lt //.
  - move: H H1 =>
    /(le_lt_trans ℚ_ring_order) /[apply] /(O1_r ℚ_ring_order (-y)) /=.
    suff -> : (y+1+-y = 1); rewrite ? IZQ_lt -? IZQ_add -? IZQ_neg //; ring.
Qed.

Lemma floor_le : ∀ x y, x ≤ y → ⌊x⌋ ≤ ⌊y⌋.
Proof.
  pose proof (le_trans ℚ_ring_order : ∀ a b c : Q, a ≤ b → b ≤ c → a ≤ c).
  eauto using floor_refl, floor_upper.
Qed.

Lemma floor_lower : ∀ x (z : Z), x < z+1 → ⌊x⌋ ≤ z.
Proof.
  rewrite /floor /sig_rect => x z H.
  case constructive_indefinite_description => [y [H0 H1]].
  apply le_not_gt => /= H2.
  contradiction (lt_0_1 (y+-z)).
  - move: H2 => /IZQ_lt /(lt_shift ℤ_order) //.
  - move: H0 H =>
    /(le_lt_trans ℚ_ring_order) /[apply] /(O1_r ℚ_ring_order (-z)) /=.
    suff -> : (z+1+-z = 1); rewrite ? IZQ_lt -? IZQ_add -? IZQ_neg //; ring.
Qed.

Theorem floor_plus_1 : ∀ x, x < ⌊x⌋ + 1.
Proof.
  rewrite /floor /sig_rect => x.
  case constructive_indefinite_description => ? [] //.
Qed.

Theorem floor_add_int : ∀ x (z : Z), ⌊z + x⌋ = (z + ⌊x⌋)%Z.
Proof.
  move=> x z.
  apply IZQ_eq, (ordered_rings.le_antisymm ℚ_ring_order); rewrite -/le.
  - apply floor_lower.
    rewrite -IZQ_add -A2.
    apply O1, floor_plus_1.
  - apply floor_upper.
    rewrite -IZQ_add.
    apply add_le_l, floor_refl.
Qed.

Theorem Q_archimedean : ∀ x b, 0 < b → ∃ n : Z, n * b ≤ x < (n + 1) * b.
Proof.
  move=> x b =>
  /[dup] H /[dup] /(pos_ne_0 ℚ_ring_order) /= H0 /(inv_lt ℚ_order) /= H1.
  case (Z_archimedean (x*b^-1)) =>
  [n [/(mul_le_r ℚ_ring_order _ _ b) /(_ H) /=
       /[swap] /(O3_r ℚ_ring_order b)]] /(_ H) /=.
  have -> : x * b^-1 * b = x; eauto; field => //.
Qed.

Theorem inv_zero : 0^-1 = 0.
Proof.
  rewrite /inv /sig_rect.
  elim constructive_indefinite_description => x [y [H H0]].
  elim constructive_indefinite_description => z [H1].
  rewrite (Qequiv x z) ? (mul_0_r ℤ : ∀ a, a * 0 = 0)%Z ? (integers.M1 _ 1)
          ? integers.M3 /zero /embed; auto using integers.zero_ne_1 => ->.
  repeat case excluded_middle_informative => * //.
    by apply /set_proj_injective.
Qed.

Theorem inv_neg : ∀ a, -a^-1 = (-a)^-1.
Proof.
  move=> a.
  case (classic (a = 0)) => [-> | H].
  - rewrite -[-0]/(rings.neg _ (rings.zero ℚ))
    -neg_0 inv_zero -{2}[0]/(rings.zero ℚ) neg_0 //.
  - by apply /(fields.inv_neg ℚ).
Qed.

Definition inv_ne_0 := fields.inv_ne_0 ℚ : ∀ a, a ≠ 0 → a^-1 ≠ 0.

Theorem inv_inv : ∀ a, a^-1^-1 = a.
Proof.
  move: classic => /[swap] a /(_ (a = 0)) [-> | /(fields.inv_inv ℚ)] //.
    by rewrite ? inv_zero.
Qed.

Theorem inv_mul : ∀ a b, a^-1 * b^-1 = (a*b)^-1.
Proof.
  move: classic =>
  /[swap] a /[swap] b /[dup] /(_ (a = 0)) /[swap] /(_ (b = 0)) [-> | ?]
   [-> | ?]; rewrite ? inv_zero -[mul]/(rings.mul ℚ_ring) ? mul_0_l ? mul_0_r
                                      /= ? inv_zero; by field.
Qed.

Theorem one_lt_2 : 1 < 2.
Proof.
  apply /IZQ_lt /(one_lt_2 ℤ_order).
Qed.

Definition pow := pow ℚ : Q → Z → Q.
Infix "^" := pow : Q_scope.

Definition pow_0_r := pow_0_r ℚ : ∀ a, a ^ 0 = 1.

Theorem pow_0_l : ∀ a : Z, a ≠ 0%Z → 0 ^ a = 0.
Proof.
  move: classic => /[swap] a /(_ (a < 0)%Z) [H H0 | H /(pow_0_l ℚ)] //.
  (rewrite /pow /fields.pow /integer_powers.pow;
   repeat case excluded_middle_informative; try tauto) =>
  [/[dup] /(le_not_gt ℤ_order) H1 | /unit_nonzero H1] //.
Qed.

Theorem pow_neg : ∀ a b, a ^ (-b) = (a^-1) ^ b.
Proof.
  move: classic =>
  /[swap] a /[swap] b /[dup] /(_ (a = 0)) /[swap] /(_ (b = 0%Z)) [-> | H]
   [-> | ]; try (by apply (pow_neg ℚ)); rewrite inv_zero.
  - f_equal; ring.
  - rewrite ? pow_0_l //.
    contradict H.
    ring [H].
Qed.

Theorem inv_pow : ∀ a, a ^ (-1) = a^-1.
Proof.
  move: classic => /[swap] a /(_ (a = 0)) [-> | H].
  - rewrite pow_neg inv_zero (pow_1_r ℚ : ∀ a, a^1 = a) //.
  - apply (inv_unique ℚ).
    rewrite pow_neg (pow_1_r ℚ : ∀ a, a^1 = a) inv_r //.
Qed.

Theorem pow_mul_l : ∀ a b c, (a * b) ^ c = a ^ c * b ^ c.
Proof.
  move: classic =>
  /[swap] a /[swap] b /[swap] c /[dup] /(_ (a = 0)) /[swap]
   /[dup] /(_ (b = 0)) /[swap] /(_ (c = 0%Z)) [-> | ?] [-> | ?] [-> | ?];
    rewrite -[mul]/(rings.mul ℚ_ring) ? mul_0_l ? mul_0_r /=
                  ? pow_0_r ? pow_0_l //; try (by apply (pow_mul_l ℚ)); ring.
Qed.

Theorem neg_pow : ∀ a b, a ^ (-b) = (a ^ b)^-1.
Proof.
  move: classic => /[swap] a /(_ (a = 0)) [-> | ?] b;
                     last by apply (fields.neg_pow ℚ).
  case (classic (b = 0%Z)) => [-> | H].
  - rewrite pow_0_r -[integers.neg]/(rings.neg ℤ) -(neg_0 ℤ) pow_0_r.
    apply /eq_sym /(fields.inv_one ℚ).
  - rewrite ? pow_0_l ? inv_zero //.
    contradict H.
    ring [H].
Qed.

Theorem pow_mul_r : ∀ a b c, a ^ (b * c) = (a ^ b) ^ c.
Proof.
  move: classic => /[swap] a /[dup] /(_ (a = 0)) [-> | H] /[swap] b /[swap] c
  => [/(_ (b*c = 0)%Z)
       [/[dup] {2}-> /(cancellation_0_mul ℤ_order) [-> | ->] |
        /[dup] H /(cancellation_ne0 ℤ) [H0 H1]] | _];
       rewrite ? pow_0_r ? pow_0_l // /pow ? (pow_1_l ℚ) //.
    by apply /(fields.pow_mul_r ℚ).
Qed.

Theorem pow_div_distr : ∀ a b c, (a * b^-1) ^ c = a ^ c * (b ^ c)^-1.
Proof.
  move=> a b c.
  rewrite pow_mul_l -neg_pow pow_neg //.
Qed.

Lemma a_g_pow_ineq : ∀ x n, 0 < x → (0 < n)%Z → 1 + n * x ≤ (1 + x) ^ n.
Proof.
  move=> x n H H0.
  induction n using strong_induction.
  (case (integers.T 1 n) =>
   [[H2 _] | [[_ [<- _]] | [_ [_ H2]]]]; last by contradiction (lt_0_1 n));
    last by rewrite M3 (pow_1_r ℚ: ∀ a, a^1 = a); right.
  have: (0 < n+-1)%Z => [ | /[dup] H3 /IZQ_lt H4].
  { rewrite -(integers.A4 1) ? (integers.A1 _ (-1)).
      by apply integers.O1. }
  have: (0 < 1+x) => [ | /[dup] H5 /(pos_ne_0 ℚ_ring_order) H6].
  { apply (lt_trans _ 1); try apply (ordered_rings.zero_lt_1 ℚ_ring_order).
    move: H A1 A3 => /(O1 1) /[swap] -> /[swap] -> //. }
  (case (H1 (n+-1)%Z); repeat split; auto) =>
  /= [ | /(O3 ℚ_ring_order (1+x) _ _ H5) | H7].
  - have {2}-> : (n = n+(-1)+1)%Z by ring.
    apply (ordered_rings.lt_succ ℤ_order).
  - rewrite -{2}(fields.pow_1_r ℚ (1+x)) -(fields.pow_add_r ℚ) //=.
    (have -> : (1+(n+-1) = n)%Z by ring) => *.
    eapply or_introl, lt_trans; eauto.
    rewrite D1 M3 (M1 x) D1 A2 -(A2 1) -D1 -IZQ_add -IZQ_neg
    -(A2 n) (A1 (-1)) A4 (A1 _ 0) A3 -{1}(A3 (1+n*x)) (A1 0) IZQ_neg ? IZQ_add.
    auto using O1, O2.
  - have {2}-> : n = (n+(-1)+1)%Z by ring.
    rewrite /pow (pow_add_r ℚ) // -/pow -H7 /pow (pow_1_r ℚ)
    -IZQ_add /= ? D1 M3 -IZQ_neg -[IZQ 1%Z]/one -(A3 (1+n*x)) (A1 0).
    have ->: 1+x+(n*x*(1+x)+-1*x*(1+x)) = 1+n*x+x*x*(n+-1) by ring.
    rewrite IZQ_neg IZQ_add /le /ordered_rings.le /=.
    auto using O1, O2.
Qed.

Theorem pos_pow_archimedean : ∀ a r, 1 < r → ∃ n, (0 < n)%Z ∧ a < r ^ n.
Proof.
  move: classic =>
  /[swap] a /(_ (1 < a))
   [H r /[dup] H0 /(lt_shift ℚ_ring_order)
      /(Q_archimedean (a+-1)) /= [n [H1 /[dup] H2 /(O1 1)]] |
    /(le_not_gt ℚ_ring_order) H r H0].
  - (have -> : 1 + (a + -1) = a by ring) => H3.
    exists (n+1)%Z.
    have H4: (0 < n+1)%Z.
    { eapply IZQ_lt, (pos_div_r ℚ_ring_order (r+-1)) =>
      /=; [ | rewrite -IZQ_add; eapply lt_trans; eauto ];
        rewrite -[lt]/(ordered_rings.lt ℚ_ring_order) -lt_shift //. }
    ((case (a_g_pow_ineq (r + - 1) (n+1));
      try have -> : (1+(r+-1) = r) by ring); auto) =>
    [ | | <-]; rewrite -? IZQ_add; eauto using lt_trans.
    rewrite -[lt]/(ordered_rings.lt ℚ_ring_order) -lt_shift //.
  - exists 1%Z.
    rewrite /pow (pow_1_r ℚ) -[lt]/(ordered_rings.lt ℚ_ring_order).
    split; eauto using integers.zero_lt_1, le_lt_trans.
Qed.

Theorem neg_pow_archimedean : ∀ a r, 0 < a → 1 < r → ∃ n, (n < 0)%Z ∧ r ^ n < a.
Proof.
  move=> a r H /[dup] /(pos_pow_archimedean (a^-1) r)
           [n [/[dup] ? /(neg_lt_0 ℤ_order) /= ? ?]] /(one_lt ℚ_ring_order) /=.
  exists (-n)%Z.
  split; auto.
  apply (lt_cross_inv ℚ_order) => //=.
  + by apply (pow_pos ℚ_order).
  + rewrite neg_pow inv_inv //.
Qed.

Theorem square_in_interval : ∀ a, 1 < a → ∃ r, 0 < r ∧ 1 < r * r < a.
Proof.
  move=> a H.
  have: (0 < 3)%Z => [ | /[dup] H0 /[dup] /(lt_neq ℤ_order) H1
                          /IZQ_lt /[dup] H2 /(inv_lt ℚ_order) /= H3].
  { rewrite -[integers.lt]/(ordered_rings.lt ℤ_order).
    eauto using (ordered_rings.O0 ℤ_order), (ordered_rings.zero_lt_1 ℤ_order). }
  case (classic (2 < a)) => [H4 | H4].
  - exists (4/3).
    repeat split.
    + rewrite inv_div //.
      apply /O2 => //.
      apply IZQ_lt.
      rewrite -[integers.lt]/(ordered_rings.lt ℤ_order).
      eauto using (ordered_rings.O0 ℤ_order), (ordered_rings.zero_lt_1 ℤ_order).
    + rewrite -(M3 1).
      suff H5: 1 < 4 / 3.
      * apply (lt_cross_mul ℚ_ring_order) =>
        //; auto using (ordered_rings.zero_lt_1 ℚ_ring_order).
      * rewrite inv_div //.
        apply (lt_div ℚ_order) => //.
        apply IZQ_lt, (O1_r ℤ_order), (O1_r ℤ_order), IZQ_lt, one_lt_2.
    + eapply lt_trans; eauto.
      rewrite inv_div // {2}(M1 4) -? M2 (M1 4) -(M3 2) -(M3 2)
      -(inv_l 3) ? IZQ_eq // -? (M2 (3^-1)) ? (M2 3) (M1 3) -? M2.
      repeat apply (O3 ℚ_ring_order) => //.
      rewrite -? IZQ_add M2 ? D1 ? M3 ? D1 ? M3 -? A2 -{16}(A3 1%Z) (A1 0).
      repeat apply O1.
      apply (zero_lt_2 ℚ_ring_order).
  - set (r := 1+(a+-1) * 3^-1).
    exists r.
    have: 1 < r => [ | /[dup] H5 /(one_lt ℚ_ring_order) /= H6].
    { rewrite -(A3 1) (A1 0) /r.
      apply O1, O2 => //.
      rewrite -[lt]/(ordered_rings.lt ℚ_ring_order) -lt_shift //. }
    repeat split; auto.
    + rewrite -(M3 1).
      apply (lt_cross_mul ℚ_ring_order) =>
      //; auto using (ordered_rings.zero_lt_1 ℚ_ring_order).
    + have: r + 1 < 3 => [ | /(O3_r ℚ_ring_order (-1+r))].
      { rewrite -? IZQ_add /r -? A2 -(A1 1) -[IZQ 1]/one
        -{6}(inv_l 3) ? IZQ_eq // -(M1 (3^-1)).
        repeat apply O1.
        apply (O3 ℚ_ring_order) => //=.
        have: 2 < 4.
        { rewrite -? IZQ_add -{2}(A3 1%Z) (A1 0) -? A2.
          repeat apply O1.
          apply (zero_lt_2 ℚ_ring_order). }
        move: H4 => /(le_not_gt ℚ_ring_order) /le_lt_trans =>
        /(_ (4 : Q)) /[apply] /(O1_r ℚ_ring_order (-1)).
        rewrite -? IZQ_add -rings.A2 rings.A4 rings.A3_r //. }
      rewrite {4}/r {3}A2 (A1 (-1) 1) A4 A3 /= (M1 3) -M2 inv_l ? IZQ_eq //
      -(M1 1) M3 (A1 (-1)) -{1}[lt]/(ordered_rings.lt ℚ_ring_order) -lt_shift
      => /(_ H5) /(O1 1).
      have -> : 1 + (r + 1) * (r + -1) = r * r by ring.
        by have -> : 1 + (a + -1) = a by ring.
Qed.

Theorem division_signed : ∀ a b : Z,
    (0 < b)%Z → ∃ q r : Z, 0 ≤ r ≤ b / 2 ∧ b*q + (-1)^⌊2 * a / b⌋ * r = a.
Proof.
  move=> a b /[dup] H /[dup] /(lt_neq ℤ_order) H0 /[dup] /IZQ_lt /[dup] H1
           /[dup] /(inv_lt ℚ_order) /[dup] /= H2 /(lt_neq ℚ_ring_order) H3
           /(lt_neq ℚ_ring_order) H4 /(division_algorithm a b)
           [q [r [<- {a} [/[dup] H5 /IZQ_le H6 /[dup] H7 /[dup]
                           /(lt_shift ℤ_order) /= H8 /IZQ_lt H9]]]].
  (have: 0 < 2 by rewrite -IZQ_add; apply (zero_lt_2 ℚ_ring_order)) =>
  /[dup] H10 /[dup] /IZQ_lt /[dup] H11 /(lt_neq ℤ_order) H12
   /(lt_neq ℚ_ring_order) H13.
  case (classic (r < b/2)) => [H14 | /[dup] H14 /(le_not_gt ℚ_ring_order) H15].
  - exists q, r.
    repeat split; try by (apply IZQ_le || left).
    rewrite -IZQ_add -IZQ_mul -{2}(M3 r).
    repeat f_equal.
    suff -> : ⌊2 * (b * q + r) / b⌋ = (2*q)%Z.
    { rewrite pow_mul_r /pow /integers.one INZ_add
      -pow_wf add_1_r /pow_N pow_2_r rings.mul_neg_neg rings.M3 pow_1_l //. }
    apply (ordered_rings.le_antisymm ℤ_order); apply IZQ_le.
    + apply /floor_lower.
      rewrite inv_div -? IZQ_mul -? M2 // -(IZQ_add _ r)
      -IZQ_mul D1 (M1 (b*q)) M2 inv_l // M3
      -[mul]/(rings.mul ℚ) D1_l /= -(inv_l (2*b^-1)) ? M2 ? (M1 2 r) -? M2;
        auto using (ne0_cancellation (integral_domain_from_field ℚ)).
      have -> : (2 * b^-1)^-1 = b / 2 by
          rewrite inv_div -? IZQ_eq //; field => //.
      apply /O1 /(O3_r ℚ_ring_order) => //=.
      apply /O2 => //.
    + apply /floor_upper.
      rewrite inv_div -? IZQ_mul -? M2 // -(IZQ_add _ r)
      -IZQ_mul D1 (M1 b q) -M2 (M1 b) inv_l // (M1 q) M3 A1 -{1}(A3 q).
      apply mul_le_l => //.
      apply add_le_r, mul_nonneg_nonneg, or_introl => //.
  - exists (q+1)%Z, (b+-r)%Z.
    repeat split; first by apply IZQ_le, or_introl.
    { move: H15.
      rewrite /le le_shift -{1}/le le_shift /= -/le inv_div //
                               -? IZQ_add -IZQ_neg -[IZQ 1]/one.
      have -> : (b * (1 + 1)^-1 + - (b + - r) =
                 r + - (b * (1 - (1 + 1)^-1))) by ring.
      suff -> : 1 - (1 + 1)^-1 = (1 + 1)^-1 => //.
      apply (inv_unique ℚ) => /=.
      rewrite M1 D1 -[neg]/(rings.neg ℚ) -(mul_neg_1_l ℚ) /=
      -M2 inv_l ? IZQ_add // M1 -IZQ_add D1 -? (M1 1) ? M3 -A2 A4 A1 A3 //. }
    suff -> : (-1) ^ ⌊2 * (b * q + r) / b⌋ = -1.
    { rewrite -? IZQ_add -IZQ_neg -IZQ_mul -[IZQ 1]/one.
      ring. }
    suff -> : ⌊2 * (b * q + r) / b⌋ = (2*q+1)%Z.
    { rewrite /pow (pow_add_r ℚ) ? pow_1_r -/pow ? pow_mul_r ? INZ_add /pow
              -? pow_wf /pow_N ? add_1_r ? pow_2_r ? rings.mul_neg_neg /=
              ? M3 ? pow_1_l ? M3; auto using (minus_one_nonzero ℚ). }
    apply (ordered_rings.le_antisymm ℤ_order); apply IZQ_le.
    + apply floor_lower.
      rewrite inv_div -? IZQ_mul -? M2 // -(IZQ_add _ r)
      -IZQ_mul D1 (M1 (b*q)) M2 inv_l // M3 -(IZQ_add (2*q)) -IZQ_mul
      -[mul]/(rings.mul ℚ) (D1_l ℚ_ring) -A2 /= -[one]/(IZQ 1) IZQ_add
      -{4}(M3 2) (M1 1) -(inv_l b) // (M1 _ b).
      apply O1, (O3 ℚ_ring_order) => //.
      apply (mul_lt_r ℚ_ring_order) => //.
    + apply floor_upper.
      rewrite inv_div -? IZQ_mul // -M2 -(IZQ_add _ r)
      -IZQ_mul D1 (M1 (b*q)) M2 inv_l // M3 -[mul]/(rings.mul ℚ) (D1_l ℚ_ring)
      -IZQ_add /= -IZQ_mul -[IZQ 1]/one -(inv_l b) // M2 (M1 _ (b^-1))
      -{2}(M3 b) -(inv_l 2) // (M1 _ 2) -M2 -(M1 b) -inv_div //.
      apply add_le_l, mul_le_l => //.
      apply mul_le_l => //.
Qed.

Theorem QR_epsilon_construction :
  ∀ a b : Z, (0 < a → 0 < b → 0 ≤ ⌊a / b⌋)%Z.
Proof.
  move=> a b /IZQ_lt H /[dup] H0 /IZQ_lt H1.
  rewrite inv_div; auto using (pos_ne_0 ℤ_order).
  apply IZQ_le, floor_upper, (mul_nonneg_nonneg ℚ_ring_order), or_introl.
  - by apply or_introl.
  - by apply (inv_lt ℚ_order).
Qed.

Definition QR_ε_exp (a b : Z) : N.
Proof.
  case (excluded_middle_informative (0 < a)%Z) => [H | H].
  - case (excluded_middle_informative (0 < b)%Z) => [H0 | H0].
    + eapply QR_epsilon_construction, le_def in H0; try apply H.
      elim (constructive_indefinite_description H0) => [c H1].
      exact c.
    + exact 0%N.
  - exact 0%N.
Defined.

Theorem IZQ_pow : ∀ (a : Z) (n : N), a^n = (a^n : Z)%Z.
Proof.
  move=> a n.
  case (classic (a = 0%Z)) => [-> | H].
  - case (classic (n = 0%N)) => [-> | H0].
    + rewrite /pow rings.pow_0_r -/pow pow_0_r //.
    + rewrite rings.pow_0_l // pow_0_l // INZ_eq //.
  - induction n using Induction.
    + rewrite pow_0_r rings.pow_0_r //.
    + rewrite /pow pow_succ_r -add_1_r -INZ_add pow_add_r ? IZQ_eq // pow_1_r
      -IZQ_mul -pow_wf -IHn pow_wf //.
Qed.

Definition QR_ε (a b : Z) := ((-1) ^ (QR_ε_exp a b) : Z)%Z.

Theorem division_QR : ∀ a b : Z,
    (0 < a → 0 < b →
     ∃ q r : Z, 0 ≤ r ≤ ⌊b / 2⌋ ∧ b * q + QR_ε (2 * a) b * r = a)%Z.
Proof.
  rewrite /QR_ε /QR_ε_exp /sig_rect => a b H /[dup] H0 /division_signed =>
  /(_ a) [q [r [[/[dup] H1 /IZQ_le H2 /[dup] H3 /floor_upper /IZQ_le H4] H5]]].
  (repeat elim excluded_middle_informative; try tauto) =>
  [{}H0 H6 | []]; last by apply (mul_pos_pos ℤ_order);
    auto; apply (zero_lt_2 ℤ_order).
  elim constructive_indefinite_description => x H7.
  exists q, r.
  repeat split; auto.
  rewrite -IZQ_eq -H5 H7 integers.A3 -IZQ_add -? IZQ_mul -IZQ_pow -IZQ_neg //.
Qed.

Theorem IZQ_div : ∀ a b : Z, b ≠ 0%Z → b｜a → a / b = (a / b)%Z.
Proof.
  move=> a b H H0.
  apply Qequiv; auto using integers.zero_ne_1.
  rewrite integers.div_inv_l // integers.M1 integers.M3 //.
Qed.
