Require Export ssreflect ssrbool ssrfun naturals.

Definition swap {X Y} (a b : X) (f : X → Y) : X → Y.
Proof.
  move=> x.
  elim (excluded_middle_informative (x = a)) => *.
  - exact (f b).
  - elim (excluded_middle_informative (x = b)) => *.
    + exact (f a).
    + exact (f x).
Defined.

Theorem swap_refl : ∀ {X Y} a (f : X → Y), swap a a f = f.
Proof.
  move=> X Y a f.
  extensionality x.
  rewrite /swap.
  elim: excluded_middle_informative => /= [-> | ] //.
Qed.

Theorem swap_sym : ∀ {X Y} a b (f : X → Y), swap a b f = swap b a f.
Proof.
  move=> X Y a b f.
  extensionality x.
  rewrite /swap.
  repeat (elim: excluded_middle_informative => /=) => [-> | ] //.
Qed.

Theorem swap_left : ∀ X Y (a b : X) (f : X → Y), swap a b f b = f a.
Proof.
  move=> X Y a b f.
  rewrite /swap /sumbool_rect.
  (repeat (elim: excluded_middle_informative => /=)) => [-> | | ] //.
Qed.

Theorem swap_right : ∀ X Y (a b : X) (f : X → Y), swap a b f a = f b.
Proof.
  move=> X Y a b f.
  rewrite /swap /sumbool_rect.
  (repeat (elim: excluded_middle_informative => /=)) => [ | -> | ] //.
Qed.

Section Iterated_op_construction.

  Context {R : Type}.
  Variable op : R → R → R.
  Variable f : N → R.
  Variable start : R.
  Infix "*" := op.
  Hypothesis M2 : ∀ x y z, x * (y * z) = (x * y) * z.

  Definition iterate_with_bounds (a b : N) : R.
  Proof.
    elim (excluded_middle_informative (a ≤ b)) =>
    [/constructive_indefinite_description [c H] | H].
    - exact (iterated_op op (f a) (λ x, f (a + x + 1)%N) c).
    - exact start.
  Defined.

  Theorem iterate_neg : ∀ a b, b < a → iterate_with_bounds a b = start.
  Proof.
    rewrite /iterate_with_bounds => a b.
    elim: excluded_middle_informative => H0 => /lt_not_ge //.
  Qed.

  Theorem iterate_0 : ∀ a, iterate_with_bounds a a = f a.
  Proof.
    rewrite /iterate_with_bounds => a.
    elim: excluded_middle_informative => H /=.
    - elim: constructive_indefinite_description => x.
      rewrite -{2}[a]add_0_r.
      move: (@iterated_op_0) => /[swap] /naturals.cancellation_add -> -> //.
    - move: H => /lt_not_ge /lt_irrefl => //.
  Qed.

  Theorem iterate_succ : ∀ a b,
      a ≤ b → iterate_with_bounds a (S b) = iterate_with_bounds a b * (f (S b)).
  Proof.
    rewrite /iterate_with_bounds => a b H.
    (repeat (elim: excluded_middle_informative => /=); try tauto) => H0 H1.
    - (repeat (elim: constructive_indefinite_description)) => x H2 y H3.
      suff -> : y = S x.
      + rewrite iterated_op_succ H2 add_1_r //.
      + apply (cancellation_add a).
        rewrite add_succ_r H2 H3 //.
    - move: H1 H => /lt_not_ge /[swap] => /le_lt_succ /lt_antisym /[apply] //.
  Qed.

  Theorem iterate_lower : ∀ a c,
      iterate_with_bounds a (S a+c) =
      op (f a) (iterate_with_bounds (S a) (S a+c)).
  Proof.
    move=> a c.
    elim/Induction: c => [| n H].
    - rewrite add_0_r iterate_succ ? iterate_0; auto using le_refl.
    - rewrite add_succ_r ? iterate_succ ? H ? M2 //;
      [ eapply le_trans; eauto using le_succ | ]; now (exists n).
  Qed.

  Theorem iterate_1 : iterate_with_bounds 0 1 = op (f 0%N) (f 1%N).
  Proof.
    rewrite /naturals.one iterate_succ ? iterate_0; auto using zero_le.
  Qed.

  Theorem iterate_2 : iterate_with_bounds 0 2 = op (op (f 0%N) (f 1%N)) (f 2).
  Proof.
    rewrite iterate_succ ? iterate_1 ; auto using zero_le.
  Qed.

  Theorem iterate_succ_lower_limit : ∀ a b,
      a ≤ S b → start * (f (S b)) = f (S b) →
      iterate_with_bounds a (S b) = iterate_with_bounds a b * (f (S b)).
  Proof.
    move=> a b /[dup] => H.
    elim: (classic (a ≤ b)); auto using iterate_succ => /[dup] => H0.
    suff -> : (a = S b).
    - rewrite iterate_0 iterate_neg; auto using succ_lt.
    - move: H0 H => /lt_not_ge => /lt_le_succ /le_antisymm /[apply] //.
  Qed.

End Iterated_op_construction.

Theorem iterate_extensionality : ∀ X op f g (start : X) a b,
      (∀ k, a ≤ k ≤ b → f k = g k) →
      iterate_with_bounds op f start a b = iterate_with_bounds op g start a b.
Proof.
  move=> X op f g start a b.
  elim: (classic (a ≤ b)) =>
  [[c <-] | H]; last rewrite ? iterate_neg ? lt_not_ge //.
  elim/Induction: c => [| n H H0]; first rewrite add_0_r ? iterate_0;
                         eauto using le_refl.
  rewrite add_succ_r !iterate_succ ? H -? add_succ_r ? H0; try (exists n); auto.
  - move: H0 => /[swap] => k /[swap] => H1 -> //.
    rewrite add_succ_r.
    intuition eauto using le_trans, le_succ.
  - split; eauto using le_refl.
    now (exists (S n)).
Qed.

Section Iterated_op_theorems.

  Context {X : Type}.
  Variable op : X → X → X.
  Variable s : X.
  Infix "*" := op.
  Hypothesis M1 : ∀ x y, x * y = y * x.
  Hypothesis M2 : ∀ x y z, x * (y * z) = (x * y) * z.

  Theorem iterate_shift : ∀ f a c,
      iterate_with_bounds op f s a (a+c) =
      iterate_with_bounds op (λ n, (f (n+a)%N)) s 0 c.
  Proof.
    move=> f a c.
    elim/Induction: c => [|n H].
    - rewrite add_0_r ? iterate_0 add_0_l //.
    - rewrite add_succ_r ? iterate_succ ? H -? add_succ_r 1 ? (add_comm (S n));
        auto using zero_le; now (exists n).
  Qed.

  Lemma iterate_swap_upper_two : ∀ m f,
    iterate_with_bounds op f s 0 (S (S m)) =
    iterate_with_bounds op (swap (S m) (S (S m)) f) s 0 (S (S m)).
  Proof.
    move=> m f.
    rewrite ? iterate_succ; auto using zero_le.
    rewrite -M2 (M1 (f (S m))) M2 /swap /sumbool_rect.
    do 2 f_equal; repeat elim excluded_middle_informative => /=; try congruence.
    apply /iterate_extensionality => k.
    (repeat elim excluded_middle_informative; auto) => -> => [[_ H] | _ [_ H]].
    - move: H => /not_succ_le //.
    - move: H (le_succ m) => /le_trans /[apply] /not_succ_le //.
  Qed.

  Lemma iterate_swap_upper_one : ∀ n f i,
      0 ≤ i ≤ n → iterate_with_bounds op (swap i n f) s 0 n =
                  iterate_with_bounds op f s 0 n.
  Proof.
    move=> n.
    elim/Induction: n => [f i [H H0] | n H f i [H0 H1]].
    { move: le_antisymm H H0 => /[apply] /[apply] <-.
      rewrite ? iterate_0 swap_refl //. }
    move: H1 => /le_lt_or_eq.
    elim => [| <-]; try rewrite swap_refl //.
    elim (classic (1 = S n)%N) => [<- |].
    { move /(_ 0):PA4 => /[swap] /(squeeze_lower _ _ H0) ->.
      rewrite /naturals.one /swap ? iterate_succ ? iterate_0 /sumbool_rect;
        auto using zero_le.
      repeat (elim: excluded_middle_informative); intuition congruence. }
    rewrite neq_sym /not /naturals.one PA5_iff.
    move: H => /[swap] /succ_0 => [[m]] -> => H H1.
    elim (classic (i = S m)) => [-> |]; try rewrite -iterate_swap_upper_two //.
    symmetry.
    rewrite iterate_swap_upper_two iterate_succ
    -1 ? (H _ i) ? iterate_succ -? M2;
      repeat split; auto using zero_le, le_refl; first by now apply le_lt_succ.
    f_equal; rewrite 1 ? M1 /swap /sumbool_rect.
    - apply iterate_extensionality => k [H3 H4].
      repeat elim excluded_middle_informative; move=> *; subst; try tauto.
      + move: H4 => /not_succ_le //.
      + move: H4 (le_succ m) => /le_trans /[apply] /not_succ_le //.
    - f_equal; repeat elim excluded_middle_informative;
        move=> *; subst; try tauto; try now contradiction (neq_succ (S m)).
      move: H1 => /lt_irrefl //.
  Qed.

  Theorem iterate_swap_0 : ∀ n f i j,
      0 ≤ i ≤ n → 0 ≤ j ≤ n →
      iterate_with_bounds op (swap i j f) s 0 n =
      iterate_with_bounds op f s 0 n.
  Proof.
    move=> n.
    elim/Induction: n => [| n H] => f i j [H0 H1] [H2 H3].
    { rewrite ? iterate_0 1 ? (le_antisymm i 0)
              1 ? (le_antisymm j 0) ? swap_refl //. }
    move: H1 H3 => /le_lt_or_eq /[swap] /le_lt_or_eq.
    elim; move /[swap]; elim; move /[dup] => H1 /[swap] /[dup] => H3; subst.
    - move /le_lt_succ /[swap] /le_lt_succ.
      rewrite ? iterate_succ; auto using zero_le => /[dup] H4 /[swap] /[dup] H5.
      rewrite H /swap /sumbool_rect; eauto.
      (repeat (elim: excluded_middle_informative); auto)
      => <-; by move=> _ /not_succ_le.
    - rewrite swap_sym iterate_swap_upper_one ? (le_lt_or_eq j); intuition.
    - rewrite iterate_swap_upper_one ? (le_lt_or_eq i); intuition.
    - rewrite swap_refl //.
  Qed.

  Theorem iterate_swap : ∀ a b f i j,
      a ≤ i ≤ b → a ≤ j ≤ b →
      iterate_with_bounds op (swap i j f) s a b =
      iterate_with_bounds op f s a b.
  Proof.
    move: classic => /[swap] a /[swap] b /(_ (a ≤ b))
                      [[c <-] | H] f i j [[x <-]] /[swap] [[[y <-]] | [[y <-]]].
    - rewrite ? iterate_shift ? (add_comm a) -? O1_le_iff => H H0.
      rewrite -(iterate_swap_0 _ _ x y); eauto using zero_le.
      apply iterate_extensionality => k H1.
      rewrite /swap /sumbool_rect.
      repeat elim excluded_middle_informative; auto; try congruence;
        rewrite -? (add_comm a) => /cancellation_add //.
    - rewrite /iterate_with_bounds /sumbool_rect.
      elim excluded_middle_informative; tauto.
  Qed.

  Theorem iterate_bijection_0 : ∀ n f g,
      (∀ j, 0 ≤ j ≤ n → exists ! i, 0 ≤ i ≤ n ∧ f i = g j) →
      (∀ i, 0 ≤ i ≤ n → exists ! j, 0 ≤ j ≤ n ∧ f i = g j) →
      iterate_with_bounds op f s 0 n = iterate_with_bounds op g s 0 n.
  Proof.
    induction n using Induction => [ | f g H H0].
    { move=> f g /(_ 0%N (conj (le_refl 0%N) (le_refl 0%N)))
               [j [[[/le_antisymm /[apply]] <-] *]].
      rewrite ? iterate_0 //. }
    have E1: ∀ j i1 i2, 0 ≤ i1 ≤ S n → 0 ≤ i2 ≤ S n → 0 ≤ j ≤ S n →
                        f i1 = g j → f i2 = g j → i1 = i2.
    { move=> j i1 i2 H1 H2 H3 H4 H5.
      elim (H j); auto => [k [[[H6 H7] H8] /[dup] /(_ i1) H9 /(_ i2) H10]].
      intuition congruence. }
    have E2: ∀ i j1 j2, 0 ≤ i ≤ S n → 0 ≤ j1 ≤ S n → 0 ≤ j2 ≤ S n →
                        f i = g j1 → f i = g j2 → j1 = j2.
    { move=> i j1 j2 H1 H2 H3 H4 H5.
      elim (H0 i); auto => [k [[[H6 H7] H8] /[dup] /(_ j1) H9 /(_ j2) H10]].
      intuition congruence. }
    elim (H (S n)); eauto using le_refl, zero_le => k.
    elim (classic (k = S n)) =>
    [-> [[H1 H2] H3 {k}] | H1 [[[H2 /le_lt_or_eq [H3 | H3]] H4] H5]]; try tauto.
    { rewrite ? iterate_succ; auto using zero_le.
      f_equal; auto.
      apply IHn =>
      i [H4 H5]; [set (Z := H) | set (Z := H0)];
        (elim (Z i); eauto using le_trans, le_succ =>
      [k [[/and_comm [/le_lt_or_eq [/le_lt_succ ? | ->] *]]]];
        [exists k | exists (S n)]; repeat split; eauto using zero_le;
        intuition eauto using le_trans, le_succ;
        (have -> : (S n) = i by eauto 6 using le_trans, le_succ) => //). }
    rewrite -(iterate_swap _ _ f k (S n)); repeat split;
      eauto using le_refl, zero_le; try eapply lt_le_trans; eauto using le_refl.
    rewrite ? iterate_succ ? swap_left ? H4; auto using zero_le.
    f_equal.
    apply IHn => [j [H6 H7] | i].
    - elim (H j); eauto using le_trans, le_succ =>
      [l [[/and_comm [/le_lt_or_eq [/le_lt_succ H8 | ->] H9] H10] H11]].
      + exists l.
        repeat split; auto using zero_le; try now apply le_lt_succ.
        * rewrite -H10 /swap /sumbool_rect.
          move: H8 H9 H10 H11 (H7) => /le_lt_succ.
          (repeat elim excluded_middle_informative; auto) =>
          -> => [ {l} | ? /lt_irrefl] // => [[H8 H9] H10] H11 H12.
          (have <- : (S n) = j) => [ | /not_succ_le Z] //.
          eauto 6 using zero_le, le_refl, le_trans, le_succ.
        * rewrite /swap /sumbool_rect => x'.
          (repeat elim excluded_middle_informative) =>
          [-> [H12 H13] | -> ? [[?]] /not_succ_le | H12 H13 [[H14 H15] H16]]
            //; [ replace l with (S n) in H8;
                  try now contradiction (not_succ_le n) | ];
            apply (E1 j); eauto using zero_le, le_refl, le_trans, le_succ.
      + exists k.
        (repeat split; auto using zero_le; try now apply le_lt_succ) =>
        [ | x' [[H8]]]; rewrite /swap /sumbool_rect;
          (repeat elim excluded_middle_informative; try tauto; try congruence)
        => [ ->  ? /not_succ_le | ] // => H12 H13 H14 H15.
        contradict H12.
        apply (E1 j); eauto using zero_le, le_refl, le_trans, le_succ.
    - elim (classic (i = k)) =>
      [-> [H6 H7] | H6 [H7 H8]]; rewrite /swap /sumbool_rect.
      + elim (H0 (S n)); eauto using zero_le, le_refl =>
        [l [[[H8 /le_lt_or_eq H9] H10] H11]].
        exists l.
        (elim excluded_middle_informative; try tauto) => _.
        (repeat split; auto using zero_le) => [ | x' [[H12 H13] H14]].
        * move: H9 H8 H10 H11 => [/le_lt_succ | ->] * //.
          contradict H1.
          apply (E1 (S n)); eauto using zero_le, le_refl, le_trans, le_succ.
        * eauto using le_trans, le_succ.
      + elim (H0 i); eauto using le_trans, le_succ =>
        [l [[[H9 /le_lt_or_eq H10] H11] H12]].
        exists l.
        (repeat split; auto) => [ | | x' [[H13 H14]]].
        * apply le_lt_succ.
          move: H3 H10 H9 H11 H12 => /le_lt_succ H3 [ | ->] // *.
          contradict H6.
          apply (E1 (S n)); eauto using zero_le, le_refl, le_trans, le_succ.
        * repeat elim excluded_middle_informative => *; subst => //.
          now apply not_succ_le in H8.
        * repeat elim excluded_middle_informative;
            eauto using le_trans, le_succ => //.
          move: H8 => /[swap] -> /not_succ_le //.
  Qed.

  Theorem iterate_bijection_helper : ∀ (a c : N) (f g : N → X),
      (∀ j, a ≤ j ≤ a + c → exists ! i, a ≤ i ≤ a + c ∧ f i = g j) →
      (∀ i, a ≤ i ≤ a + c → exists ! j, a ≤ j ≤ a + c ∧ f i = g j) →
      ∀ j : N, 0 ≤ j ≤ c →
               ∃ y, unique (λ i : N, 0 ≤ i ≤ c ∧ f (i + a) = g (j + a)) y.
  Proof.
    move=> a c f g H H0 j [H1 H2].
    elim (H (j + a)%N) =>
    [y [[[[z <-] /[dup] H3 /(iff_sym (@O1_l_le_iff z c a)) H4]]] /[swap] H5 | ].
    - exists z.
      repeat split; rewrite -1?(add_comm a); auto using zero_le => x' [[H6 H7]].
      rewrite (add_comm x') -(add_comm j) => H8.
      apply /(naturals.cancellation_add a) /H5.
      repeat split; auto using O1_l_le, le_add.
    - rewrite -{1}(add_0_l a) ? (add_comm a).
      split; auto using O1_le.
  Qed.

  Theorem iterate_bijection : ∀ a b f g,
      (∀ j, a ≤ j ≤ b → exists ! i, a ≤ i ≤ b ∧ f i = g j) →
      (∀ i, a ≤ i ≤ b → exists ! j, a ≤ j ≤ b ∧ f i = g j) →
      iterate_with_bounds op f s a b = iterate_with_bounds op g s a b.
  Proof.
    move: classic => /[swap] a /[swap] b /(_ (a ≤ b)) =>
    [[[c <- f g H H0] | /lt_not_ge H *]]; last by rewrite ? iterate_neg //.
    rewrite ? iterate_shift.
    (apply iterate_bijection_0; eauto using iterate_bijection_helper) =>
    i /(iterate_bijection_helper a c g f) => H1.
    elim H1 => [y [H2 H3] | j /H0 [y [H2 H3]] | j /H [y [H2 H3]]];
                 exists y; split; intuition.
  Qed.

End Iterated_op_theorems.

Definition sum_N f a b := iterate_with_bounds add f 0 a b.
Definition prod_N f a b := iterate_with_bounds mul f 1 a b.

Theorem sum_N_0 : ∀ f a, sum_N f a a = f a.
Proof.
  move=> f a.
  rewrite /sum_N iterate_0 //.
Qed.

Theorem sum_N_neg : ∀ f a b, b < a → sum_N f a b = 0.
Proof.
  move=> f a b H.
  rewrite /sum_N iterate_neg //.
Qed.

Theorem sum_N_succ : ∀ f a b,
    a ≤ S b → (sum_N f a (S b)) = (sum_N f a b) + (f (S b)).
Proof.
  move=> f a b H.
  apply iterate_succ_lower_limit; auto.
  now ring_simplify.
Qed.

Theorem prod_N_0 : ∀ f a, prod_N f a a = f a.
Proof.
  move=> f a.
  rewrite /prod_N iterate_0 //.
Qed.

Theorem prod_N_neg : ∀ f a b, b < a → prod_N f a b = 1.
Proof.
  move=> f a b H.
  rewrite /prod_N iterate_neg //.
Qed.

Theorem prod_N_succ : ∀ f a b,
    a ≤ S b → (prod_N f a (S b)) = (prod_N f a b) * (f (S b)).
Proof.
  move=> f a b H.
  apply iterate_succ_lower_limit; auto.
  now ring_simplify.
Qed.

Theorem sum_N_dist :
  ∀ f g a b, sum_N (λ n, (f n) + (g n)) a b = sum_N f a b + sum_N g a b.
Proof.
  move=> f g a b.
  elim (classic (a ≤ b)) => [[c <-] | /lt_not_ge H].
  - induction c using Induction.
    + rewrite add_0_r ? sum_N_0 //.
    + rewrite add_succ_r ? sum_N_succ ? IHc; try (now ring_simplify);
        eauto using le_trans, le_add, le_succ.
  - rewrite ? sum_N_neg ? add_0_r //.
Qed.

Theorem sum_N_mul : ∀ f a b c, c * sum_N f a b = sum_N (λ n, c * (f n)) a b.
Proof.
  move=> f a b c.
  elim (classic (a ≤ b)) => [[d <-] | /lt_not_ge H].
  - induction d using Induction.
    + rewrite add_0_r ? sum_N_0 //.
    + rewrite add_succ_r ? sum_N_succ ? mul_distr_l ? IHd //;
              eauto using le_trans, le_add, le_succ.
  - rewrite ? sum_N_neg ? mul_0_r //.
Qed.

Theorem prod_dist :
  ∀ f g a b, prod_N (λ n, (f n) * (g n)) a b = prod_N f a b * prod_N g a b.
Proof.
  move=> f g a b.
  elim (classic (a ≤ b)) => [[c <-] | /lt_not_ge H].
  - induction c using Induction.
    + rewrite add_0_r ? prod_N_0 //.
    + rewrite add_succ_r ? prod_N_succ ? IHc; try (now ring_simplify);
        eauto using le_trans, le_add, le_succ.
  - rewrite ? prod_N_neg ? mul_1_r //.
Qed.

Theorem sum_of_0 : ∀ d, (sum_N (λ n, 0) 0 d) = 0.
Proof.
  induction d using Induction.
  - apply iterate_0.
  - rewrite sum_N_succ ? IHd ? add_0_r; auto using zero_le.
Qed.

Theorem sum_of_0_a_b : ∀ a b, (sum_N (λ n, 0) a b) = 0.
Proof.
  move=> a b.
  elim (classic (a ≤ b)) => [[c <-] | /lt_not_ge H].
  - rewrite /sum_N iterate_shift -{4} (sum_of_0 c) //.
  - rewrite sum_N_neg //.
Qed.

Theorem prod_of_1 : ∀ d, (prod_N (λ n, 1) 0 d) = 1.
Proof.
  induction d using Induction.
  - apply iterate_0.
  - rewrite prod_N_succ ? IHd ? mul_1_r; auto using zero_le.
Qed.

Theorem prod_of_1_a_b : ∀ a b, (prod_N (λ n, 1) a b) = 1.
Proof.
  move=> a b.
  elim (classic (a ≤ b)) => [[c <-] | /lt_not_ge H].
  - rewrite /prod_N iterate_shift -{3} (prod_of_1 c) //.
  - rewrite prod_N_neg //.
Qed.

Theorem prod_N_mul : ∀ f a b c,
    a ≤ b → c^(S (b-a)) * prod_N f a b = prod_N (λ n, c * (f n)) a b.
Proof.
  move=> f a b c [d <-].
  elim/Induction: d => [ | n].
  - rewrite add_0_r sub_diag pow_1_r ? prod_N_0 //.
  - rewrite ? (add_comm a) ? sub_abba ? pow_succ_r add_succ_l ? prod_N_succ
            // => [ | | <-]; eauto using le_trans, le_add_l, le_succ; ring.
Qed.
