Set Warnings "-ambiguous-paths,-typechecker".
Require Export integers combinatorics.

Open Scope Z_scope.

Definition Primes := {x of type ℤ | 0 < x ∧ prime x}.

Lemma Primes_classification : ∀ x : Z, x ∈ Primes ↔ 0 < x ∧ prime x.
Proof.
  move=> x.
  rewrite Specify_classification /specify_lift.
  case excluded_middle_informative => // [H | /(_ (elts_in_set x))] //.
  move: (reify H) => /set_proj_injective <-; tauto.
Qed.

Lemma fact_succ : (∀ n : N, (S n)! = n! * (S n))%N.
Proof.
  move=> n.
  rewrite {1}/factorial prod_N_succ; auto using one_le_succ.
Qed.

Lemma fact_div : ∀ x n : N, 0 < x → x < n → x｜n!.
Proof.
  induction n using Induction => [/INZ_lt /[swap] /INZ_lt /naturals.lt_antisym |
                                   /[dup] H /IHn {}IHn ] //.
  move: H => /INZ_lt /naturals.lt_def [c [/neq_sym /succ_0 [m H] H1]].
  (rewrite add_0_l in H1; subst => /INZ_lt /le_lt_succ /le_lt_or_eq)
  => [[/INZ_lt /IHn | ?]]; subst; rewrite ? fact_succ -INZ_mul.
  - by apply (div_mul_r ℤ).
  - exists (m! * (S (S m))) => /=.
    rewrite -? INZ_mul -integers.M2 (integers.M1 (S m)) integers.M2 //.
Qed.

Lemma finite_max : ∀ X, X ⊂ ℤ → finite X → ∃ m : Z, ∀ x : Z, x ∈ X → x < m.
Proof.
  move=> X H [n]; move: X H.
  (induction n using Induction => [? _ /empty_card ? | X H H0]; subst);
  first (exists 0 => s /Empty_set_classification //).
  (have: X ≠ ∅ => [H1 | /Nonempty_classification [k H1]]; subst);
  first move: H0 card_empty => /equivalence_to_card -> /(@eq_sym N) /PA4 //.
  have H2: k ∈ ℤ by auto.
  elim (IHn (X \ {k,k})) => [z H3 | x /complement_subset /H // | ].
  - (((case (le_sym ℤ_order (mkSet H2) z);
       rewrite -[ordered_rings.le ℤ_order]/(integers.le)) => [H4 | H4]);
     [ exists (z + 1) | exists ((mkSet H2 + 1)) ] => x H5);
    case (classic (x = (mkSet H2))) => H6; subst; (try by apply le_lt_1);
                                       (try by apply (lt_succ ℤ_order)).
    + apply (succ_lt ℤ_order), H3, Complement_classification, conj; auto =>
              /Singleton_classification H7; subst.
      by apply H6, set_proj_injective.
    + eapply le_lt_1, le_trans; eauto.
      apply or_introl, H3, Complement_classification, conj; auto =>
              /Singleton_classification H7; subst.
      by apply H6, set_proj_injective.
  - move: (complement_union X {k,k}) (H0) => {1}-> =>
          [z /Singleton_classification -> // | ].
    have H3: finite (X \ {k,k}).
    { eapply subsets_of_finites_are_finite;
        rewrite /finite; eauto using complement_subset. }
    rewrite {1}finite_union_equinumerosity;
      auto using singletons_are_finite, disjoint_intersection_complement =>
              /natural_cardinality_uniqueness.
    rewrite singleton_card add_comm add_1_r => /PA5 <-.
    auto using card_equiv.
Qed.

Theorem Euclid's_theorem : ¬ finite Primes.
Proof.
  move=> /finite_max [x /Specify_classification [H] | m H] //.
  have /le_def [c] : 0 ≤ m.
  { apply le_not_gt => /= H0.
    move: (ordered_rings.zero_lt_2 ℤ_order : 0 < 2) (two_is_prime) => H1 H2.
    move: Primes_classification (H 2) => -> /(_ (conj H1 H2)) H3.
    apply (lt_irrefl ℤ_order m) => /=; eauto using integers.lt_trans. }
  rewrite integers.A3 => H0; subst.
  elim (exists_prime_divisor (c! + 1)) =>
         [? [/lt_def [p [H0 H1]]] [/[dup] H2] [H3 H4] H5 | ].
  - rewrite integers.A3 in H1; subst.
    apply H3; rewrite /unit /rings.unit => /=.
    have -> : 1 = c! + 1 + (-c!) by ring.
    have H1: 0 < p by apply INZ_lt, nonzero_lt, neq_sym => /INZ_eq //.
    apply div_add, (div_sign_r ℤ _ (c! : Z)), fact_div, H,
      Primes_classification; auto.
  - eapply lt_def.
    exists (c!).
    by move: integers.A1 (factorial_ne_0 c) => -> /neq_sym /INZ_eq.
Qed.
