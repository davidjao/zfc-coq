Set Warnings "-ambiguous-paths".
Require Export sets polynomials.

Definition STR := (⋃ {({0%N,1%N}^n)%set | n in ω})%N.

Theorem STR_classification : ∀ f, f ∈ STR ↔ ∃ n : N, is_function f n {0,1}%N.
Proof.
  rewrite /STR => f.
  split => [/Union_classification
             [x [/replacement_classification [n ->] /Specify_classification []]]
           | [n /[dup] H [H0 H1]]]; eauto.
  rewrite Union_classification.
  exists ({0%N,1%N}^n).
  rewrite replacement_classification Specify_classification
          Powerset_classification; eauto.
Qed.

Theorem zero_string_construction : (is_function {(0,0),(0,0)} 1 {0,1})%N.
Proof.
  split => [z /Singleton_classification -> | a].
  - rewrite Product_classification.
    exists 0%N, 0%N.
    rewrite -lt_is_in Pairing_classification.
    auto using zero_le, (naturals.lt_succ 0).
  - rewrite /naturals.one => /Pairwise_union_classification =>
              [[/Empty_set_classification | /Singleton_classification ->]] //.
    exists 0%N.
    rewrite /unique Pairing_classification Singleton_classification.
    split; auto => x' [H /Singleton_classification /Ordered_pair_iff [] //].
Qed.

Theorem one_string_construction : (is_function {(0,1),(0,1)} 1 {0,1})%N.
Proof.
  split => [z /Singleton_classification -> | a].
  - rewrite Product_classification.
    exists 0%N, 1%N.
    rewrite -lt_is_in Pairing_classification.
    auto using zero_le, (naturals.lt_succ 0).
  - rewrite /naturals.one => /Pairwise_union_classification =>
              [[/Empty_set_classification | /Singleton_classification ->]] //.
    exists 1%N.
    rewrite /unique Pairing_classification Singleton_classification.
    split; auto => x' [H /Singleton_classification /Ordered_pair_iff [] //].
Qed.

Declare Scope String_scope.
Delimit Scope String_scope with str.
Open Scope String_scope.

Definition σ := elts STR.
Definition setify := elt_to_set : σ → set.
Coercion setify : σ >-> set.
Definition Σ := elts (P STR).
Definition subsetify := elt_to_set : Σ → set.
Coercion subsetify : Σ >-> set.

Bind Scope String_scope with STR.
Bind Scope String_scope with σ.

Definition functionify : σ → function.
Proof.
  move: (@elts_in_set) => /[swap] z /(_ _ z) /STR_classification =>
        /constructive_indefinite_description [n H].
  exact (mkFunc H).
Defined.

Coercion functionify : σ >-> function.

Theorem functionify_injective :
  ∀ s t : σ, (s : function) = (t : function) → s = t.
Proof.
  rewrite /functionify => s t.
  (repeat (elim: constructive_indefinite_description => ? ?)) =>
    [[]] _ /set_proj_injective //.
Qed.

Theorem string_range : ∀ x : σ, range x = {0,1}%N.
Proof.
  rewrite /functionify => x.
  elim: constructive_indefinite_description => //.
Qed.

Definition zero_string : σ.
Proof.
  have H: ({(0,0),(0,0)} ∈ STR)%N.
  { rewrite STR_classification.
    eauto using zero_string_construction. }
  exact (mkSet H).
Defined.
Notation "0" := zero_string : String_scope.

Definition one_string : σ.
Proof.
  have H: ({(0,1),(0,1)} ∈ STR)%N.
  { rewrite STR_classification.
    eauto using one_string_construction. }
  exact (mkSet H).
Defined.
Notation "1" := one_string : String_scope.

Definition length : σ → N.
Proof.
  move: (@elts_in_set) => /[swap] z /(_ _ z) /STR_classification =>
        /constructive_indefinite_description [n H].
  exact n.
Defined.

Theorem length_is_domain : ∀ x : σ, domain x = length x.
Proof.
  rewrite /length /functionify => x.
  elim: constructive_indefinite_description => //.
Qed.

Theorem string_domain : ∀ (x : σ) z, z ∈ domain x → z ∈ ω.
Proof.
  move=> x z.
  rewrite length_is_domain => /elements_of_naturals_are_naturals.
  eauto using elts_in_set.
Qed.

Theorem length_zero : length 0 = 1%N.
Proof.
  rewrite /length /zero_string.
  repeat elim: constructive_indefinite_description => /= *.
  eauto using set_proj_injective, domain_uniqueness, zero_string_construction.
Qed.

Theorem length_one : length 1 = 1%N.
Proof.
  rewrite /length /zero_string.
  repeat elim: constructive_indefinite_description => /= *.
  eauto using set_proj_injective, domain_uniqueness, one_string_construction.
Qed.

Definition cc_singleton : σ → Σ.
Proof.
  move=> [x H].
  have H0: ({x,x} ∈ P STR) by
    apply Powerset_classification => z /Singleton_classification -> //.
  exact (mkSet H0).
Defined.

Section concat_elements_construction.

  Context {n m : N} {f g : set}.
  Hypothesis F : is_function f n {0,1}%N.
  Hypothesis G : is_function g m {0,1}%N.

  Definition concat_elements : elts (n+m)%N → elts {0,1}%N.
  Proof.
    move=> x.
    have H: (x ∈ ω) by
      eauto using elements_of_naturals_are_naturals, elts_in_set.
    case (excluded_middle_informative (mkSet H < n)%N) =>
           [/lt_is_in H0 | /naturals.le_not_gt /sub_abab H0].
    - have H1: (mkFunc F) x ∈ {0%N,1%N}.
      { rewrite -[{0%N,1%N}]/(range (mkFunc F)).
        auto using function_maps_domain_to_range. }
      exact (mkSet H1).
    - have H1: (mkFunc G) (mkSet H - n)%N ∈ {0%N,1%N}.
      { rewrite -[{0%N,1%N}]/(range (mkFunc G)).
        apply function_maps_domain_to_range => /=.
        move: (elts_in_set x).
        rewrite -{1}[elt_to_set x]/(INS (mkSet H)) -? lt_is_in
                    ? naturals.lt_not_ge => /[swap] =>
                  /constructive_indefinite_description [c H1] [].
        rewrite -H0 -H1 naturals.add_assoc /naturals.le; eauto. }
      exact (mkSet H1).
  Defined.

End concat_elements_construction.

Definition concat : σ → σ → σ.
Proof.
  move=> [a /STR_classification /constructive_indefinite_description [n H]]
           [b /STR_classification /constructive_indefinite_description [m H0]].
  have H1: (graph (sets.functionify (concat_elements H H0)) ∈ STR).
  { rewrite STR_classification.
    exists (n+m)%N.
    move: (func_hyp (sets.functionify (concat_elements H H0))).
    rewrite sets.functionify_domain sets.functionify_range //. }
  exact (mkSet H1).
Defined.

Infix "++" := concat : set_scope.

Theorem concat_length : ∀ a b, length (a ++ b) = (length a + length b)%N.
Proof.
  rewrite /concat /length /ssr_have => [[a A]] [b B].
  (repeat elim constructive_indefinite_description => /=) => x H x0 H0 x1 H1.
  move: (func_hyp (sets.functionify (concat_elements H0 H))).
  rewrite sets.functionify_domain sets.functionify_range // => /= H2.
  eapply set_proj_injective, domain_uniqueness; eauto.
Qed.

Definition empty_string : σ.
Proof.
  have H: (∅ ∈ STR).
  { rewrite STR_classification.
    exists 0%N.
    split; auto using Empty_set_is_subset => a /Empty_set_classification //. }
  exact (mkSet H).
Defined.

Notation "'ε'" := empty_string (at level 0) : String_scope.

Reserved Notation "s =~ re" (at level 80).

Theorem length_empty : length ε = 0%N.
Proof.
  rewrite /empty_string /length /ssr_have.
  elim constructive_indefinite_description => /= x H.
  eapply set_proj_injective, domain_uniqueness; eauto.
  split; auto using Empty_set_is_subset => a /Empty_set_classification //.
Qed.

(* Lightly adapted from
   https://www.seas.upenn.edu/~cis500/current/sf/lf-current/IndProp.html *)

Inductive reg_exp : Type :=
| EmptySet
| Char (t : σ)
| Concat (r1 r2 : reg_exp)
| Or (r1 r2 : reg_exp)
| Star (r : reg_exp).

Notation "[]" := EmptySet : String_scope.
Notation "[ x ]" := (Char x) : String_scope.
Infix "⌣" := Or (at level 60) : String_scope.
Infix "||" := Concat : String_scope.
Notation "A '⃰' " := (Star A) (at level 30) : String_scope.

(* Note bug in upstream definition: MStarApp needs the additional condition
   (u ≠ ε) in order for induction on Star to terminate. The original statement
   of MStarApp still holds, as a theorem (which we prove in MStarApp_full). *)
Inductive exp_match : σ → reg_exp → Prop :=
| MChar x : x =~ [x]
| MUnionL a A B (H1 : a =~ A) : a =~ A ⌣ B
| MUnionR b A B (H2 : b =~ B) : b =~ A ⌣ B
| MApp a b A B (H1 : a =~ A) (H2 : b =~ B) : a ++ b =~ A || B
| MStar0 A : ε =~ A ⃰
| MStarApp u v A (H1 : u =~ A) (H2 : u ≠ ε) (H3 : v =~ A ⃰) : u ++ v =~ A ⃰
where "s =~ re" := (exp_match s re).

Definition realization A := {x in STR | ∃ y : σ, x = y ∧ exp_match y A}.
Coercion realization : reg_exp >-> set.

Theorem realization_in_powerset : ∀ A, realization A ∈ P STR.
Proof.
  move=> A.
  rewrite Powerset_classification => z /Specify_classification [?] //.
Qed.

Theorem realization_is_subset : ∀ A, realization A ⊂ STR.
Proof.
  move=> A.
  apply Powerset_classification, realization_in_powerset.
Qed.

Definition subset_of (A : reg_exp) := mkSet (realization_in_powerset A) : Σ.

Coercion subset_of : reg_exp >-> Σ.

Definition concat_set (A : Σ) (B : Σ) : Σ.
Proof.
  have H: ({z in STR | ∃ a b : σ, a ∈ A ∧ b ∈ B ∧ z = a ++ b} ∈ P STR) by
    rewrite Powerset_classification => x /Specify_classification [?] //.
  exact (mkSet H).
Defined.

Infix "++" := concat_set : String_scope.

Theorem concat_set_classification : ∀ (x : set) (A B : Σ),
    x ∈ (A ++ B)%str ↔ ∃ a b : σ, a ∈ A ∧ b ∈ B ∧ x = (a ++ b)%set.
Proof.
  rewrite /concat_set => /= x A B.
  rewrite Specify_classification.
  split => [[?] | [a [b [H [H0 ->]]]]] //.
  eauto 6 using elts_in_set.
Qed.

Theorem concat_reg_exp : ∀ A B : reg_exp, A ++ B = A || B.
Proof.
  move=> A B.
  apply set_proj_injective, Extensionality => z.
  split => [/Specify_classification
             [H [a [b [/Specify_classification
                        [? [y [/set_proj_injective -> ?]]]
                        [/Specify_classification
                          [? [y' [/set_proj_injective -> ?]]] ->]]]]] |
             /Specify_classification [? [y [-> H]]]].
  - rewrite Specify_classification.
    eauto using elts_in_set, MApp.
  - rewrite Specify_classification.
    inversion H as [ | | | a b | | ].
    split; eauto using elts_in_set.
    exists a, b.
    rewrite ? Specify_classification.
    eauto 9 using elts_in_set.
Qed.

Theorem empty_set_realization : realization EmptySet = ∅.
Proof.
  apply Extensionality => z.
  split => [/Specify_classification [H [h [H0 H1]]] |
             /Empty_set_classification] //.
  inversion H1.
Qed.

Theorem singleton_realization : ∀ a, realization [a] = {a,a}.
Proof.
  move=> a.
  (apply Extensionality => z; split) =>
    [/Specify_classification [? [y [-> H1]]] | /Singleton_classification ->];
    rewrite ? Singleton_classification ? Specify_classification;
    eauto using elts_in_set, MChar; by inversion H1.
Qed.

Theorem reg_exps_are_strings : ∀ A : reg_exp, A ⊂ STR.
Proof.
  move=> A z /Specify_classification [?] //.
Qed.

Theorem empty_subset_construction : [ε] ∈ P STR.
Proof.
  rewrite Powerset_classification => z.
  rewrite singleton_realization Singleton_classification => ->.
  eauto using elts_in_set.
Qed.

Theorem elts_of_reg_exps : ∀ z (A : reg_exp), z ∈ A → z ∈ STR.
Proof.
  move=> z A /reg_exps_are_strings //.
Qed.

Definition empty_subset := [ε] : Σ.

Definition concat_pow A n := iterate_with_bounds concat_set (λ x, A) [ε] 1 n.
Infix "**" := concat_pow (at level 35) : String_scope.

Definition pow A n := iterate_with_bounds Concat (λ x, A) [ε] 1 n.
Infix "^" := pow : String_scope.

Theorem concat_pow_0_r : ∀ A, A ** 0 = [ε].
Proof.
  rewrite /concat_pow /iterate_with_bounds => A.
  elim excluded_middle_informative => // /[dup] /naturals.le_not_gt.
  move: (naturals.succ_lt 0) => //.
Qed.

Theorem concat_pow_1_r : ∀ A, A ** 1 = A.
Proof.
  rewrite /concat_pow => A.
  by rewrite iterate_0.
Qed.

Theorem pow_0_r : ∀ A, A^0 = [ε].
Proof.
  rewrite /pow /iterate_with_bounds => A.
  elim excluded_middle_informative => // /[dup] /naturals.le_not_gt.
  move: (naturals.succ_lt 0) => //.
Qed.

Theorem pow_1_r : ∀ A, A^1 = A.
Proof.
  rewrite /pow => A.
  by rewrite iterate_0.
Qed.

Theorem append_ε_l : ∀ b, (ε ++ b)%set = b.
Proof.
  rewrite /concat /empty_string => [[b B]] /=.
  apply set_proj_injective => /=.
  (repeat elim constructive_indefinite_description => /=) => x H x0 /[dup] H0.
  rewrite -[b]/(graph (mkFunc H)).
  (have ->: x0 = 0%N => [ | {}H0]).
  { eapply set_proj_injective, domain_uniqueness; eauto.
    split; auto using Empty_set_is_subset => ? /Empty_set_classification //. }
  apply f_equal, func_ext;
    rewrite ? sets.functionify_domain ? sets.functionify_range /=
            ? add_0_l // => y H1.
  rewrite -[y]/((mkSet H1 : elts (0 + x)%N) : set) /sets.functionify
              /concat_elements /ssr_have.
  elim constructive_indefinite_description => f [H2 [H3 ->]] /=.
  case excluded_middle_informative => /= [/naturals.lt_not_ge | ].
  - move: zero_le => //.
  - by rewrite sub_0_r.
Qed.

Theorem MStarApp_full : ∀ u v A, u =~ A → v =~ A ⃰ → (u ++ v)%set =~ A ⃰.
Proof.
  move=> u v A H H0.
  case (classic (u = ε)); auto using MStarApp => ->.
  by rewrite append_ε_l.
Qed.

Theorem concat_ε_l : ∀ A, [ε] ++ A = A.
Proof.
  move=> [A /[dup] /Powerset_classification H HA].
  apply set_proj_injective, Extensionality => z /=.
  split => [/Specify_classification [H0 [a [b]]] | /[dup] H0 /H H1].
  - rewrite singleton_realization Singleton_classification =>
              [[/set_proj_injective ->]].
    rewrite append_ε_l => /and_comm [->] //.
  - rewrite Specify_classification.
    split; auto.
    rewrite (reify H1).
    exists ε, (mkSet H1 : σ).
    by rewrite append_ε_l singleton_realization Singleton_classification.
Qed.

Theorem concat_pow_succ_r : (∀ n A, A ** (S n) = concat_set (A ** n) A)%set.
Proof.
  (elim/Induction => [A | n H A]);
  rewrite ? concat_pow_0_r ? concat_pow_1_r ? concat_ε_l // /concat_pow
          iterate_succ //; auto using one_le_succ.
Qed.

Theorem pow_succ_r : ∀ n A, (A^(S n) : Σ) = (A^n || A).
Proof.
  (elim/Induction => [A | n H A]);
  rewrite ? pow_0_r ? pow_1_r -? concat_reg_exp ? concat_ε_l //
          /pow iterate_succ ? concat_reg_exp; auto using one_le_succ.
Qed.

Theorem pow_concat_pow : ∀ n A, (A^n : Σ) = A ** n.
Proof.
  (elim/Induction => [A | n H A]);
  rewrite ? pow_0_r ? concat_pow_0_r // ? pow_succ_r ? concat_pow_succ_r
          -? concat_reg_exp ? H //.
Qed.

Theorem subsetifying_subset : ∀ A, subsetify (subset_of A) = A.
Proof.
  reflexivity.
Qed.

Section concat_function_construction.

  Variable A B : reg_exp.

  Definition concat_function : elts (A × B) → elts (A || B).
  Proof.
    move=> [z /Product_classification /constructive_indefinite_description
              [a /constructive_indefinite_description
                 [b [/[dup] ? /reg_exps_are_strings H
                      [/[dup] ? /reg_exps_are_strings H0 ?]]]]].
    have H1: ((mkSet H) ++ (mkSet H0) ∈ A || B).
    { rewrite -subsetifying_subset -concat_reg_exp Specify_classification.
      split; eauto using elts_in_set.
      by exists (mkSet H), (mkSet H0). }
    exact (mkSet H1).
  Defined.

  Definition concat_product := sets.functionify concat_function.

End concat_function_construction.

Theorem concat_product_action :
  ∀ (A B : reg_exp) (x : elts (A × B)) (a b : σ),
    a ∈ A → b ∈ B → (a,b) = x → concat_product A B x = (a ++ b)%set.
Proof.
  rewrite /concat_product /concat_function /sets.functionify /ssr_have =>
            A B [x X] [a ?] [b ?] ? ? H.
  elim constructive_indefinite_description => f [? [? ->]].
  elim constructive_indefinite_description => [a' [b' [? [? ?]]]].
  elim constructive_indefinite_description => [b'' [? [? H0]]] /=.
  (repeat elim constructive_indefinite_description) => [c H1] d H2 m H3 n H4.
  rewrite /ssr_have /=; subst.
  move: H H0 => /Ordered_pair_iff [? ?] /Ordered_pair_iff [? ?]; subst.
  have ?: c = m; have ?: d = n;
    eauto using set_proj_injective, domain_uniqueness; subst.
  by rewrite (proof_irrelevance _ H1 H3) (proof_irrelevance _ H2 H4).
Qed.

Inductive unambiguous : reg_exp → Prop :=
| unambiguous_empty : unambiguous []
| unambiguous_char x : unambiguous [x]
| unambiguous_union A B :
    unambiguous A → unambiguous B → A ∩ B = ∅ → unambiguous (A ⌣ B)
| unambiguous_prod A B :
    unambiguous A → unambiguous B → injective (concat_product A B) →
    unambiguous (A || B)
| unambiguous_star A :
    unambiguous A →
    (∀ n m : N, n ≠ m → (A^n)%str ∩ (A^m)%str = ∅) →
    injective (concat_product A (A ⃰)) →
    unambiguous (A ⃰).

Theorem concat_surjective : ∀ A B, surjective (concat_product A B).
Proof.
  move=> A B.
  rewrite Surjective_classification {1 2}/concat_product sets.functionify_range
          sets.functionify_domain => y /Specify_classification [? [y' [? H]]].
  inversion H as [ | | | a b | | ]; subst.
  (have: a ∈ A; have: b ∈ B; try by rewrite ? Specify_classification;
   eauto using elts_in_set) => ? ?.
  have H0: (a, b) ∈ A × B by rewrite Product_classification; eauto.
  exists (mkSet H0).
  eauto using concat_product_action.
Qed.

Section test_generating_series.
  (* TODO: replace this with the function mapping f to 1/(1-f) *)
  Variable star_func : (power_series ℤ) → (power_series ℤ).

  Fixpoint gen_func (f : reg_exp) :=
    match f with
    | [] => IRS ℤ 1%Z
    | [a] => power_series.x ℤ
    | A || B => power_series.mul ℤ (gen_func A) (gen_func B)
    | A ⌣ B => power_series.add ℤ (gen_func A) (gen_func B)
    | A ⃰ => star_func (gen_func A)
    end.

  Goal (gen_func [0]) = power_series.x ℤ.
  Proof.
    reflexivity.
  Qed.

  Goal gen_func ([0] ⌣ [1]) =
  power_series.add _ (power_series.x ℤ) (power_series.x ℤ).
  Proof.
    reflexivity.
  Qed.
End test_generating_series.

Theorem singleton_unambiguous : ∀ x, unambiguous [x].
Proof.
  apply unambiguous_char.
Qed.

Theorem ambiguous_singletons : ∀ x, ¬ unambiguous ([x] ⌣ [x]).
Proof.
  move=> x H.
  inversion H as [ | | A B H0 H1 H2 | | ].
  contradiction (Empty_set_classification x).
  rewrite -H2 Intersection_idempotent Specify_classification.
  eauto using elts_in_set, MChar.
Qed.

Theorem ambiguous_empty_star : ¬ unambiguous ([ε] ⃰).
Proof.
  move=> H.
  inversion H as [ | | | | C H0 H1 H2 H3].
  move: (PA4 0) => /H1.
  apply Nonempty_classification.
  exists ε.
  rewrite Pairwise_intersection_classification pow_0_r pow_1_r
          singleton_realization Singleton_classification //.
Qed.

Theorem zero_ne_1 : 0 ≠ 1.
Proof.
  move: (eq_refl (∅, ∅)) => /Singleton_classification /[swap] =>
        /(f_equal elt_to_set) /= ->
        /Singleton_classification /Ordered_pair_iff [_].
  move: (Empty_set_classification ∅) => /[swap] {2}->.
  auto using in_succ.
Qed.

Theorem functionify_concat_l : ∀ a b x, (x < length a)%N → (a ++ b)%set x = a x.
Proof.
  intros a b x H.
  pose proof length_is_domain a as A0.
  destruct a as [a A], b as [b B].
  unfold functionify, concat, ssr_have in A0 |-*.
  destruct constructive_indefinite_description as [m].
  destruct constructive_indefinite_description as [a'].
  destruct constructive_indefinite_description as [n].
  simpl in *.
  assert (a' = m+n)%N as H0.
  { eapply set_proj_injective, domain_uniqueness; eauto.
    split; intros z H0.
    - apply graph_elements_are_pairs in H0.
      now rewrite -> sets.functionify_domain, sets.functionify_range in H0.
    - destruct (func_hyp (sets.functionify (concat_elements i i1))) as [H1 H2].
      rewrite -> sets.functionify_domain, sets.functionify_range in H2.
      now apply H2 in H0. }
  subst.
  set (f := mkFunc i0).
  assert (f = (sets.functionify (concat_elements i i1))) as H0.
  { apply function_record_injective; auto.
    now rewrite -> sets.functionify_range. }
  rewrite -> H0.
  unfold sets.functionify.
  destruct constructive_indefinite_description as [f'], a0 as [H1 [H2 H3]].
  apply set_proj_injective in A0.
  rewrite <-A0 in H.
  assert (x ∈ m+n)%N as H4.
  { assert (m ≤ m+n)%N as H4 by now (exists n).
    rewrite -> le_is_subset in H4.
    now apply H4, lt_is_in. }
  set (ξ := mkSet H4 : elts (m+n)%N).
  replace (f' x) with (f' ξ) by auto.
  rewrite -> H3.
  unfold concat_elements, ssr_have.
  repeat destruct excluded_middle_informative; auto; simpl.
  contradict n0.
  unfold ξ.
  simpl.
  destruct x.
  simpl.
  eapply naturals.le_lt_trans; eauto.
  exists 0%N.
  rewrite -> add_0_r.
  now apply set_proj_injective.
Qed.

Theorem functionify_concat_r : ∀ a b x,
    (length a ≤ x < length a + length b → (a ++ b)%set x = b (x - length a))%N.
Proof.
  intros a b x [H H0].
  pose proof length_is_domain a as A0.
  pose proof length_is_domain b as B0.
  destruct a as [a A], b as [b B].
  unfold functionify, concat in A0, B0 |-*.
  destruct constructive_indefinite_description as [m].
  destruct constructive_indefinite_description as [n].
  destruct constructive_indefinite_description as [a'].
  simpl in *.
  apply set_proj_injective in A0.
  apply set_proj_injective in B0.
  rewrite <-? A0 in H0, H.
  rewrite <-B0 in H0.
  assert (a' = m+n)%N.
  { eapply set_proj_injective, domain_uniqueness; eauto.
    split; intros z H1.
    - apply graph_elements_are_pairs in H1.
      now rewrite -> sets.functionify_domain, sets.functionify_range in H1.
    - pose proof func_hyp (sets.functionify (concat_elements i i0)) as [H2 H3].
      rewrite -> sets.functionify_domain, sets.functionify_range in H3.
      by apply H3 in H1. }
  subst a'.
  set (f := mkFunc i1).
  assert (f = (sets.functionify (concat_elements i i0))) as H1.
  { apply function_record_injective; auto.
    now rewrite -> sets.functionify_range. }
  rewrite -> H1.
  unfold sets.functionify.
  destruct constructive_indefinite_description as [f'], a0 as [H2 [H3 H4]].
  assert (x ∈ m+n)%N as H5 by now apply lt_is_in.
  set (ξ := mkSet H5 : elts (m+n)%N).
  replace (f' x) with (f' ξ) by auto.
  rewrite -> H4.
  unfold concat_elements, ssr_have.
  destruct excluded_middle_informative; simpl.
  - apply naturals.le_not_gt in H.
    contradict H.
    destruct x.
    simpl in l.
    eapply naturals.le_lt_trans; eauto.
    exists 0%N.
    rewrite -> add_0_r.
    now apply set_proj_injective.
  - f_equal.
    rewrite <-A0.
    unfold INS.
    do 2 f_equal.
    destruct x.
    now apply set_proj_injective.
Qed.

Theorem app_assoc : ∀ a b c : σ, (a ++ (b ++ c)%set = (a ++ b)%set ++ c)%set.
Proof.
  intros a b c.
  apply functionify_injective, func_ext; try now rewrite -> ? string_range.
  - rewrite -> ? length_is_domain, ? concat_length.
    f_equal.
    ring.
  - intros x H.
    rewrite -> ? length_is_domain, ? concat_length in *.
    assert (x ∈ ω) as H0 by
          eauto using elements_of_naturals_are_naturals, elts_in_set.
    set (ξ := mkSet H0 : N).
    replace x with (ξ : set) in * by auto.
    rewrite <-lt_is_in in H.
    destruct (classic (ξ < length a)%N) as [H1 | H1].
    { rewrite -> ? functionify_concat_l; auto.
      rewrite -> concat_length.
      eapply naturals.lt_le_trans; eauto.
      now exists (length b). }
    apply naturals.le_not_gt in H1.
    destruct (classic (ξ < (length a + length b)))%N as [H2 | H2].
    { rewrite -> functionify_concat_r, functionify_concat_l,
      functionify_concat_l, functionify_concat_r; auto.
      - now rewrite -> concat_length.
      - apply sub_abab in H1.
        now rewrite <-H1, ? (naturals.add_comm (length a)),
        <-naturals.O1_iff in H2.
      - split; auto.
        rewrite -> concat_length, naturals.add_assoc.
        eapply naturals.lt_le_trans; eauto.
        now exists (length c). }
    apply naturals.le_not_gt in H2.
    rewrite -> ? functionify_concat_r, ? concat_length; auto.
    + do 2 f_equal.
      symmetry.
      repeat apply sub_spec.
      now rewrite -> naturals.add_assoc, sub_abab.
    + now rewrite -> ? concat_length, <-naturals.add_assoc.
    + split; apply sub_abab in H1.
      * now rewrite <-H1, ? (naturals.add_comm (length a)),
        <-naturals.O1_le_iff in H2.
      * now rewrite <-H1, ? (naturals.add_comm (length a)),
        <-naturals.O1_iff in H.
    + now rewrite -> concat_length.
Qed.

Theorem concat_assoc :
  ∀ A B C, A ++ (B ++ C) = (A ++ B) ++ C.
Proof.
  intros A B C.
  apply set_proj_injective, Extensionality.
  split; intros H; rewrite -> concat_set_classification in *;
    destruct H as [x [y [H [H0 H1]]]]; subst;
      rewrite -> concat_set_classification in *.
  - destruct H0 as [z [w [H0 [H1 H2]]]].
    apply set_proj_injective in H2.
    subst.
    exists (x ++ z)%set, w.
    repeat split; auto.
    + rewrite -> concat_set_classification; eauto.
    + now rewrite -> app_assoc.
  - destruct H as [z [w [H [H1 H2]]]].
    apply set_proj_injective in H2.
    subst.
    exists z, (w ++ y)%set.
    repeat split; auto.
    + rewrite -> concat_set_classification; eauto.
    + now rewrite -> app_assoc.
Qed.

Theorem append_ε_r : ∀ b, (b ++ ε)%set = b.
Proof.
  intros b.
  apply eq_sym, functionify_injective, func_ext.
  - rewrite -> ? length_is_domain, concat_length, length_empty.
    f_equal.
    ring.
  - now rewrite -> ? string_range.
  - intros x H.
    assert (x ∈ ω) as H0.
    { rewrite -> length_is_domain in H.
      eauto using elements_of_naturals_are_naturals, elts_in_set. }
    set (ξ := mkSet H0 : N).
    replace x with (ξ : set) in * by auto.
    rewrite -> functionify_concat_l; auto.
    now rewrite -> lt_is_in, <-length_is_domain.
Qed.

Theorem concat_ε_r : ∀ A, A ++ [ε] = A.
Proof.
  intros A.
  apply set_proj_injective, Extensionality.
  split; intros H; rewrite -> concat_set_classification in *.
  - destruct H as [a [b [H [H0 H1]]]].
    rewrite -> subsetifying_subset, singleton_realization,
    Singleton_classification in *.
    apply set_proj_injective in H0.
    subst.
    now rewrite -> append_ε_r.
  - assert (z ∈ STR) as H0.
    { pose proof (elts_in_set A) as H0.
      apply Powerset_classification in H0.
      auto. }
    set (ζ := mkSet H0 : σ).
    replace z with (ζ : set) by auto.
    exists ζ, ε.
    rewrite -> append_ε_r.
    repeat split; auto.
    now rewrite -> subsetifying_subset, singleton_realization,
    Singleton_classification in *.
Qed.

Lemma concat_sym : ∀ A n, A^n ++ A = A ++ A^n.
Proof.
  intros A n.
  induction n using Induction.
  - now rewrite -> pow_0_r, concat_ε_l, concat_ε_r.
  - now rewrite -> ? pow_succ_r, <-? concat_reg_exp, IHn, <-concat_assoc, IHn.
Qed.

Theorem pow_add_r : ∀ n m A, (A^(m+n)%N : Σ) = A^m || A^n.
Proof.
  intros n m A.
  induction m using Induction.
  - now rewrite -> pow_0_r, add_0_l, <-concat_reg_exp, concat_ε_l.
  - now rewrite -> naturals.add_comm, add_succ_r, naturals.add_comm,
    <-concat_reg_exp, ? pow_succ_r, <-? concat_reg_exp, IHm,
    <-concat_reg_exp, <-? concat_assoc, concat_sym.
Qed.

Theorem length_of_n_string :
  ∀ (n : N) (x : σ), x ∈ (([0] ⌣ [1])^n)%str ↔ length x = n.
Proof.
  induction n using Induction; split; intros H.
  - rewrite -> pow_0_r, singleton_realization, Singleton_classification in *.
    apply set_proj_injective in H.
    subst.
    apply length_empty.
  - pose proof length_is_domain x.
    rewrite -> pow_0_r, singleton_realization, Singleton_classification in *.
    rewrite -> H in H0.
    f_equal.
    apply functionify_injective, func_ext; try now rewrite -> ? string_range.
    + now rewrite -> ? length_is_domain, length_empty, H.
    + intros z H1.
      rewrite -> H0 in H1.
      contradiction (Empty_set_classification z).
  - rewrite <-subsetifying_subset, pow_succ_r, <-concat_reg_exp in H.
    apply Specify_classification in H as [H [a [b [H0 [H1 H2]]]]].
    apply set_proj_injective in H2.
    subst.
    replace n with (length a) by now apply IHn.
    rewrite -> concat_length, <-add_1_r; auto.
    f_equal.
    apply Specify_classification in H1 as [H1 [y [H2 H3]]].
    apply set_proj_injective in H2.
    inversion H3; inversion H6; subst; auto using length_zero, length_one.
  - rewrite <-subsetifying_subset, pow_succ_r, <-concat_reg_exp,
    concat_set_classification.
    assert (x n ∈ {0,1}%N) as X.
    { erewrite <-string_range.
      apply function_maps_domain_to_range.
      rewrite -> length_is_domain, H, <-S_is_succ.
      apply Pairwise_union_classification.
      rewrite -> Singleton_classification; auto. }
    destruct (function_construction n {0,1}%N (λ i, x i)) as [a' [H0 [H1 H2]]].
    { intros a H0.
      erewrite <-string_range.
      apply function_maps_domain_to_range.
      rewrite -> length_is_domain, H, <-S_is_succ.
      apply Pairwise_union_classification; tauto. }
    assert (is_function {(0,x n),(0,x n)} 1 {0,1})%N as H3.
    { split.
      - intros z H3.
        apply Singleton_classification in H3.
        subst.
        apply Product_classification.
        exists 0%N, (x n).
        repeat split; auto.
        apply lt_is_in, naturals.succ_lt.
      - intros a H3.
        unfold naturals.one in H3.
        rewrite <-S_is_succ in H3.
        unfold succ in H3.
        rewrite -> Union_comm, Union_empty, Singleton_classification in H3.
        subst.
        exists (x n).
        repeat split; auto.
        + now rewrite -> Singleton_classification.
        + intros x' [H3 H4].
          apply Singleton_classification, Ordered_pair_iff in H4.
          intuition. }
    assert (graph a' ∈ STR) as H4.
    { rewrite -> STR_classification.
      exists n.
      rewrite <-H0, <-H1.
      apply func_hyp. }
    assert ({(0, x n), (0, x n)}%N ∈ STR).
    { rewrite -> STR_classification.
      now exists 1%N. }
    exists (mkSet H4 : σ), (mkSet H5 : σ).
    assert (length (mkSet H4) = n) as L1.
    { apply set_proj_injective.
      unfold INS in *.
      rewrite <-length_is_domain, <-H0.
      f_equal.
      unfold functionify.
      destruct constructive_indefinite_description.
      simpl in *.
      apply function_record_injective; simpl; congruence. }
    assert (length (mkSet H5) = 1%N) as L2.
    { apply set_proj_injective.
      rewrite <-length_is_domain.
      unfold functionify.
      repeat destruct constructive_indefinite_description.
      simpl in *.
      destruct constructive_indefinite_description.
      replace ({| graph := x |}) with (functionify x) in i;
        eauto using domain_uniqueness.
      unfold functionify.
      destruct constructive_indefinite_description.
      apply function_record_injective; simpl; auto; congruence. }
    repeat split; try now rewrite -> IHn, L1.
    + apply Pairing_classification in X as [X | X]; simpl; rewrite -> X;
        apply Specify_classification.
      * replace ({(∅, 0%N),(∅, 0%N)}) with (0 : set);
          eauto using elts_in_set, MUnionL, MUnionR, MChar.
      * replace ({(∅, 1%N),(∅, 1%N)}) with (1 : set);
          eauto using elts_in_set, MUnionL, MUnionR, MChar.
    + f_equal.
      apply functionify_injective, func_ext; try now rewrite -> ? string_range.
      { rewrite -> ? length_is_domain, concat_length, H, <-add_1_r.
        do 2 f_equal; congruence. }
      intros z H6.
      rewrite -> length_is_domain, H, <-S_is_succ in H6.
      apply Pairwise_union_classification in H6 as [H6 | H6].
      * assert (z ∈ ω) as H8
            by eauto using elements_of_naturals_are_naturals, elts_in_set.
        replace z with ((mkSet H8 : N) : set) by auto.
        rewrite -> functionify_concat_l; try now rewrite -> L1, lt_is_in.
        rewrite <-H2; auto; simpl.
        f_equal.
        unfold functionify.
        destruct constructive_indefinite_description.
        simpl.
        apply function_record_injective; simpl; auto; congruence.
      * rewrite -> Singleton_classification in H6.
        rewrite -> H6, functionify_concat_r, L1, sub_diag.
        2: { rewrite -> L1, L2, add_1_r.
             auto using naturals.succ_lt, naturals.le_refl. }
        symmetry.
        rewrite <-function_maps_domain_to_graph.
        -- unfold functionify at 2.
           destruct constructive_indefinite_description.
           simpl.
           now apply Singleton_classification.
        -- rewrite -> length_is_domain, L2, <-lt_is_in.
           apply naturals.succ_lt.
        -- now rewrite -> string_range.
Qed.

Theorem unambiguous_all_strings : unambiguous (([0] ⌣ [1]) ⃰).
Proof.
  apply unambiguous_star.
  - apply unambiguous_union; auto using singleton_unambiguous.
    apply Extensionality.
    split; intros H.
    + apply Pairwise_intersection_classification in H as [H H0].
      rewrite -> singleton_realization, Singleton_classification in *.
      contradiction zero_ne_1.
      apply set_proj_injective.
      unfold setify in *.
      congruence.
    + contradiction (Empty_set_classification z).
  - intros n m H.
    apply NNPP.
    contradict H.
    apply Nonempty_classification in H as [x H].
    apply Pairwise_intersection_classification in H as [H H0].
    assert (x ∈ STR).
    { pose proof (elts_in_set (([0] ⌣ [1]) ** n)%set) as H1; simpl in H1.
      rewrite <-subsetifying_subset, pow_concat_pow in H.
      apply Powerset_classification in H1; auto. }
    set (ξ := (mkSet H1 : σ)).
    replace x with (ξ : set) in * by auto.
    rewrite -> length_of_n_string in *; congruence.
  - apply Injective_classification.
    intros x y H H0 H1.
    unfold concat_product in H, H0.
    rewrite -> @sets.functionify_domain in *.
    set (ξ := mkSet H : elts (([0] ⌣ [1]) × ([0] ⌣ [1]) ⃰)).
    set (γ := mkSet H0 : elts (([0] ⌣ [1]) × ([0] ⌣ [1]) ⃰)).
    pose proof H as H2.
    pose proof H0 as H3.
    replace x with (ξ : set) in * by auto.
    replace y with (γ : set) in * by auto.
    apply Product_classification in H2 as [x1 [x2 [H4 [H5 H6]]]].
    apply Product_classification in H3 as [y1 [y2 [H7 [H8 H9]]]].
    assert (x1 ∈ STR) as H10 by now apply realization_is_subset in H4.
    assert (x2 ∈ STR) as H11 by now apply realization_is_subset in H5.
    assert (y1 ∈ STR) as H12 by now apply realization_is_subset in H7.
    assert (y2 ∈ STR) as H13 by now apply realization_is_subset in H8.
    set (ζ1 := (mkSet H10 : σ)).
    set (ζ2 := (mkSet H11 : σ)).
    set (γ1 := (mkSet H12 : σ)).
    set (γ2 := (mkSet H13 : σ)).
    replace x1 with (ζ1 : set) in * by auto.
    replace x2 with (ζ2 : set) in * by auto.
    replace y1 with (γ1 : set) in * by auto.
    replace y2 with (γ2 : set) in * by auto.
    erewrite -> (concat_product_action _ _ ξ ζ1 ζ2),
    (concat_product_action _ _ γ γ1 γ2) in H1; eauto.
    apply set_proj_injective in H1.
    rewrite -> H6, H9.
    assert (length ζ1 = length γ1) as H2.
    { pose proof (length_of_n_string 1 ζ1) as [L1 L2].
      pose proof (length_of_n_string 1 γ1) as [L3 L4].
      rewrite -> L1, L3; auto; now rewrite -> pow_1_r. }
    do 2 f_equal.
    + apply functionify_injective, func_ext;
      rewrite -> ? length_is_domain, ? string_range; try congruence.
      intros z H3.
      assert (z ∈ ω) as H14 by
            eauto using elements_of_naturals_are_naturals, elts_in_set.
      set (ζ := mkSet H14 : N).
      replace z with (ζ : set) by auto.
      rewrite <-(functionify_concat_l ζ1 ζ2), <-(functionify_concat_l γ1 γ2);
        try congruence; rewrite -> lt_is_in; auto.
      now rewrite -> H2 in H3.
    + assert (length ζ2 = length γ2) as H3.
      { eapply naturals.cancellation_add.
        now rewrite <-concat_length, H1, concat_length, H2. }
      apply functionify_injective, func_ext; auto.
      * rewrite -> ? length_is_domain; congruence.
      * now rewrite -> ? string_range.
      * intros z H14.
        assert (z ∈ ω) as H15 by eauto using string_domain.
        set (ζ := mkSet H15 : N).
        replace z with (ζ : set) by auto.
        rewrite <-(sub_abba ζ (length ζ1)) at 1.
        rewrite <-(sub_abba ζ (length γ1)) at 2.
        assert (length γ1 ≤ ζ + length γ1 < length γ1 + length γ2)%N.
        { split.
          - exists ζ.
            ring.
          - rewrite -> (naturals.add_comm _ (length γ2)).
            apply naturals.O1, lt_is_in.
            rewrite -> length_is_domain, H3 in H14.
            apply H14. }
        rewrite <-? functionify_concat_r; congruence.
Qed.

Theorem length_0_empty : ∀ u, length u = 0%N → u = ε.
Proof.
  intros u H.
  apply eq_sym, functionify_injective, func_ext.
  - now rewrite -> ? length_is_domain, length_empty, H.
  - now rewrite -> ? string_range.
  - intros x H0.
    rewrite -> length_is_domain, length_empty in H0.
    contradiction (Empty_set_classification x).
Qed.

Theorem elements_of_Astar : ∀ A : reg_exp, ⋃ {A^n | n in ω} = A ⃰.
Proof.
  intros A.
  apply eq_sym, Extensionality.
  split; intros H.
  - apply Specify_classification in H as [H [y [H0 H1]]].
    subst.
    clear H.
    remember (length y) as m.
    revert m y Heqm H1.
    induction m using Strong_Induction.
    intros z H0 H1.
    inversion H1; subst.
    + apply Union_classification.
      exists (A^0).
      split.
      * apply replacement_classification.
        eauto.
      * now rewrite -> pow_0_r, singleton_realization, Singleton_classification.
    + eapply H in H6; eauto.
      * apply Union_classification in H6 as [X [H6 H7]].
        apply replacement_classification in H6 as [n H6]; subst.
        apply Union_classification.
        exists (A^(n+1)%N).
        rewrite -> replacement_classification.
        split; eauto.
        rewrite -> add_1_r, <-subsetifying_subset, pow_succ_r,
        <-concat_reg_exp, concat_sym.
        apply concat_set_classification.
        exists u, v.
        repeat split; auto.
        apply Specify_classification.
        eauto using elts_in_set.
      * rewrite -> concat_length, naturals.lt_def.
        exists (length u).
        split; try ring.
        intros H0.
        contradict H4.
        now apply eq_sym, length_0_empty in H0.
  - apply Union_classification in H as [X [H H0]].
    apply replacement_classification in H as [n H].
    subst.
    fold N in n.
    revert z H0.
    induction n using Induction.
    { intros z H0.
      rewrite -> pow_0_r, singleton_realization, Singleton_classification in H0.
      subst.
      apply Specify_classification.
      split; eauto using elts_in_set.
      exists ε.
      eauto using MStar0. }
    intros z H0.
    rewrite <-subsetifying_subset, pow_succ_r, <-concat_reg_exp,
    concat_sym in H0.
    apply concat_set_classification in H0 as [a [b [H0 [H1 H2]]]].
    subst.
    apply Specify_classification.
    split; eauto using elts_in_set.
    exists (a ++ b)%set.
    split; auto.
    apply MStarApp_full.
    apply IHn in H1.
    + apply Specify_classification in H0 as [H0 [y [H2 H3]]].
      apply set_proj_injective in H2.
      congruence.
    + apply IHn, Specify_classification in H1 as [H1 [y [H2 H3]]].
      apply set_proj_injective in H2.
      congruence.
Qed.

Theorem basic_decomposition : STR = (([0] ⌣ [1]) ⃰).
Proof.
  apply Extensionality.
  split; intros H; try eapply realization_is_subset; eauto.
  rewrite <-elements_of_Astar, Union_classification.
  set (ζ := (mkSet H : σ)).
  replace z with (ζ : set) by auto.
  exists (([0] ⌣ [1])^(length ζ)).
  split.
  - apply replacement_classification.
    now (exists (length ζ)).
  - now apply length_of_n_string.
Qed.

Theorem string_induction_l : ∀ P : σ → Prop,
    (P ε → (∀ x, P x → P (0 ++ x)) → (∀ x, P x → P (1 ++ x)) → ∀ x, P x)%set.
Proof.
  intros P H H0 H1 x.
  remember (length x) as n.
  symmetry in Heqn.
  revert x Heqn.
  induction n using Induction; intros x Heqn.
  - apply length_0_empty in Heqn.
    congruence.
  - rewrite <-length_of_n_string, <-subsetifying_subset, pow_succ_r,
    <-concat_reg_exp, concat_sym, concat_set_classification in *.
    destruct Heqn as [a [b [H2 [H3 H4]]]].
    apply set_proj_injective in H4; subst.
    rewrite -> subsetifying_subset, length_of_n_string in H3.
    apply IHn in H3.
    apply Specify_classification in H2 as [H2 [y [H4 H5]]].
    apply set_proj_injective in H4; subst.
    inversion H5; inversion H7; subst; auto.
Qed.

Theorem string_induction_r : ∀ P : σ → Prop,
    (P ε → (∀ x, P x → P (x ++ 0)) → (∀ x, P x → P (x ++ 1)) → ∀ x, P x)%set.
Proof.
  intros P H H0 H1 x.
  remember (length x) as n.
  symmetry in Heqn.
  revert x Heqn.
  induction n using Induction; intros x Heqn.
  - apply length_0_empty in Heqn.
    congruence.
  - rewrite <-length_of_n_string, <-subsetifying_subset, pow_succ_r,
    <-concat_reg_exp, concat_set_classification in *.
    destruct Heqn as [a [b [H2 [H3 H4]]]].
    apply set_proj_injective in H4; subst.
    rewrite -> subsetifying_subset, length_of_n_string in H2.
    apply IHn in H2.
    apply Specify_classification in H3 as [H3 [y [H4 H5]]].
    apply set_proj_injective in H4; subst.
    inversion H5; inversion H7; subst; auto.
Qed.

Definition regular (x : set) := ∃ A : reg_exp, x = A.

Theorem regular_union : ∀ A B, regular A → regular B → regular (A ∪ B).
Proof.
  intros A B H H0.
  destruct H as [A' H], H0 as [B' H0].
  subst.
  exists (A' ⌣ B').
  apply Extensionality.
  split; intros H.
  - apply Pairwise_union_classification in H as [H | H].
    + apply Specify_classification.
      apply Specify_classification in H as [H [ζ [H0 H1]]].
      subst.
      split; eauto using MUnionL.
    + apply Specify_classification.
      apply Specify_classification in H as [H [ζ [H0 H1]]].
      subst.
      split; eauto using MUnionR.
  - apply Specify_classification in H as [H [ζ [H0 H1]]].
    subst.
    rewrite -> Pairwise_union_classification.
    inversion H1; subst.
    + left.
      apply Specify_classification; eauto.
    + right.
      apply Specify_classification; eauto.
Qed.

Theorem regular_concat :
  ∀ A B : Σ, regular A → regular B → regular (A ++ B)%str.
Proof.
  intros A B H H0.
  destruct H as [A' H], H0 as [B' H0]; subst.
  exists (A' || B').
  apply Extensionality.
  split; intros H1.
  - rewrite <-subsetifying_subset, <-concat_reg_exp, concat_set_classification.
    apply Specify_classification in H1 as [H1 [a [b [H2 [H3 H4]]]]].
    subst.
    exists a, b.
    repeat split; auto; simpl in *; congruence.
  - rewrite <-subsetifying_subset, <-concat_reg_exp,
    concat_set_classification in H1.
    destruct H1 as [a [b [H1 [H2 H3]]]].
    subst.
    apply Specify_classification.
    split; eauto using elts_in_set.
    exists a, b.
    repeat split; auto; simpl in *; congruence.
Qed.

Theorem regular_star :
  ∀ A, regular A → ∃ B : reg_exp, A = B ∧ regular (⋃ {B^n | n in ω}).
Proof.
  intros A H.
  destruct H as [B H].
  exists B.
  split; auto.
  exists (B ⃰).
  now rewrite -> elements_of_Astar.
Qed.

Theorem union_smile : ∀ A B, (A ⌣ B : set) = A ∪ B.
Proof.
  intros A B.
  apply Extensionality.
  split; intros H.
  - apply Specify_classification in H as [H [y [H0 H1]]].
    apply Pairwise_union_classification.
    inversion H1; subst.
    + left.
      apply Specify_classification; eauto.
    + right.
      apply Specify_classification; eauto.
  - apply Specify_classification.
    apply Pairwise_union_classification in H as [H | H];
      split; apply reg_exps_are_strings in H as H0; auto;
        replace z with ((mkSet H0 : σ) : set) in *; auto;
          exists (mkSet H0 : σ); split; auto;
            [ apply MUnionL | apply MUnionR ];
            apply Specify_classification in H as [H [y [H1 H2]]];
            apply set_proj_injective in H1; congruence.
Qed.

(* This theorem is too hard to prove for now. The standard proof uses DFAs,
   and requires (in the worst case) a doubly exponential construction.
Theorem regular_complement : ∀ A, regular A → regular (STR \ A). Admitted. *)

Definition gen_series (A : Σ) :=
  seriesify ℤ (λ n, # {x in A | ∃ ξ : σ, x = ξ ∧ length ξ = n} : Z).

Infix "+" := (power_series.add ℤ) : String_scope.
Notation "- a" := (power_series.neg ℤ a) : String_scope.
Infix "*" := (power_series.mul ℤ) : String_scope.

Theorem finite_length_subsets :
  ∀ k A, (∀ x, x ∈ A → ∃ ξ : σ, x = ξ ∧ length ξ = k) → finite A.
Proof.
  intros k A H.
  eapply subsets_of_finites_are_finite.
  - apply (finite_powers_are_finite {0,1}%N k);
      auto using naturals_are_finite.
    replace {0,1}%N with (2%N : set); auto using naturals_are_finite.
    apply Extensionality.
    split; intros H0.
    + rewrite -> Pairing_classification.
      rewrite <-? S_is_succ in H0.
      unfold naturals.one in H0.
      rewrite <-? S_is_succ in H0.
      apply Pairwise_union_classification in H0 as [H0 | H0].
      * rewrite <-? S_is_succ in H0.
        apply Pairwise_union_classification in H0 as [H0 | H0];
          intuition.
        -- contradiction (Empty_set_classification z).
        -- apply Singleton_classification in H0.
           intuition.
      * apply Singleton_classification in H0.
        now right.
    + rewrite <-? S_is_succ.
      apply Pairwise_union_classification.
      unfold naturals.one.
      rewrite -> Singleton_classification, <-S_is_succ.
      apply Pairing_classification in H0 as [H0 | H0].
      * left.
        apply Pairwise_union_classification.
        rewrite -> Singleton_classification.
        intuition.
      * now right.
  - intros x H0.
    apply H in H0 as [ξ [H0 H1]].
    subst.
    apply Specify_classification.
    pose proof (func_hyp ξ).
    rewrite -> length_is_domain in H0.
    unfold functionify in H0.
    destruct constructive_indefinite_description.
    simpl in *.
    split; auto.
    destruct H0.
    now rewrite -> Powerset_classification.
Qed.

Theorem product_lemma : ∀ A B,
    unambiguous (A || B) → gen_series (A || B) = gen_series A * gen_series B.
Proof.
  intros A B H.
  apply power_series_extensionality.
  extensionality n.
  unfold gen_series.
  rewrite -> power_series.coefficient_mul, ? coefficient_seriesify.
  simpl.
  assert (∀ f g : N → N, (λ k : N, (f k : Z) * (g k : Z)) =
                         (λ k : N, (f k * g k)%N))%Z as H1.
  { intros f g.
    extensionality k.
    apply INZ_mul. }
  rewrite -> H1.
  replace (# {x in A || B | ∃ ξ : σ, x = ξ ∧ length ξ = n} : Z) with
      (sum ℤ (λ k, (# {x in (A || B) | ∃ a b : σ,
                         x = (a ++ b)%set ∧ a ∈ A ∧ b ∈ B ∧ length a = k
                         ∧ length b = (n - k)%N}) : Z) 0 n).
  - apply iterate_extensionality.
    intros k H2.
    apply INZ_eq.
    rewrite <-finite_products_card; try eapply finite_length_subsets.
    2: { intros x H0.
         apply Specify_classification in H0 as [H0 H3]; eauto. }
    2: { intros x H0.
         apply Specify_classification in H0 as [H0 H3]; eauto. }
    apply equinumerous_cardinality.
    inversion H.
    assert (bijective (concat_product A B)) as H7 by
          (split; auto using concat_surjective).
    unfold concat_product in H7.
    symmetry.
    set (f := sets.functionify (concat_function A B)) in *.
    apply two_sided_inverse_bijective_set.
    exists f, (inverse f).
    split.
    + intros a H8.
      apply Product_classification in H8 as [a' [b' [H8 [H9 H10]]]].
      subst.
      rename a' into a; rename b' into b.
      assert ((a, b) ∈ A × B) as H3.
      { apply Specify_classification in H8 as [H8 H10].
        apply Specify_classification in H9 as [H9 H11].
        apply Product_classification; eauto. }
      replace (a, b) with ((mkSet H3 : elts (A × B)) : set);
      eauto using concat_product_action.
      split.
      2: { rewrite -> left_inverse; auto.
           unfold f.
           now rewrite -> sets.functionify_domain. }
      apply Specify_classification.
      split.
      * unfold f.
        erewrite <-@sets.functionify_range.
        apply function_maps_domain_to_range.
        now rewrite -> sets.functionify_domain.
      * apply Specify_classification in H8 as [H8 [a' [H10 H11]]].
        apply Specify_classification in H9 as [H9 [b' [H12 H13]]].
        subst.
        rename a' into a; rename b' into b.
        exists a, b.
        repeat split; eauto using concat_product_action.
    + intros b H8.
      split.
      2: { rewrite -> right_inverse; auto.
           unfold f.
           rewrite -> inverse_domain, sets.functionify_range; auto.
           apply Specify_classification in H8; tauto. }
      apply Specify_classification in H8 as
          [H8 [a' [b' [H9 [H10 [H11 [H12 H13]]]]]]].
      subst.
      rename a' into a; rename b' into b.
      apply Product_classification.
      exists a, b.
      repeat split; try apply Specify_classification; eauto.
      replace (a, b) with ((inverse f) (f (a, b))).
      2: { rewrite -> left_inverse; auto.
           unfold f.
           rewrite -> sets.functionify_domain.
           apply Product_classification; eauto. }
      f_equal.
      unfold f.
      symmetry.
      assert ((a, b) ∈ A × B) as H3 by (apply Product_classification; eauto).
      replace (a, b) with ((mkSet H3 : elts (A × B)) : set);
        eauto using concat_product_action.
  - erewrite -> sum_card; eauto.
    { eapply finite_length_subsets.
      intros x H0.
      apply Specify_classification in H0 as [H0 H2]; eauto. }
    + intros k H0 x H2.
      apply Specify_classification in H2 as [H2 [a [b [H3 [H4 [H5 [H6 H7]]]]]]].
      apply Specify_classification.
      split; auto; subst.
      exists (a ++ b)%set.
      split; auto.
      rewrite -> concat_length, H7.
      destruct H0 as [H0 H3].
      now apply sub_abab in H3.
    + intros x.
      split; intros H0.
      * apply Specify_classification in H0 as [H0 [ξ [H2 H3]]].
        subst.
        apply Specify_classification in H0 as [H0 [x [H2 H3]]].
        apply set_proj_injective in H2.
        subst.
        inversion H3.
        subst.
        assert (a ∈ A) as INA.
        { apply Specify_classification; eauto using elts_in_set. }
        assert (b ∈ B) as INB.
        { apply Specify_classification; eauto using elts_in_set. }
        exists (length a).
        repeat split; auto using zero_le.
        -- rewrite -> concat_length.
           now (exists (length b)).
        -- apply Specify_classification.
           split; try (apply Specify_classification; eauto).
           exists a, b.
           repeat split; auto; try apply Specify_classification;
             eauto using elts_in_set.
           apply sub_spec.
           now rewrite -> concat_length.
        -- intros z [H2 H4].
           apply Specify_classification in H4 as
               [H4 [a' [b' [H5 [H8 [H9 [H10 H11]]]]]]].
           inversion H.
           unfold concat_product in H16.
           assert ((a, b) ∈ A × B) as INAB.
           { apply Product_classification; eauto. }
           assert ((a', b') ∈ A × B) as INAB'.
           { apply Product_classification; eauto. }
           erewrite <-? concat_product_action in H5;
             replace (a', b') with ((mkSet INAB' : elts (A × B)) : set);
             replace (a, b) with ((mkSet INAB : elts (A × B)) : set); eauto.
           rewrite -> Injective_classification in H16.
           apply H16 in H5; try now rewrite -> sets.functionify_domain.
           inversion H5.
           apply Ordered_pair_iff in H18 as [H18 H19].
           apply set_proj_injective in H18.
           congruence.
      * destruct H0 as [k [[[H0 H2] H3] _]].
        apply Specify_classification in H3 as
            [H3 [a [b [H4 [H5 [H6 [H7 H8]]]]]]].
        apply Specify_classification.
        split; auto.
        exists (a ++ b)%set.
        rewrite -> concat_length, H7, H8.
        now apply sub_abab in H2.
Qed.

Theorem sum_lemma : ∀ A B,
    unambiguous (A ⌣ B) → gen_series (A ⌣ B) = gen_series A + gen_series B.
Proof.
  intros A B H.
  apply power_series_extensionality.
  extensionality n.
  unfold gen_series.
  rewrite -> power_series.coefficient_add, ? coefficient_seriesify.
  simpl.
  rewrite -> INZ_add.
  f_equal.
  rewrite <-finite_union_cardinality; try eapply finite_length_subsets.
  2: { intros x H0.
       apply Specify_classification in H0 as [H0 H3]; eauto. }
  2: { intros x H0.
       apply Specify_classification in H0 as [H0 H3]; eauto. }
  - f_equal.
    apply Extensionality.
    split; intros H0.
    + apply Specify_classification in H0 as [H0 [ζ [H1 H2]]].
      subst.
      rewrite -> union_smile in H0.
      rewrite -> Pairwise_union_classification in *.
      destruct H0 as [H0 | H0].
      * left.
        apply Specify_classification; eauto.
      * right.
        apply Specify_classification; eauto.
    + apply Specify_classification.
      rewrite -> union_smile, Pairwise_union_classification in *.
      destruct H0 as [H0 | H0]; apply Specify_classification in H0
        as [H0 [ζ [H1 H2]]]; subst; split; eauto.
  - apply NNPP.
    intros H0.
    apply Nonempty_classification in H0 as [z H0].
    apply Pairwise_intersection_classification in H0 as [H0 H1].
    inversion H.
    contradict H6.
    apply Nonempty_classification.
    exists z.
    apply Pairwise_intersection_classification.
    rewrite -> Specify_classification in *.
    tauto.
Qed.
