Set Warnings "-ambiguous-paths".
Require Export sets polynomials.

Definition STR := (⋃ {({0%N, 1%N}^n)%set | n in ω})%N.

Theorem STR_classification : ∀ f, f ∈ STR ↔ ∃ n : N, is_function f n {0, 1}%N.
Proof.
  rewrite /STR => f.
  split => [/Union_classification
             [x [/replacement_classification [n ->] /Specify_classification []]]
           | [n /[dup] H [H0 H1]]]; eauto.
  rewrite Union_classification.
  exists ({0%N, 1%N}^n).
  rewrite replacement_classification Specify_classification
          Powerset_classification; eauto.
Qed.

Theorem zero_string_constr : (const_function 1 (Pairing_left 0 1) ∈ STR)%N.
Proof.
  rewrite STR_classification.
  exists 1%N.
  move: (func_hyp (const_function 1 (Pairing_left 0 1)))%N.
  rewrite const_domain const_range //.
Qed.

Theorem one_string_constr : (const_function 1 (Pairing_right 0 1) ∈ STR)%N.
Proof.
  rewrite STR_classification.
  exists 1%N.
  move: (func_hyp (const_function 1 (Pairing_right 0 1)))%N.
  rewrite const_domain const_range //.
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

Theorem functionify_graph : ∀ s : σ, graph (s : function) = s.
Proof.
  rewrite /functionify => s.
  repeat elim: constructive_indefinite_description => //.
Qed.

Theorem string_range : ∀ x : σ, range x = {0, 1}%N.
Proof.
  rewrite /functionify => x.
  elim: constructive_indefinite_description => //.
Qed.

Definition zero_string := mkSet zero_string_constr : σ.
Definition one_string := mkSet one_string_constr : σ.
Notation "0" := zero_string : String_scope.
Notation "1" := one_string : String_scope.

Theorem zero_action : 0 0%N = 0%N.
Proof.
  rewrite /zero_string /functionify.
  elim constructive_indefinite_description => x H /=.
  have ->: mkFunc H = (const_function 1 (Pairing_left 0 1))%N by
    apply function_record_injective; rewrite ? const_range //.
  rewrite const_action // -[∅]/(0%N : set) -lt_is_in.
  auto using (naturals.succ_lt 0%N).
Qed.

Theorem one_action : 1 0%N = 1%N.
Proof.
  rewrite /zero_string /functionify.
  elim constructive_indefinite_description => x H /=.
  have ->: mkFunc H = (const_function 1 (Pairing_right 0 1))%N by
    apply function_record_injective; rewrite ? const_range //.
  rewrite const_action // -[∅]/(0%N : set) -lt_is_in.
  auto using (naturals.succ_lt 0%N).
Qed.

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
  move: (func_hyp (const_function 1 (Pairing_left 0 1)))%N.
  rewrite /length /zero_string const_domain const_range => H.
  repeat elim: constructive_indefinite_description => /= *.
  eauto using set_proj_injective, domain_uniqueness.
Qed.

Theorem length_one : length 1 = 1%N.
Proof.
  move: (func_hyp (const_function 1 (Pairing_right 0 1)))%N.
  rewrite /length /zero_string const_domain const_range => H.
  repeat elim: constructive_indefinite_description => /= *.
  eauto using set_proj_injective, domain_uniqueness.
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
  Hypothesis F : is_function f n {0, 1}%N.
  Hypothesis G : is_function g m {0, 1}%N.

  Definition concat_elements : elts (n + m)%N → elts {0, 1}%N.
  Proof.
    move=> x.
    have H: (x ∈ ω) by
      eauto using elements_of_naturals_are_naturals, elts_in_set.
    case (excluded_middle_informative (mkSet H < n)%N) =>
           [/lt_is_in H0 | /naturals.le_not_gt /sub_abab H0].
    - have H1: (mkFunc F) x ∈ {0%N, 1%N}.
      { rewrite -[{0%N, 1%N}]/(range (mkFunc F)).
        auto using function_maps_domain_to_range. }
      exact (mkSet H1).
    - have H1: (mkFunc G) (mkSet H - n)%N ∈ {0%N, 1%N}.
      { rewrite -[{0%N, 1%N}]/(range (mkFunc G)).
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
    exists (n + m)%N.
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
  move=> H.
  contradiction (PA4 0).
  apply set_proj_injective.
  rewrite -[elt_to_set]/INS -zero_action -one_action H //.
Qed.

Theorem functionify_concat_l : ∀ a b x, (x < length a)%N → (a ++ b)%set x = a x.
Proof.
  move: length_is_domain => /[swap] a /(_ a) /[swap] b /[swap] x /[swap] H.
  destruct a as [a A], b as [b B], x as [x X].
  rewrite /functionify /concat /ssr_have.
  (repeat elim constructive_indefinite_description => /=) =>
    n H0 m H1 a' H2 m' H3 /set_proj_injective H4.
  have ?: m = m'; subst; eauto using set_proj_injective, domain_uniqueness.
  rewrite (proof_irrelevance _ H3 H1) => {H3}.
  set (m := (length (mkSet A))) in *.
  have ?: (a' = m + n)%N; subst;
    eauto using set_proj_injective, domain_uniqueness, functionify_is_function.
  have ->: mkFunc H2 = sets.functionify (concat_elements H1 H0) by
    auto using function_record_injective, sets.functionify_range.
  rewrite /sets.functionify.
  elim constructive_indefinite_description => [f [H3 [H4 H5]]].
  have H6: (x ∈ m + n)%N by
    move: H (le_add m n) => /lt_is_in /[swap] /le_is_subset /[apply] //.
  rewrite -{1}[x]/(mkSet H6 : set) H5 /concat_elements /ssr_have /=.
  rewrite (proof_irrelevance _ (elements_of_naturals_are_naturals _ _ _ H6)).
  by case excluded_middle_informative.
Qed.

Theorem functionify_concat_r : ∀ a b x,
    (length a ≤ x < length a + length b → (a ++ b)%set x = b (x - length a))%N.
Proof.
  move: length_is_domain => /[swap] a /[dup] /(_ a) A0 /[swap] b /(_ b) B0 =>
        x [/[dup] H /naturals.le_not_gt H0 /[dup] H1 /lt_is_in H2].
  move: A0 B0.
  destruct a as [a A], b as [b B], x as [x X].
  rewrite /functionify /concat /ssr_have.
  (repeat elim constructive_indefinite_description => /=) =>
    n H3 m H4 a' H5 n' H6 m' H7 /set_proj_injective H8 /set_proj_injective H9.
  have ?: m = m'; have ?: n = n'; subst;
    eauto using set_proj_injective, domain_uniqueness.
  rewrite (proof_irrelevance _ H6 H3) => {H6} {H7}.
  set (m := (length (mkSet A))) in *.
  set (n := (length (mkSet B))) in *.
  have ?: (a' = m + n)%N; subst;
    eauto using set_proj_injective, domain_uniqueness, functionify_is_function.
  have ->: mkFunc H5 = sets.functionify (concat_elements H4 H3) by
    auto using function_record_injective, sets.functionify_range.
  rewrite /sets.functionify.
  elim constructive_indefinite_description => [f [H6 [H7 H8]]].
  rewrite -[x]/(mkSet H2 : set) H8 /concat_elements /ssr_have /=.
  rewrite (proof_irrelevance _ (elements_of_naturals_are_naturals _ _ _ H2)).
  by case excluded_middle_informative.
Qed.

Theorem app_assoc : ∀ a b c : σ, (a ++ (b ++ c)%set = (a ++ b)%set ++ c)%set.
Proof.
  move=> a b c.
  ((apply functionify_injective, func_ext => [ | | x]);
   rewrite ? string_range ? length_is_domain ? concat_length //;
           first (f_equal; ring)) => /[dup] /elements_of_naturals_are_naturals
  => /(_ (elts_in_set _)) H.
  rewrite -[x]/((mkSet H : N) : set) => /lt_is_in H0.
  case: (classic (mkSet H < length a)%N) =>
        [H1 | /naturals.le_not_gt /[dup] H1 /sub_abab H2].
  { rewrite ? functionify_concat_l // concat_length.
    eauto using naturals.lt_le_trans, le_add. }
  case: (classic (mkSet H < (length a + length b)))%N =>
        [H3 | /naturals.le_not_gt H3].
  { rewrite functionify_concat_r 1 ? functionify_concat_l 1
            ? functionify_concat_l ? functionify_concat_r ? concat_length; auto.
    by rewrite -H2 ? (naturals.add_comm (length a)) -naturals.O1_iff in H3. }
  rewrite ? functionify_concat_r ? concat_length -? naturals.add_assoc; auto.
  - split; rewrite -H2 ? (naturals.add_comm (length a)) in H0 H3;
      move: H0 H3; by rewrite -naturals.O1_le_iff -naturals.O1_iff.
  - apply f_equal, f_equal, eq_sym, sub_spec, sub_spec.
    by rewrite naturals.add_assoc sub_abab.
Qed.

Theorem concat_assoc :
  ∀ A B C, A ++ (B ++ C) = (A ++ B) ++ C.
Proof.
  move=> A B C.
  apply set_proj_injective, Extensionality => ?.
  rewrite ? concat_set_classification.
  split => [[x [y [H [/concat_set_classification
                       [z [w [H0 [H1 /set_proj_injective H2]]]] H3]]]] |
             [x [y [/concat_set_classification
                     [z [w [H [H0 /set_proj_injective H1]]]] [H2 H3]]]]];
           subst; [ exists (x ++ z)%set, w | exists z, (w ++ y)%set ];
           rewrite concat_set_classification app_assoc; eauto 7.
Qed.

Theorem append_ε_r : ∀ b, (b ++ ε)%set = b.
Proof.
  move=> b.
  (apply eq_sym, functionify_injective, func_ext => [ | | x]);
  rewrite ? string_range // ? length_is_domain ? concat_length ? length_empty
          ? add_0_r // => H.
  have H0: x ∈ ω by eauto using elements_of_naturals_are_naturals, elts_in_set.
  rewrite -[x]/((mkSet H0 : N) : set) functionify_concat_l // lt_is_in //.
Qed.

Theorem concat_ε_r : ∀ A, A ++ [ε] = A.
Proof.
  move=> A.
  apply set_proj_injective, Extensionality => z.
  (split; rewrite concat_set_classification) => [[a [b [H]]] | H].
  - rewrite subsetifying_subset singleton_realization Singleton_classification
            => [[/set_proj_injective ->]].
    rewrite append_ε_r => -> //.
  - move: (elts_in_set A) => /Powerset_classification /(_ _ H) H0.
    exists (mkSet H0), ε.
    by rewrite -[z]/(mkSet H0 : set) append_ε_r subsetifying_subset
                   singleton_realization Singleton_classification.
Qed.

Lemma concat_sym : ∀ n A, A^n ++ A = A ++ A^n.
Proof.
  (elim/Induction => [A | n H A]);
  rewrite ? pow_0_r ? concat_ε_l ? concat_ε_r // ? pow_succ_r
          -? concat_reg_exp {1}H concat_assoc //.
Qed.

Theorem pow_add_r : ∀ n m A, (A^(n+m)%N : Σ) = A^n || A^m.
Proof.
  (elim/Induction => [m A | n H m A]);
  rewrite ? pow_0_r ? add_0_l -? concat_reg_exp ? concat_ε_l //
          add_comm add_succ_r add_comm ? pow_succ_r -? concat_reg_exp
          H -concat_reg_exp -? concat_assoc concat_sym //.
Qed.

Theorem length_of_n_string :
  ∀ (n : N) (x : σ), x ∈ (([0] ⌣ [1])^n)%str ↔ length x = n.
Proof.
  ((elim/Induction => [x | n H x]; split); move: (length_is_domain x);
   rewrite ? pow_0_r ? singleton_realization ? Singleton_classification) =>
    [/[swap] /set_proj_injective -> | /[swap] /[dup] H -> H0 | H0 | H0 H1];
    auto using length_empty.
  - apply f_equal, functionify_injective, func_ext;
      rewrite ? string_range // ? length_is_domain ? length_empty ? H // =>
            z /Empty_set_classification //.
  - rewrite -subsetifying_subset pow_succ_r -concat_reg_exp =>
              /Specify_classification
               [H1 [a [b [H2 [/Specify_classification
                               [H3 [y [/set_proj_injective H4 H5]]]
                               /set_proj_injective ?]]]]]; subst.
    have <-: length a = n by apply H.
    rewrite concat_length -add_1_r.
    f_equal.
    inversion H5 as [ | x A B H4 | | | | ]; subst;
      inversion H4; subst; auto using length_zero, length_one.
  - rewrite -subsetifying_subset pow_succ_r
            -concat_reg_exp concat_set_classification.
    have H2: domain (restriction x n) = n.
    { rewrite restriction_domain H0 H1.
      by have ->: n ∩ S n = n by apply Intersection_subset, subset_S. }
    have H3: graph (restriction x n) ∈ STR.
    { apply STR_classification; eauto.
      exists n.
      move: (func_hyp (restriction x n)).
      by rewrite restriction_graph restriction_range string_range H2. }
    have H4: length (mkSet H3) = n.
    { rewrite /length.
      elim constructive_indefinite_description => *.
      apply set_proj_injective.
      eapply domain_uniqueness; eauto.
      move: (func_hyp (restriction x n)).
      rewrite H2 string_range //. }
    exists (mkSet H3), (If (x n = 0%N) then 0 else 1).
    (repeat split; first by apply H);
    try (by (case excluded_middle_informative => _);
         rewrite Specify_classification;
         eauto using elts_in_set, MUnionL, MUnionR, MChar).
    (apply f_equal, functionify_injective, func_ext => [ | | s]);
    rewrite ? string_range // ? length_is_domain ? concat_length ? H4 ? H1;
    first by (case excluded_middle_informative => _);
    rewrite ? length_zero ? length_one add_succ_r add_0_r //.
    rewrite -S_is_succ /succ Pairwise_union_classification =>
              [[H5 | /Singleton_classification ->]].
    + have H6: s ∈ ω by
        eauto using (elements_of_naturals_are_naturals n), elts_in_set.
      rewrite (reify H6) -[elt_to_set]/INS functionify_concat_l ? H4;
        rewrite ? lt_is_in // /=; erewrite (restriction_action _ n).
      * f_equal.
        apply function_record_injective;
          rewrite ? restriction_range ? string_range //
                  restriction_graph functionify_graph //.
      * rewrite H0 H1 Pairwise_intersection_classification.
        split; auto; by apply subset_S.
    + rewrite functionify_concat_r ? H4;
        first by (case excluded_middle_informative => _);
        rewrite ? length_zero ? length_one add_1_r;
        eauto using naturals.le_refl, naturals.succ_lt.
      have /Pairing_classification: x n ∈ {0, 1}%N.
      { rewrite -(string_range x).
        apply function_maps_domain_to_range.
        rewrite H0 H1.
        apply in_S. }
      (case excluded_middle_informative => [-> _| /[swap] [[-> // | -> _]]]);
      rewrite sub_diag ? zero_action ? one_action //.
Qed.

Theorem unambiguous_length :
  ∀ x y z w : σ, (x ++ y = z ++ w)%set → length x = length z → (x, y) = (z, w).
Proof.
  move=> x y z w H H0.
  apply Ordered_pair_iff, conj.
  - apply f_equal, functionify_injective, func_ext;
      rewrite ? length_is_domain ? string_range ? H0 // => s /[dup] /[dup] H1.
    have S: s ∈ ω by eauto using elements_of_naturals_are_naturals, elts_in_set.
    rewrite (reify S) -[elt_to_set]/INS -{1}H0 => /lt_is_in H2 /lt_is_in H3.
    erewrite <-functionify_concat_l, <-(functionify_concat_l z), H; auto.
  - have H1: length y = length w.
    { apply (naturals.cancellation_add (length x)).
      rewrite {2}H0 -? concat_length H //. }
    apply f_equal, functionify_injective, func_ext;
      rewrite ? length_is_domain ? string_range ? H1 // => s /[dup] /[dup] H2.
    have S: s ∈ ω by eauto using elements_of_naturals_are_naturals, elts_in_set.
    rewrite (reify S) -{3}(sub_abba (mkSet S) (length x)) -{1}H1
            -{4}(sub_abba (mkSet S) (length z)) => /lt_is_in H3 /lt_is_in H4.
    erewrite <-functionify_concat_r, <-(functionify_concat_r z);
      rewrite ? H ? H0 ? H1 //; split; rewrite ? (add_comm (length z));
      auto using naturals.O1, le_add_l.
Qed.

Theorem unambiguous_all_strings : unambiguous (([0] ⌣ [1]) ⃰).
Proof.
  apply unambiguous_star => [ | n m H | ].
  - apply unambiguous_union, Extensionality;
      auto using singleton_unambiguous => z.
    split => [/Pairwise_intersection_classification |
               /Empty_set_classification //].
    rewrite ? singleton_realization ? Singleton_classification =>
              [[ ]] -> /set_proj_injective /zero_ne_1 //.
  - apply NNPP => /Nonempty_classification
                   [x /Pairwise_intersection_classification [H0 H1]].
    move: H0 H1 H => /[dup] /realization_is_subset H.
    rewrite (reify H) -[elt_to_set]/setify ? length_of_n_string => -> //.
  - apply Injective_classification => x y.
    rewrite {1 2}/concat_product sets.functionify_domain =>
              /[dup] H /[swap] /[dup] H0 /[swap].
    rewrite {2}(reify H) {2 3}(reify H0) =>
              /Product_classification
               [x1 [x2 [/[dup] H1 /realization_is_subset H2
                         [/[dup] H3 /realization_is_subset H4 ?]]]]
               /Product_classification
               [y1 [y2 [/[dup] H5 /realization_is_subset H6
                         [/[dup] H7 /realization_is_subset H8 ?]]]]; subst.
    rewrite (reify H2) (reify H4) (reify H6) (reify H8)
            -[elt_to_set]/setify in H1 H3 H5 H7.
    have H9: length (mkSet H2) = length (mkSet H6).
    { rewrite -(pow_1_r ([0] ⌣ [1])) in H1 H5.
      apply length_of_n_string in H1, H5.
      congruence. }
    erewrite (concat_product_action _ _ _ (mkSet H2) (mkSet H4)),
      (concat_product_action _ _ _ (mkSet H6) (mkSet H8)); eauto =>
               /set_proj_injective /unambiguous_length /(_ H9) //.
Qed.

Theorem length_0_empty : ∀ u, length u = 0%N → u = ε.
Proof.
  move=> u H.
  apply eq_sym, functionify_injective, func_ext;
    rewrite ? length_is_domain ? length_empty ? H ? string_range // =>
          x /Empty_set_classification //.
Qed.

Theorem star_realization : ∀ A : reg_exp, ⋃ {A^n | n in ω} = A ⃰.
Proof.
  move=> A.
  apply eq_sym, Extensionality => z.
  split => [/Specify_classification [_ [y [-> H]]] |
             /Union_classification [X [/replacement_classification [n ->] H]]].
  - remember (length y) as m.
    revert m y Heqm H.
    induction m as [m H] using Strong_Induction => x H0 H1.
    inversion H1 as [ | | | | | u v H2 H3 H4 H5 ]; subst.
    + apply Union_classification.
      exists (A^0).
      rewrite replacement_classification {2}pow_0_r singleton_realization
              Singleton_classification.
      eauto.
    + eapply H in H5; eauto.
      * move: H5 => /Union_classification
                     [X [/replacement_classification [n ->] H5]].
        rewrite Union_classification.
        exists (A^(n + 1)%N).
        rewrite add_1_r -{2}subsetifying_subset pow_succ_r
                -concat_reg_exp concat_sym concat_set_classification
                                replacement_classification.
        split; eauto.
        exists u, v.
        rewrite Specify_classification.
        eauto 6 using elts_in_set.
      * rewrite concat_length -{1}(add_0_l (length v)).
        apply naturals.O1, nonzero_lt.
        move: H4 => /[swap] /length_0_empty //.
  - elim/Induction: n z H => [z | n IHn z].
    + rewrite pow_0_r singleton_realization Singleton_classification
              Specify_classification => ->.
      eauto using elts_in_set, MStar0.
    + rewrite -subsetifying_subset pow_succ_r -concat_reg_exp concat_sym =>
                /concat_set_classification
                 [a [b [/Specify_classification
                         [H [x [/set_proj_injective -> H0]]]
                         [/[dup] H1 /IHn /Specify_classification
                           [H2 [y [/set_proj_injective -> H3]]] ->]]]].
      apply Specify_classification.
      eauto using elts_in_set, MStarApp_full.
Qed.

Theorem basic_decomposition : STR = (([0] ⌣ [1]) ⃰).
Proof.
  apply Extensionality => z.
  split => [H | /realization_is_subset //].
  rewrite -star_realization Union_classification.
  exists (([0] ⌣ [1])^(length (mkSet H))).
  rewrite -{2}[z]/(setify (mkSet H)) replacement_classification
              length_of_n_string; eauto.
Qed.

Theorem string_induction_l : ∀ P : σ → Prop,
    (P ε → (∀ x, P x → P (0 ++ x)) → (∀ x, P x → P (1 ++ x)) → ∀ x, P x)%set.
Proof.
  move=> P ? ? ? x.
  remember (length x) as n.
  elim/Induction: n x Heqn =>
        [x /(@eq_sym N) /length_0_empty -> // | n H x /(@eq_sym N)].
  rewrite -length_of_n_string -subsetifying_subset pow_succ_r
          -concat_reg_exp concat_sym concat_set_classification =>
            [[a [b [/[swap] [[/[swap] /set_proj_injective ->]]]]]].
  rewrite subsetifying_subset length_of_n_string =>
            /(@eq_sym N) /H /[swap] /Specify_classification
             [? [y [/set_proj_injective -> H0]]].
  inversion H0 as [ | ? ? ? H1 | ? ? ? H1 | | | ]; inversion H1; subst; auto.
Qed.

Theorem string_induction_r : ∀ P : σ → Prop,
    (P ε → (∀ x, P x → P (x ++ 0)) → (∀ x, P x → P (x ++ 1)) → ∀ x, P x)%set.
Proof.
  move=> P ? ? ? x.
  remember (length x) as n.
  elim/Induction: n x Heqn =>
        [x /(@eq_sym N) /length_0_empty -> // | n H x /(@eq_sym N)].
  rewrite -length_of_n_string -subsetifying_subset pow_succ_r
          -concat_reg_exp concat_set_classification =>
            [[a [b [/[swap] [[/[swap] /set_proj_injective ->]]]]]].
  rewrite subsetifying_subset length_of_n_string =>
            /[swap] /(@eq_sym N) /H /[swap] /Specify_classification
             [? [y [/set_proj_injective -> H0]]].
  inversion H0 as [ | ? ? ? H1 | ? ? ? H1 | | | ]; inversion H1; subst; auto.
Qed.

Definition regular (x : set) := ∃ A : reg_exp, x = A.

Lemma union_realization : ∀ A B : reg_exp, A ∪ B = A ⌣ B.
Proof.
  move=> A B.
  apply Extensionality => ?.
  rewrite Pairwise_union_classification ? Specify_classification.
  split => [[[? [? [-> H]]] | [? [? [-> H]]]] | [? [? [-> H]]]];
           do 2 (eauto using MUnionL, MUnionR, elts_in_set; try inversion H).
Qed.

Theorem regular_union : ∀ A B, regular A → regular B → regular (A ∪ B).
Proof.
  move=> ? ? [A ->] [B ->].
  firstorder using union_realization.
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
  now rewrite -> star_realization.
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
  - apply (finite_powers_are_finite {0, 1}%N k);
      auto using naturals_are_finite.
    replace {0, 1}%N with (2%N : set); auto using naturals_are_finite.
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
