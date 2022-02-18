Set Warnings "-notation-bound-to-variable,-notation-overridden".
Set Warnings "-ambiguous-paths,-uniform-inheritance".
Require Export iterated_ops integers.

Record group :=
  mkGroup {
      Gset :> set;
      id : elts Gset where "1" := id;
      mul : elts Gset → elts Gset → elts Gset where "a * b" := (mul a b);
      inv : elts Gset → elts Gset where "/ a" := (inv a);
      assoc : ∀ a b c, a * (b * c) = (a * b) * c;
      mul_1_r : ∀ a, a * 1 = a;
      mul_inv_r : ∀ a, a * / a = 1;
    }.

Section Group_theorems.

  Variable Group : group.
  Notation G := (elts Group).
  Declare Scope Group_scope.
  Delimit Scope Group_scope with group.
  Open Scope Group_scope.
  Bind Scope Group_scope with G.
  Notation "1" := (id Group) : Group_scope.
  Infix "*" := (mul Group) : Group_scope.
  Notation "/ a" := (inv Group a) : Group_scope.
  Notation "/ 1" := (inv Group 1) : Group_scope.

  Definition IGS (g : G) := elt_to_set g : set.

  Global Coercion IGS : G >-> set.

  Definition div (a b : G) := a * / b : G.

  Infix "/" := div : Group_scope.

  Lemma sub_is_neg : ∀ a b, a / b = a * / b.
  Proof.
    auto.
  Qed.

  Theorem mul_1_l : ∀ a, 1 * a = a.
  Proof.
    move=> a.
    rewrite -(mul_1_r _ (1 * a)) -assoc
            -{2}(mul_inv_r _ (/a)) (assoc _ a) mul_inv_r assoc mul_1_r
            -(mul_inv_r _ a) -assoc mul_inv_r mul_1_r //.
  Qed.

  Theorem mul_inv_l : ∀ a, / a * a = 1.
  Proof.
    move=> a.
    rewrite -{2}(mul_1_r _ a) -{1}(mul_inv_r _ (/a)) (assoc _ a) mul_inv_r
                                  mul_1_l mul_inv_r //.
  Qed.

End Group_theorems.
