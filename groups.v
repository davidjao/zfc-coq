Set Warnings "-notation-bound-to-variable,-notation-overridden".
Set Warnings "-ambiguous-paths,-uniform-inheritance".
Require Export ssreflect ssrbool ssrfun iterated_ops integers.

Record group :=
  mkGroup {
      Gset :> set;
      ident : elts Gset where "1" := ident;
      mul : elts Gset → elts Gset → elts Gset where "a * b" := (mul a b);
      inv : elts Gset → elts Gset where "/ a" := (inv a);
      assoc : ∀ a b c, a * (b * c) = (a * b) * c;
      mul_1_r : ∀ a, a * 1 = a;
      mul_inv_r : ∀ a, a * / a = 1;
    }.

Arguments mul {g}.
Arguments inv {g}.
Arguments assoc {g}.
Arguments mul_1_r {g}.
Arguments mul_inv_r {g}.

Section Group.

  Context {Group : group}.
  Notation G := (elts Group).
  Declare Scope Group_scope.
  Delimit Scope Group_scope with group.
  Open Scope Group_scope.
  Bind Scope Group_scope with G.
  Notation "1" := (@ident Group) : Group_scope.
  Infix "*" := (@mul Group) : Group_scope.
  Notation "/ a" := (inv a) : Group_scope.
  Notation "/ 1" := (inv 1) : Group_scope.

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
    rewrite -{2}(mul_1_r a) -{2}(mul_inv_r (/a)) assoc mul_inv_r
            -{2}(mul_1_r 1) -{3}(mul_inv_r a) -? assoc mul_inv_r mul_1_r //.
  Qed.

  Theorem mul_inv_l : ∀ a, / a * a = 1.
  Proof.
    move=> a.
    rewrite -(mul_inv_r (/a)) -(mul_1_l (/ /a))
            -(mul_inv_r a) -? assoc mul_inv_r mul_1_r //.
  Qed.

End Group.
