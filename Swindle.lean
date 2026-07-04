import Mathlib

/-!
# The abstract Eilenberg–Mazur swindle

This file isolates the *purely algebraic* core of the Mazur swindle (as used in knot
theory for infinite connected sums, and by Eilenberg in an algebraic context).

The informal slogan is:

> We can never have a context in which **all** infinite sums make sense and behave
> well, **and** every element has an inverse, **and** not everything is equal to zero.

We model "a context where all infinite sums make sense and behave well" by an additive
commutative monoid `M` together with a *total* summation operator
`ssum : (ℕ → M) → M` assigning a value to **every** sequence, subject to three
"infinitary associativity" laws:

* `sum_zero`  : the sum of the zero sequence is `0`;
* `cons`      : `ssum f = f 0 + ssum (fun i => f (i+1))` (peel off the first term);
* `pair`      : `ssum f = ssum (fun i => f (2*i) + f (2*i+1))` (group in consecutive pairs).

These are exactly the manipulations the connected-sum construction justifies for knots.

The main result (`InfSum.eq_zero_of_add_eq_zero`) is the swindle proper: any element
`a` that has an additive inverse (`a + b = 0` for some `b`) must be `0`.  Consequently,
a commutative group carrying such an operator is trivial
(`InfSum.subsingleton_of_addCommGroup`), i.e. a nontrivial commutative group admits no
well-behaved total infinite summation.

The trivial monoid `PUnit` carries such an operator (`InfSum.punit`), so the axioms are
consistent; the interest is that they are consistent only when inverses are scarce.
-/

universe u

variable {M : Type u}

/-- A total, well-behaved "infinite summation" operator on an additive commutative
monoid, encoding the infinitary associativity laws needed for the Mazur swindle. -/
structure InfSum (M : Type u) [AddCommMonoid M] where
  /-- The value assigned to a sequence `f : ℕ → M`. -/
  ssum : (ℕ → M) → M
  /-- The infinite sum of the constant zero sequence is `0`. -/
  sum_zero : ssum (fun _ => 0) = 0
  /-- Peeling off the first summand. -/
  cons : ∀ f : ℕ → M, ssum f = f 0 + ssum (fun i => f (i + 1))
  /-- Grouping the summands into consecutive pairs. -/
  pair : ∀ f : ℕ → M, ssum f = ssum (fun i => f (2 * i) + f (2 * i + 1))

namespace InfSum

/-- The trivial monoid `PUnit` carries a summation operator, so the axioms are
consistent. -/
def punit : InfSum PUnit where
  ssum _ := PUnit.unit
  sum_zero := rfl
  cons _ := rfl
  pair _ := rfl

/-
**The Eilenberg–Mazur swindle.**  In any commutative monoid equipped with a
well-behaved total infinite summation, every element that has an additive inverse is
zero.
-/
theorem eq_zero_of_add_eq_zero [AddCommMonoid M] (S : InfSum M) {a b : M}
    (h : a + b = 0) : a = 0 := by
  have := S.pair ( fun i => if Even i then a else b );
  have := S.cons ( fun i => if Even i then a else b ) ; simp_all +decide [ Nat.even_add_one ] ;
  have := S.pair ( fun i => if Odd i then a else b ) ; simp_all +decide ;
  simp_all +decide [ Nat.even_iff, Nat.odd_iff ];
  simp_all +decide [ add_comm, S.sum_zero ]

/-- A commutative *group* equipped with a well-behaved total infinite summation is
trivial: every element is `0`.  Equivalently, no nontrivial commutative group admits
such an operator. -/
theorem eq_zero_of_addCommGroup [AddCommGroup M] (S : InfSum M) (a : M) :
    a = 0 :=
  S.eq_zero_of_add_eq_zero (add_neg_cancel a)

/-- A commutative group carrying a well-behaved total infinite summation is a
subsingleton. -/
theorem subsingleton_of_addCommGroup [AddCommGroup M] (S : InfSum M) :
    Subsingleton M :=
  ⟨fun x y => by rw [S.eq_zero_of_addCommGroup x, S.eq_zero_of_addCommGroup y]⟩

end InfSum