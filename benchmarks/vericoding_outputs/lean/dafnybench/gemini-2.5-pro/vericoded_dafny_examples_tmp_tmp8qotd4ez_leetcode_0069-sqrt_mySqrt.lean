import Mathlib
-- <vc-preamble>
def sqrt (x : Int) (r : Int) : Bool :=
r*r ≤ x ∧ (r+1)*(r+1) > x
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def mySqrt (x : Int) : Int :=
(Nat.sqrt x.toNat)
-- </vc-definitions>

-- <vc-theorems>
theorem mySqrt_spec (x : Int) :
x ≥ 0 → sqrt x (mySqrt x) :=
by
  intro hx
  -- The `sqrt` function returns a `Bool` but is defined with `Prop`s.
  -- The expression `P ∧ Q` is a `Prop`, so Lean inserts `decide` to get a `Bool`,
  -- resulting in `decide (P ∧ Q)`.
  -- The goal `sqrt x (mySqrt x)` in a `Prop` context means `sqrt x (mySqrt x) = true`.
  unfold sqrt
  -- The goal is `decide (mySqrt x * mySqrt x ≤ x ∧ (mySqrt x + 1) * (mySqrt x + 1) > x) = true`.
  -- The erroneous `rw [Bool.and_eq_true_iff]` failed because the goal is not of the form `(a && b) = true`.
  -- We use `decide_eq_true_iff` to change the goal into a `Prop`.
  simp only [decide_eq_true_iff]
  -- The goal is now the `Prop`: `mySqrt x * mySqrt x ≤ x ∧ (mySqrt x + 1) * (mySqrt x + 1) > x`.
  dsimp [mySqrt]
  rw [← Int.toNat_of_nonneg hx]
  norm_cast
  exact ⟨Nat.sqrt_le _, Nat.lt_succ_sqrt _⟩
-- </vc-theorems>
