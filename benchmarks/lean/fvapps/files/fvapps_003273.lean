-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def f (x : α) : Option Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem positive_integers_sum {n : Nat} (h : n > 0) :
  f n = some (n * (n + 1) / 2) :=
sorry

theorem non_positive_returns_none {n : Int} (h : n ≤ 0) :
  f n = none :=
sorry

theorem non_integer_returns_none (x : Float) :
  f x = none :=
sorry

theorem non_numeric_returns_none (α : Type) (x : α) :
  f x = none :=
sorry

theorem handles_large_inputs (n : Nat) :
  f n ≠ none → ∃ m : Nat, f n = some m ∧ m > 0 :=
sorry
-- </vc-theorems>