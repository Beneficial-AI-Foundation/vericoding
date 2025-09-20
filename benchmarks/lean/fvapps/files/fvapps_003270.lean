-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (sum gcd : Nat) : Option (Nat × Nat) :=
  sorry

def gcd (a b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_properties (x y : Nat) (h1: x > 0) (h2: y > 0) :
  let s := x + y
  let g := gcd x y
  match solve s g with
  | none => s % g ≠ 0
  | some (a, b) => a + b = s ∧ gcd a b = g ∧ a ≤ b
  :=
sorry

theorem solve_same_number (x : Nat) (h: x > 0) :
  solve (2*x) x = some (x, x) :=
sorry
-- </vc-theorems>