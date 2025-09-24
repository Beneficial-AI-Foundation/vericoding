-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsPerfectSquare (n : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsPerfectSquare_spec (n : Int) :
n ≥ 0 →
let result := IsPerfectSquare n
(result = true → ∃ i : Int, 0 ≤ i ∧ i ≤ n ∧ i * i = n) ∧
(result = false → ∀ a : Int, (0 < a*a ∧ a*a < n) → a*a ≠ n) :=
sorry
-- </vc-theorems>