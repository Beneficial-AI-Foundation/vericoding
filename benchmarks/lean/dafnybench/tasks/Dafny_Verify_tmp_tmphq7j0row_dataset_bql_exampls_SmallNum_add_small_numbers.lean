-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add_small_numbers (a : Array Int) (n : Int) (max : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_small_numbers_spec (a : Array Int) (n : Int) (max : Int) (r : Int) :
n > 0 ∧
n ≤ a.size ∧
(∀ i : Nat, i < n → a[i]! ≤ max) →
r ≤ max * n :=
sorry
-- </vc-theorems>