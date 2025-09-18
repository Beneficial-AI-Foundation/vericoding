-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mystery (n : Int) : List Int := sorry

theorem mystery_returns_odd_factors (n : Int)
  (h : n ≥ 1) : 
  let result := mystery n
  (∀ x ∈ result, x % 2 = 1) ∧ 
  (∀ x ∈ result, n % x = 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mystery_returns_ascending (n : Int) :
  let result := mystery n
  (∀ i j, i < j → 
    ∀ x y, result.get? i = some x → result.get? j = some y → x ≤ y) := sorry

theorem mystery_numbers_in_range (n : Int)
  (h : n ≥ 1) :
  let result := mystery n
  (∀ x ∈ result, 1 ≤ x ∧ x ≤ n) ∧
  result.head? = some 1 := sorry

theorem mystery_invalid_input (n : Int)
  (h : n ≤ 0) :
  mystery n = [] := sorry
-- </vc-theorems>