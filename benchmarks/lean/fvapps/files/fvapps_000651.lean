-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_minimum_array_sum (arr : List Nat) : Nat := sorry

def gcd (a b : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_minimum_sum {x : Nat} (h : x > 0) : 
  find_minimum_array_sum [x] = x := sorry

theorem same_number {n : Nat} {x : Nat} (h : n ≥ 2) (h₁ : x > 0) :
  find_minimum_array_sum (List.replicate n x) = n * x := sorry
-- </vc-theorems>