-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_even (n : Int) : Bool := sorry

theorem is_even_divisible_by_2 (n : Int) :
  is_even n = (n % 2 = 0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_even_plus_2 (n : Int) :
  is_even n = is_even (n + 2) := sorry

theorem is_even_neighbor (n : Int) :
  is_even n ≠ is_even (n + 1) := sorry
-- </vc-theorems>