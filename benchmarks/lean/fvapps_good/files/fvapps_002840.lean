-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_divide_by (n a b : Int) : Bool := sorry

theorem is_divide_by_correct (n a b : Int) (ha : a ≠ 0) (hb : b ≠ 0) : 
  is_divide_by n a b = true ↔ n % a = 0 ∧ n % b = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divide_by_one (n : Int) :
  is_divide_by n 1 1 = true := sorry

theorem divide_by_self (n a : Int) (h : a ≠ 0) :
  is_divide_by a a a = true := sorry

theorem divide_by_zero_error (n : Int) :
  is_divide_by n 0 1 = false ∧ is_divide_by n 1 0 = false := sorry
-- </vc-theorems>