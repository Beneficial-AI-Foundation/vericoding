-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isClassyNumber (n : Nat) : Bool := sorry

def countClassyIntegers (start : Nat) (finish : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_is_nonnegative (start finish : Nat) : 
  countClassyIntegers start finish ≥ 0 := sorry

theorem count_bounded_by_range (start finish : Nat) :
  countClassyIntegers start finish ≤ finish - start + 1 := sorry

theorem empty_range_is_zero (start finish : Nat) :
  start > finish → countClassyIntegers start finish = 0 := sorry

theorem singleton_range_classy (n : Nat) :
  countClassyIntegers n n = (if isClassyNumber n then 1 else 0) := sorry
-- </vc-theorems>