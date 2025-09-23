-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_lowest_int (k : Nat) : Nat := sorry

def digits_to_sorted_list (n : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_lowest_int_positive (k : Nat) (h : k > 0) : 
  find_lowest_int k > 0 := sorry

theorem find_lowest_int_products_different (k : Nat) (h : k > 0) :
  find_lowest_int k * k ≠ find_lowest_int k * (k + 1) := sorry
-- </vc-theorems>