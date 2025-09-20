-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def create_array (n : Nat) : Array Nat := sorry

theorem create_array_length (n : Nat) :
  (create_array n).size = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem create_array_sequential (n : Nat) (i : Nat) (h : i < n) : 
  have h' : i < (create_array n).size := by rw [create_array_length]; exact h
  (create_array n)[i]'h' = i + 1 := sorry

theorem create_array_increasing (n : Nat) (i j : Nat) 
  (hi : i < n) (hj : j < n) (h_order : i < j) :
  have hi' : i < (create_array n).size := by rw [create_array_length]; exact hi
  have hj' : j < (create_array n).size := by rw [create_array_length]; exact hj
  (create_array n)[i]'hi' < (create_array n)[j]'hj' := sorry
-- </vc-theorems>