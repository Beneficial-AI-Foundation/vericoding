-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_array_element (n : Nat) (x : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_array_element_in_bounds {n x : Nat} (hn : n > 0) (hx : x > 0) (hxn : x ≤ n) : 
  1 ≤ find_array_element n x ∧ find_array_element n x ≤ n :=
sorry

theorem find_array_element_first {n : Nat} (hn : n > 0) :
  find_array_element n 1 = 1 :=
sorry

theorem find_array_element_bijective {n : Nat} (hn : n > 1) :
  ∀ y : Nat, 1 ≤ y ∧ y ≤ n → ∃ x : Nat, 1 ≤ x ∧ x ≤ n ∧ find_array_element n x = y :=
sorry
-- </vc-theorems>