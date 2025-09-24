-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arr : Nat → List Nat
| n => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arr_length (n : Nat) : (arr n).length = n := sorry

theorem arr_sequence (n : Nat) (i : Nat) (h : i < n) : 
  (arr n).get ⟨i, by rw [arr_length n]; exact h⟩ = i := sorry 

theorem arr_empty : arr 0 = [] := sorry
-- </vc-theorems>