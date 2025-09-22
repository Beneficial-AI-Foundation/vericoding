-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def odd_row (n : Nat) : List Nat := sorry

theorem odd_row_length (n : Nat) (h : n > 0) :
  (odd_row n).length = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_row_all_odd (n : Nat) (h : n > 0) :
  ∀ x ∈ odd_row n, x % 2 = 1 := sorry

theorem odd_row_sequential_differences (n : Nat) (h : n > 0) :
  ∀ i, i < (odd_row n).length - 1 → 
    ((odd_row n)[i+1]? >>= fun x => (odd_row n)[i]? >>= fun y => some (x - y)) = some 2 := sorry

theorem odd_row_first_element (n : Nat) (h : n > 0) :
  (odd_row n).head? = some (n * (n-1) + 1) := sorry
-- </vc-theorems>