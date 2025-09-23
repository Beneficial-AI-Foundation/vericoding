-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stringy (n : Int) : String := sorry 

theorem stringy_length {n : Int} (h : n > 0) (h2 : n ≤ 500) : 
  (stringy n).length = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stringy_alternating {n : Int} (h : n > 0) (h2 : n ≤ 500) (i : Nat) (h3 : i < n - 1) :
  have h4 : i < (stringy n).length := sorry
  have h5 : i + 1 < (stringy n).length := sorry
  (stringy n).data[i]'h4 ≠ (stringy n).data[i+1]'h5 := sorry

theorem stringy_starts_with_one {n : Int} (h : n > 0) (h2 : n ≤ 500) :
  have h3 : 0 < (stringy n).length := sorry
  (stringy n).data[0]'h3 = '1' := sorry

theorem stringy_only_ones_and_zeros {n : Int} (h : n > 0) (h2 : n ≤ 500) (i : Nat) (h3 : i < n) :
  have h4 : i < (stringy n).length := sorry
  (stringy n).data[i]'h4 = '0' ∨ (stringy n).data[i]'h4 = '1' := sorry

theorem stringy_empty : stringy 0 = "" := sorry

theorem stringy_negative {n : Int} (h : n < 0) : stringy n = "" := sorry
-- </vc-theorems>