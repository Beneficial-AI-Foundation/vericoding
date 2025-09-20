-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_possible_divide (nums : List Nat) (k : Nat) : Bool := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem list_length_div_k {nums : List Nat} {k : Nat} (h : k > 0) : 
  nums.length % k ≠ 0 → ¬(is_possible_divide nums k) :=
  sorry

theorem single_number_sequence {nums : List Nat} (h : nums.length > 0) :
  is_possible_divide nums 1 :=
  sorry
-- </vc-theorems>