-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.reverse (s : String) : String := sorry

def reverse (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_non_negative (n : Nat) : 
  reverse n ≥ 0 := sorry

theorem reverse_length_leq (n : Nat) :
  n > 0 → n ≤ 10^9 → 
  (toString (reverse n)).length ≤ (toString n).length := sorry

theorem reverse_single_digit (n : Nat) :
  n ≤ 9 → reverse n = n := sorry
-- </vc-theorems>