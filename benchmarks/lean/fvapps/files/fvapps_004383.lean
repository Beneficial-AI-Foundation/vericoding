-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sxore (n : Nat) : Nat := sorry

theorem sxore_matches_manual_xor (n : Nat) : 
  sxore n = (List.range (n + 1)).foldl Nat.xor 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sxore_output_pattern (n : Nat) :
  (n % 4 = 0 → sxore n = n) ∧
  (n % 4 = 1 → sxore n = 1) ∧ 
  (n % 4 = 2 → sxore n = n + 1) ∧
  (n % 4 = 3 → sxore n = 0) := sorry
-- </vc-theorems>