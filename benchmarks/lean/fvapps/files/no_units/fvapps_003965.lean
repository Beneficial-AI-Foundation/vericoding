-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def survivor (n : Nat) : Bool := sorry

-- Basic properties
-- </vc-definitions>

-- <vc-theorems>
theorem survivor_returns_bool (n : Nat) : 
  survivor n = true ∨ survivor n = false := by sorry

-- Properties about n = 1

theorem one_is_survivor : 
  survivor 1 = true := by sorry

-- Consistency property

theorem survivor_is_consistent (n : Nat) :
  survivor n = survivor n := by sorry

-- At least one survivor property

theorem exists_survivor_up_to_n (n : Nat) :
  n > 0 → ∃ k : Nat, k ≤ n ∧ k > 0 ∧ survivor k = true := by sorry
-- </vc-theorems>