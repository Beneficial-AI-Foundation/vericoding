-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def group_size (s d: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem group_size_is_nat (s d: Nat) (h1: s > 0) (h2: s ≤ 100) (h3: d ≤ 1000) :
  group_size s d ≥ 0 := sorry

theorem group_size_known_cases : 
  (group_size 1 6 = 3) ∧ 
  (group_size 3 10 = 5) ∧ 
  (group_size 5 7 = 6) := sorry
-- </vc-theorems>