-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_cake_cost (n m : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_cake_cost_divisible (n m : Nat)
  (hn : n > 0) (hm : m > 0) :
  find_min_cake_cost n m % n = 0 ∧ find_min_cake_cost n m % m = 0 :=
  sorry

theorem find_min_cake_cost_positive (n m : Nat)
  (hn : n > 0) (hm : m > 0) :
  find_min_cake_cost n m > 0 :=
  sorry

theorem find_min_cake_cost_symmetric (n m : Nat) 
  (hn : n > 0) (hm : m > 0) :
  find_min_cake_cost n m = find_min_cake_cost m n :=
  sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_min_cake_cost 2 3

/-
info: 12
-/
-- #guard_msgs in
-- #eval find_min_cake_cost 4 6

/-
info: 35
-/
-- #guard_msgs in
-- #eval find_min_cake_cost 5 7
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible