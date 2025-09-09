-- <vc-helpers>
-- </vc-helpers>

def quicksum (s : String) : Nat :=
  sorry

theorem quicksum_invalid_packets (s : String)
  (h : ∃ c ∈ s.data, c ≠ ' ' ∧ ¬(65 ≤ c.toNat ∧ c.toNat ≤ 90)) :
  quicksum s = 0 :=
  sorry

/-
info: 46
-/
-- #guard_msgs in
-- #eval quicksum "ACM"

/-
info: 75
-/
-- #guard_msgs in
-- #eval quicksum "A C M"

/-
info: 0
-/
-- #guard_msgs in
-- #eval quicksum "As "

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible