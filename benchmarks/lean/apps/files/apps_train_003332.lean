-- <vc-preamble>
def find_key (s : String) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrime (n : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_key_edge_cases :
  find_key "0" = 0 ∧ find_key "1" = 0 :=
  sorry

/-
info: 1080
-/
-- #guard_msgs in
-- #eval find_key "47b"

/-
info: 9328
-/
-- #guard_msgs in
-- #eval find_key "2533"

/-
info: 6912
-/
-- #guard_msgs in
-- #eval find_key "1ba9"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible