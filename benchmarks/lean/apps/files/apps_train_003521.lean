-- <vc-helpers>
-- </vc-helpers>

def hex_to_dec (s : String) : Nat :=
  sorry

theorem dec_to_hex_to_dec_roundtrip (n : Nat) :
  hex_to_dec (String.mk (Nat.toDigits 16 n)) = n :=
sorry

theorem invalid_hex_raises (s : String)
  (h : ∃ c ∈ s.data, c ∉ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', 'A', 'B', 'C', 'D', 'E', 'F']) :
  hex_to_dec s = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval hex_to_dec "1"

/-
info: 10
-/
-- #guard_msgs in
-- #eval hex_to_dec "a"

/-
info: 16
-/
-- #guard_msgs in
-- #eval hex_to_dec "10"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible