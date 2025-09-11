-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_non_negative (s : String) : 
  solve s ≥ 0 :=
sorry

theorem result_is_within_modulo (s : String) :
  solve s < 1000000007 :=
sorry

theorem single_char_properties (s : String) (c : Char) (h : s = String.mk [c]) :
  solve s = (Char.toNat 'Z' - Char.toNat c) :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve "XYZ"

/-
info: 16174
-/
-- #guard_msgs in
-- #eval solve "ABC"

/-
info: 25
-/
-- #guard_msgs in
-- #eval solve "ZAZ"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible