-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fish (input : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fish_minimum (nums : String) :
  fish nums ≥ 1 := by
  sorry

theorem fish_maximum (nums : String) :
  fish nums ≤ String.length nums + 1 := by
  sorry

theorem fish_monotonic_identical_digits (s : String) (h: ∀ (i j : Nat), i < s.length → j < s.length → s.data[i]! = s.data[j]!) :
  fish s ≤ (String.length s + 3) / 4 + 1 := by
  sorry

theorem fish_sorted_same_result (s1 s2 : String) (h: s1.data = s2.data) :
  fish s1 = fish s2 := by
  sorry

theorem fish_empty_string :
  fish "" = 1 := by
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval fish ""

/-
info: 2
-/
-- #guard_msgs in
-- #eval fish "1111"

/-
info: 4
-/
-- #guard_msgs in
-- #eval fish "111122223333"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded