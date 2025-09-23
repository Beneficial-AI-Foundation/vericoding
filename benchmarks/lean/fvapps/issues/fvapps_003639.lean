-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest (s1 s2 : List Char) : List Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longest_unique_chars {s1 s2 : List Char} :
  let result := longest s1 s2
  ∀ x ∈ result, ∀ y ∈ result, x = y → result.indexOf x = result.indexOf y :=
  sorry

theorem longest_sorted {s1 s2 : List Char} :
  let result := longest s1 s2
  ∀ i j, i < j → j < result.length → result[i]! ≤ result[j]! :=
  sorry

theorem longest_chars_from_inputs {s1 s2 : List Char} :
  let result := longest s1 s2
  ∀ c ∈ result, c ∈ s1 ++ s2 :=
  sorry

theorem longest_contains_all_unique_inputs {s1 s2 : List Char} :
  let result := longest s1 s2
  ∀ c ∈ s1 ++ s2, c ∈ result :=
  sorry

theorem longest_identity {s : List Char} :
  longest s s = longest s [] ∧ longest s [] = longest [] s :=
  sorry

theorem longest_commutative {s1 s2 : List Char} :
  longest s1 s2 = longest s2 s1 :=
  sorry

/-
info: 'abcdefklmopqwxy'
-/
-- #guard_msgs in
-- #eval longest "xyaabbbccccdefww" "xxxxyyyyabklmopq"

/-
info: 'aehrsty'
-/
-- #guard_msgs in
-- #eval longest "aretheyhere" "yestheyarehere"

/-
info: 'adefghklmnorstu'
-/
-- #guard_msgs in
-- #eval longest "lordsofthefallen" "gamekult"
-- </vc-theorems>