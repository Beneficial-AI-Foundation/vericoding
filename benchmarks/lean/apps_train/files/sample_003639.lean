/-
Take 2 strings `s1` and `s2` including only letters from `a`to `z`.
Return a new **sorted** string, the longest possible, containing distinct letters,
- each taken only once - coming from s1 or s2.

# Examples:
```
a = "xyaabbbccccdefww"
b = "xxxxyyyyabklmopq"
longest(a, b) -> "abcdefklmopqwxy"

a = "abcdefghijklmnopqrstuvwxyz"
longest(a, a) -> "abcdefghijklmnopqrstuvwxyz"
```
-/

-- <vc-helpers>
-- </vc-helpers>

def longest (s1 s2 : List Char) : List Char :=
  sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded