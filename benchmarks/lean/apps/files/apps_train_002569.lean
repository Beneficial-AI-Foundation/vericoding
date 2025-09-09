-- <vc-helpers>
-- </vc-helpers>

def create_anagram (s t : String) : Nat :=
  sorry

theorem anagram_non_negative (s t : String) :
  create_anagram s t ≥ 0 :=
  sorry

theorem anagram_self (s : String) :
  create_anagram s s = 0 :=
  sorry

theorem anagram_empty :
  create_anagram "" "" = 0 :=
  sorry

theorem anagram_length_bound (s t : String) :
  create_anagram s t ≤ String.length s :=
  sorry

theorem anagram_repeated (s : String) :
  create_anagram s (s ++ s) = 0 ∧
  create_anagram (s ++ s) s = String.length s :=
  sorry

theorem anagram_permutation (s : String) :
  -- simplified condition since we can't sort without Mathlib
  create_anagram s s = 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval create_anagram "AABAA" "BBAAA"

/-
info: 4
-/
-- #guard_msgs in
-- #eval create_anagram "OVGHK" "RPGUC"

/-
info: 1
-/
-- #guard_msgs in
-- #eval create_anagram "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAB" "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAC"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible