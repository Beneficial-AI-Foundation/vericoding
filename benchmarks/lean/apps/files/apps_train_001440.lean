def find_min_bad_luck (strings : List String) : Nat := sorry

theorem find_min_bad_luck_non_negative (strings : List String) :
  find_min_bad_luck strings ≥ 0 := sorry

-- <vc-helpers>
-- </vc-helpers>

def countChar (c : Char) (s : String) : Nat := sorry

theorem find_min_bad_luck_leq_min_len (strings : List String) : 
  strings ≠ [] → find_min_bad_luck strings ≤ List.foldr (fun s acc => min s.length acc) (strings[0]!.length) strings.tail := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_min_bad_luck ["ab", "ba"]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_min_bad_luck ["aa", "bb"]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_bad_luck ["aabb", "abab", "baab"]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible