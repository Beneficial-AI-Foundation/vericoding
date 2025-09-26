-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def name_score (name : String) (alpha : Option (Lean.HashMap String Int) := none) : 
  Lean.HashMap String Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem name_score_returns_dict_with_name (name : String) :
  let result := name_score name
  result.size = 1 ∧ result.contains name := sorry

theorem name_score_with_custom_alpha (name : String) (alpha : Lean.HashMap String Int) :
  let result := name_score name (some alpha)
  result.size = 1 ∧ result.contains name := sorry

theorem name_score_case_insensitive (name : String) : 
  (name_score name.toLower).find! name.toLower = 
  (name_score name.toUpper).find! name.toUpper := sorry

theorem name_score_nonnegative (name : String) :
  (name_score name).find! name ≥ 0 := sorry

theorem name_score_additive (name1 name2 : String) :
  (name_score (name1 ++ name2)).find! (name1 ++ name2) = 
  (name_score name1).find! name1 + (name_score name2).find! name2 := sorry

/-
info: {'MARY': 13}
-/
-- #guard_msgs in
-- #eval name_score "MARY"

/-
info: {'Mary Jane': 20}
-/
-- #guard_msgs in
-- #eval name_score "Mary Jane"

/-
info: {'CAB': 3}
-/
-- #guard_msgs in
-- #eval name_score "CAB" {"ABC": 1, "DEF": 2, "GHIJKLMNOPQRSTUVWXYZ": 0}
-- </vc-theorems>