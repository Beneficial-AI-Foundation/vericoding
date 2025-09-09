-- <vc-helpers>
-- </vc-helpers>

def xp_to_target_lvl (current_xp : Int) (target_lvl : Int) : String ⊕ Int :=
  sorry

theorem xp_to_target_lvl_invalid_input
  (current_xp : Int)
  (target_lvl : Int)
  (h1 : target_lvl ≤ 0 ∨ target_lvl ≥ 171 ∨ current_xp < 0) :
  xp_to_target_lvl current_xp target_lvl = Sum.inl "Input is invalid." :=
  sorry

theorem xp_to_target_lvl_result_positive
  (current_xp : Int)
  (target_lvl : Int)
  (h1 : target_lvl > 0)
  (h2 : target_lvl < 171)
  (h3 : current_xp ≥ 0)
  (h4 : ∃ n : Int, xp_to_target_lvl current_xp target_lvl = Sum.inr n) :
  ∃ n : Int, xp_to_target_lvl current_xp target_lvl = Sum.inr n ∧ n > 0 :=
  sorry

theorem xp_progression_monotonic
  (target_lvl : Int)
  (h1 : target_lvl > 1)
  (h2 : target_lvl < 171)
  (h3 : ∃ x y : Int, 
    xp_to_target_lvl 0 (target_lvl - 1) = Sum.inr x ∧
    xp_to_target_lvl 0 target_lvl = Sum.inr y) :
  ∃ x y : Int,
    xp_to_target_lvl 0 (target_lvl - 1) = Sum.inr x ∧
    xp_to_target_lvl 0 target_lvl = Sum.inr y ∧
    y > x :=
  sorry

/-
info: 1808
-/
-- #guard_msgs in
-- #eval xp_to_target_lvl 0 5

/-
info: 'Input is invalid.'
-/
-- #guard_msgs in
-- #eval xp_to_target_lvl 31428 "47"

/-
info: 'You have already reached level 4.'
-/
-- #guard_msgs in
-- #eval xp_to_target_lvl 2017 4

-- Apps difficulty: introductory
-- Assurance level: unguarded