-- <vc-helpers>
-- </vc-helpers>

def leo (oscar : Int) : String := sorry

theorem leo_is_string (oscar : Int) :
  ∃ s : String, leo oscar = s := sorry

theorem leo_before_wolf (oscar : Int) (h: oscar ≤ 85) :
  leo oscar = "When will you give Leo an Oscar?" := sorry

theorem leo_after_win (oscar : Int) (h: oscar ≥ 89) :
  leo oscar = "Leo got one already!" := sorry

theorem leo_edge_cases :
  leo 86 = "Not even for Wolf of wallstreet?!" ∧
  leo 88 = "Leo finally won the oscar! Leo is happy" := sorry

/-
info: 'Leo finally won the oscar! Leo is happy'
-/
-- #guard_msgs in
-- #eval leo 88

/-
info: 'When will you give Leo an Oscar?'
-/
-- #guard_msgs in
-- #eval leo 87

/-
info: 'Not even for Wolf of wallstreet?!'
-/
-- #guard_msgs in
-- #eval leo 86

-- Apps difficulty: introductory
-- Assurance level: unguarded