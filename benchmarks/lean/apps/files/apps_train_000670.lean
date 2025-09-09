-- <vc-helpers>
-- </vc-helpers>

def canZebrasSpatAtEachOther (positions : List (Int × Int)) : Bool := sorry

theorem canZebrasSpatAtEachOther_returns_bool 
  (positions : List (Int × Int))
  (h1 : positions ≠ []) : 
  canZebrasSpatAtEachOther positions = true ∨ 
  canZebrasSpatAtEachOther positions = false := sorry

theorem reciprocal_spitting
  {positions : List (Int × Int)}
  {pos1 pos2 dist1 dist2 : Int}
  (h1 : positions = [(pos1, dist1), (pos2, dist2)])
  (h2 : pos1 ≠ pos2)
  (h3 : pos1 + dist1 = pos2)
  (h4 : pos2 + dist2 = pos1) :
  canZebrasSpatAtEachOther positions = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_zebras_spit_at_each_other [[0, 1], [1, -1]]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_zebras_spit_at_each_other [[0, 1], [2, -1]]

/-
info: True
-/
-- #guard_msgs in
-- #eval can_zebras_spit_at_each_other [[0, 2], [1, 1], [2, -2]]

-- Apps difficulty: interview
-- Assurance level: unguarded