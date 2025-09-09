-- <vc-helpers>
-- </vc-helpers>

def ride (s1 s2 : String) : String :=
  sorry

theorem ride_reflexive {s1 : String} :
  ride s1 s1 = "GO" := by
  sorry

theorem ride_symmetric {s1 s2 : String} :  
  ride s1 s2 = ride s2 s1 := by
  sorry

theorem ride_transitive {s1 s2 s3 : String} :
  ride s1 s2 = "GO" → ride s2 s3 = "GO" → ride s1 s3 = "GO" := by
  sorry

theorem ride_output_format {s1 s2 : String} :
  ride s1 s2 = "GO" ∨ ride s1 s2 = "STAY" := by
  sorry

/-
info: 'GO'
-/
-- #guard_msgs in
-- #eval ride "COMETQ" "HVNGAT"

/-
info: 'STAY'
-/
-- #guard_msgs in
-- #eval ride "ABSTAR" "USACO"

/-
info: 'GO'
-/
-- #guard_msgs in
-- #eval ride "USACO" "USACO"

-- Apps difficulty: introductory
-- Assurance level: unguarded