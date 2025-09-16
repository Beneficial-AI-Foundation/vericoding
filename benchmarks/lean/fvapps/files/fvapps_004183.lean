-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compareVersions (v1 : String) (v2 : String) : Bool :=
  sorry

variable (v v1 v2 v3 : String)

-- Self equality
-- </vc-definitions>

-- <vc-theorems>
theorem compare_versions_self_equality :
  compareVersions v v = true := by
  sorry

-- Transitivity 

theorem compare_versions_transitive : 
  compareVersions v1 v2 = true → compareVersions v2 v3 = true → compareVersions v1 v3 = true := by
  sorry

-- Padding zeros

theorem compare_versions_padding :
  compareVersions v (v ++ ".0") = true ∧ compareVersions (v ++ ".0") v = true := by
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval compare_versions "11" "10"

/-
info: True
-/
-- #guard_msgs in
-- #eval compare_versions "10.4.6" "10.4"

/-
info: False
-/
-- #guard_msgs in
-- #eval compare_versions "10.4" "10.10"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded