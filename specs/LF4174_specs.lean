-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compare (v1 v2 : String) : Int := sorry

@[simp] theorem compare_symmetry {v1 v2 : String} :
  VersionCompare.compare v1 v2 = -(VersionCompare.compare v2 v1) := sorry

@[simp] theorem compare_identity {v : String} :
  VersionCompare.compare v v = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trailing_zeros_ignored {v : String} :
  VersionCompare.compare v (v ++ ".0") = 0 ∧ 
  VersionCompare.compare v (v ++ ".0.0") = 0 := sorry

theorem compare_transitivity {v1 v2 v3 : String} :
  VersionCompare.compare v1 v2 ≥ 0 → 
  VersionCompare.compare v2 v3 ≥ 0 → 
  VersionCompare.compare v1 v3 ≥ 0 := sorry

theorem compare_returns_valid {v1 v2 : String} :
  VersionCompare.compare v1 v2 = -1 ∨ 
  VersionCompare.compare v1 v2 = 0 ∨ 
  VersionCompare.compare v1 v2 = 1 := sorry

end VersionCompare

/-
info: -1
-/
-- #guard_msgs in
-- #eval compare "1" "2"

/-
info: 0
-/
-- #guard_msgs in
-- #eval compare "3" "3.0.0"

/-
info: 0
-/
-- #guard_msgs in
-- #eval compare "1.2.3.4" "1.2.3.4"

/-
info: 1
-/
-- #guard_msgs in
-- #eval compare "1.2.1" "1.2.0"

/-
info: -1
-/
-- #guard_msgs in
-- #eval compare "3.0.1" "3.1"
-- </vc-theorems>