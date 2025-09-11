-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_atoms (s : String) : String := sorry

theorem base_case_h2o :
  count_atoms "H2O" = "H2O" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem base_case_mgoh2 :
  count_atoms "Mg(OH)2" = "H2MgO2" := sorry

theorem base_case_k4on :
  count_atoms "K4(ON(SO3)2)2" = "K4N2O14S4" := sorry

theorem empty_string :
  count_atoms "" = "" := sorry

theorem single_na :
  count_atoms "Na" = "Na" := sorry

theorem single_h :
  count_atoms "H" = "H" := sorry

/-
info: 'H2O'
-/
-- #guard_msgs in
-- #eval count_atoms "H2O"

/-
info: 'H2MgO2'
-/
-- #guard_msgs in
-- #eval count_atoms "Mg(OH)2"

/-
info: 'K4N2O14S4'
-/
-- #guard_msgs in
-- #eval count_atoms "K4(ON(SO3)2)2"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded