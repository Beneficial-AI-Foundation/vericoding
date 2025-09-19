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
-- </vc-theorems>