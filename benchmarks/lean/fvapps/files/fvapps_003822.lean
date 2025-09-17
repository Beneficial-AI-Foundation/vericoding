-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def search_substr (text pattern : String) (case_sensitive : Bool := true) : Nat := sorry

theorem empty_inputs_return_zero (text pattern : String) : 
  text = "" ∨ pattern = "" → 
  search_substr text pattern = 0 ∧ 
  search_substr text pattern false = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem substring_length_property (text pattern : String) : 
  text ≠ "" → pattern ≠ "" →
  (search_substr text pattern false) * (pattern.length) ≤ text.length := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval search_substr "aa_bb_cc_dd_bb_e" "bb"

/-
info: 2
-/
-- #guard_msgs in
-- #eval search_substr "aaa" "aa"

/-
info: 1
-/
-- #guard_msgs in
-- #eval search_substr "aaa" "aa" False

/-
info: 0
-/
-- #guard_msgs in
-- #eval search_substr "abc" ""
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible