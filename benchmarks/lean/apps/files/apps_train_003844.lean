-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toUnderScore (s : String) : String := sorry

-- Property 1: All characters in result (except underscores) match original string
-- </vc-definitions>

-- <vc-theorems>
theorem chars_preserved (s : String) : 
  (toUnderScore s).replace "_" "" = s.replace "_" "" := sorry

-- Property 2: Strings with only underscores are unchanged

theorem underscore_only_strings (s : String) : 
  (∀ c ∈ s.data, c = '_') → toUnderScore s = s := sorry

-- Property 3: Function is idempotent

theorem underscore_idempotent (s : String) :
  toUnderScore (toUnderScore s) = toUnderScore s := sorry

/-
info: 'This_Is_A_Unit_Test'
-/
-- #guard_msgs in
-- #eval toUnderScore "ThisIsAUnitTest"

/-
info: 'Calculate_15_Plus_5_Equals_20'
-/
-- #guard_msgs in
-- #eval toUnderScore "Calculate15Plus5Equals20"

/-
info: '_Underscore_Marked_Test_Name_'
-/
-- #guard_msgs in
-- #eval toUnderScore "_UnderscoreMarked_Test_Name_"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded