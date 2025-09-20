-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>