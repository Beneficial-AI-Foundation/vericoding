-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def types (x : α) : String := sorry

/- For any given value, the types function returns a string that should be consistent -/
-- </vc-definitions>

-- <vc-theorems>
theorem types_matches_type_name {α : Type} (x : α) :
  types x = types x := sorry
-- </vc-theorems>