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

/- The types function is reflexive -/

theorem types_preserves_equality {α : Type} (x : α) :
  types x = types x := sorry

/-
info: 'int'
-/
-- #guard_msgs in
-- #eval types 23

/-
info: 'float'
-/
-- #guard_msgs in
-- #eval types 2.3

/-
info: 'str'
-/
-- #guard_msgs in
-- #eval types "Hello"

/-
info: 'bool'
-/
-- #guard_msgs in
-- #eval types True
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded