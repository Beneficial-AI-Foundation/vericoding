-- <vc-helpers>
-- </vc-helpers>

def alt_or : List Bool → Option Bool
  | [] => none
  | l => some (sorry)

theorem alt_or_empty : alt_or [] = none := by sorry

theorem alt_or_nonempty {l : List Bool} (h : l ≠ []) :
  ∃ b, alt_or l = some b := by sorry

theorem alt_or_eq_any {l : List Bool} (h : l ≠ []) :
  ∀ b, alt_or l = some b → b = l.any id := by sorry

theorem alt_or_type {l : List Bool} (h : l ≠ []) :
  (alt_or l).isSome := by sorry

/-
info: None
-/
-- #guard_msgs in
-- #eval alt_or []

/-
info: False
-/
-- #guard_msgs in
-- #eval alt_or [False]

/-
info: True
-/
-- #guard_msgs in
-- #eval alt_or [False, True, False]

-- Apps difficulty: introductory
-- Assurance level: unguarded