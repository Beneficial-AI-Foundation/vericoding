-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diff (p : List Int) : List Int := sorry

theorem diff_length (p : List Int) :
  (diff p).length = max 0 (p.length - 1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diff_constant (p : List Int) :
  p.length = 1 → diff p = [] := sorry

theorem diff_linear (p : List Int) :
  p.length = 2 → diff p = [p.get! 0] := sorry

theorem double_diff_quadratic (p : List Int) :
  p.length = 3 → diff (diff p) = [2 * p.get! 0] := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval diff []

/-
info: [1]
-/
-- #guard_msgs in
-- #eval diff [1, 1]

/-
info: [6, 2, 0]
-/
-- #guard_msgs in
-- #eval diff [2, 1, 0, 0]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded