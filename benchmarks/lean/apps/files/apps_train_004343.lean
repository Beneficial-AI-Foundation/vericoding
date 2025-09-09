-- <vc-helpers>
-- </vc-helpers>

def invert (xs : List Int) : List Int := sorry

def abs (n : Int) : Int :=
  if n ≥ 0 then n else -n

theorem invert_length (xs : List Int) :
  (invert xs).length = xs.length := sorry

theorem invert_involution (xs : List Int) :
  invert (invert xs) = xs := sorry

theorem invert_empty : 
  invert [] = [] := sorry

/-
info: [-1, -2, -3, -4, -5]
-/
-- #guard_msgs in
-- #eval invert [1, 2, 3, 4, 5]

/-
info: [-1, 2, -3, 4, -5]
-/
-- #guard_msgs in
-- #eval invert [1, -2, 3, -4, 5]

/-
info: []
-/
-- #guard_msgs in
-- #eval invert []

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible