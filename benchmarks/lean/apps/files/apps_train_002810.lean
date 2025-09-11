-- <vc-preamble>
def dropzone (fire : List Int) (dropzones : List (List Int)) : List Int := sorry

def hypot (x y : Int) : Float := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isClosestToFire (point fire : List Int) (points : List (List Int)) : Bool := sorry

def isClosestToOrigin (point fire : List Int) (points : List (List Int)) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dropzone_is_valid_point (fire : List Int) (dropzones : List (List Int)) :
  fire.length = 2 → dropzones.length > 0 → dropzone fire dropzones ∈ dropzones := sorry

theorem dropzone_is_closest_to_fire (fire : List Int) (dropzones : List (List Int)) :
  fire.length = 2 → dropzones.length > 0 → 
  isClosestToFire (dropzone fire dropzones) fire dropzones = true := sorry

theorem dropzone_is_closest_to_origin (fire : List Int) (dropzones : List (List Int)) :
  fire.length = 2 → dropzones.length > 0 →
  isClosestToOrigin (dropzone fire dropzones) fire dropzones = true := sorry

theorem single_dropzone (fire dropzone_single : List Int) :
  fire.length = 2 → dropzone_single.length = 2 →
  dropzone fire [dropzone_single] = dropzone_single := sorry

/-
info: [7, 9]
-/
-- #guard_msgs in
-- #eval dropzone [6, 8] [[3, 2], [6, 1], [7, 9]]

/-
info: [5, 5]
-/
-- #guard_msgs in
-- #eval dropzone [9, 2] [[1, 4], [9, 9], [5, 5]]

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval dropzone [1, 1] [[0, 1], [1, 0], [2, 2]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded