-- <vc-preamble>
def abs (x : Float) : Float := sorry

def IsFinite (x : Float) : Prop := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_mirror_position (x1 y1 x2 y2 : Float) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_mirror_position_basic_properties 
  (x1 y1 x2 y2 : Float)
  (h1 : abs (x2 - x1) > 1e-6)  -- Not vertical
  (h2 : abs (y2 + y1) > 1e-6)  -- Avoid division by zero
  : IsFinite (find_mirror_position x1 y1 x2 y2) := by
  sorry
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded