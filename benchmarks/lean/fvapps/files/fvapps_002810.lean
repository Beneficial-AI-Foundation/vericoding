-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dropzone (fire : List Int) (dropzones : List (List Int)) : List Int :=
sorry

def hypot (x y : Int) : Float :=
sorry

def isClosestToFire (point fire : List Int) (points : List (List Int)) : Bool :=
sorry

def isClosestToOrigin (point fire : List Int) (points : List (List Int)) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dropzone_is_valid_point (fire : List Int) (dropzones : List (List Int)) :
  fire.length = 2 → dropzones.length > 0 → dropzone fire dropzones ∈ dropzones :=
sorry

theorem dropzone_is_closest_to_fire (fire : List Int) (dropzones : List (List Int)) :
  fire.length = 2 → dropzones.length > 0 →
  isClosestToFire (dropzone fire dropzones) fire dropzones = true :=
sorry

theorem dropzone_is_closest_to_origin (fire : List Int) (dropzones : List (List Int)) :
  fire.length = 2 → dropzones.length > 0 →
  isClosestToOrigin (dropzone fire dropzones) fire dropzones = true :=
sorry

theorem single_dropzone (fire dropzone_single : List Int) :
  fire.length = 2 → dropzone_single.length = 2 →
  dropzone fire [dropzone_single] = dropzone_single :=
sorry
-- </vc-theorems>