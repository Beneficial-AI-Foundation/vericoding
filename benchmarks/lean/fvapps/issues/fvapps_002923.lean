-- <vc-preamble>
def solve : List String → List String := sorry

def extractDirections (commands : List String) : List Direction := sorry

def extractRoads (commands : List String) : List String := sorry

def isLeftOrRight (d : Direction) : Bool :=
  match d with
  | Direction.Left => true
  | Direction.Right => true
  | _ => false
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def allLeftOrRight (directions : List Direction) : Bool := 
  directions.all isLeftOrRight
-- </vc-definitions>

-- <vc-theorems>
theorem solution_preserves_length (commands : List String) :
  List.length (solve commands) = List.length commands := sorry

theorem solution_preserves_roads (commands : List String) :
  extractRoads (solve commands) = extractRoads commands := sorry

theorem first_direction_valid (commands : List String) :
  commands ≠ [] →
  let result := solve commands
  let firstDir := extractDirections result |>.head!
  firstDir = Direction.Begin ∨ firstDir = Direction.Left ∨ firstDir = Direction.Right := sorry

theorem directions_alternate (commands : List String) :
  List.length commands > 1 →
  allLeftOrRight (List.tail! (extractDirections (solve commands))) := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval solve ["Begin on 3rd Blvd", "Right on First Road", "Left on 9th Dr"]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval solve ["Begin on Road A", "Right on Road B", "Right on Road C", "Left on Road D"]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval solve ["Begin on Road A"]
-- </vc-theorems>