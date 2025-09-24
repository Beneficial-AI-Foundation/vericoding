-- <vc-preamble>
def flipDir : Direction → Direction 
  | Direction.N => Direction.S
  | Direction.S => Direction.N
  | Direction.E => Direction.W
  | Direction.W => Direction.E

def flipPath (path : List Direction) : List Direction :=
  path.map flipDir

def opposite (d : Direction) : Direction :=
  flipDir d
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solvable (p1 p2 : List Direction) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solvable_with_self_inverse (path : List Direction) :
  ¬(solvable path (flipPath path)) := by sorry

theorem solvable_symmetry (path : List Direction) :
  let rev := (path.reverse.map opposite)
  solvable path rev = solvable rev path := by sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval solvable "NNESWW" "SWSWSW"

/-
info: False
-/
-- #guard_msgs in
-- #eval solvable "NN" "SS"

/-
info: False
-/
-- #guard_msgs in
-- #eval solvable "ES" "NW"
-- </vc-theorems>