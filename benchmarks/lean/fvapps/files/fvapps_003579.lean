-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_1D (x y : Nat) (size : Nat × Nat) : Nat :=
  sorry

def to_2D (idx : Nat) (size : Nat × Nat) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem to_1D_to_2D_roundtrip (x y width height : Nat) (h1 : width > 0) (h2 : height > 0) :
  let size := (width, height)
  let x' := x % width
  let y' := y % height
  let (x2, y2) := to_2D (to_1D x' y' size) size
  x2 = x' ∧ y2 = y' :=
sorry

theorem to_2D_to_1D_roundtrip (idx width height : Nat) (h1 : width > 0) (h2 : height > 0) :
  let size := (width, height)
  let idx' := idx % (width * height)
  let (x, y) := to_2D idx' size
  to_1D x y size = idx' :=
sorry

theorem to_1D_bounds (x y width height : Nat) (h1 : width > 0) (h2 : height > 0) :
  let size := (width, height)
  let x' := x % width
  let y' := y % height
  let idx := to_1D x' y' size
  0 ≤ idx ∧ idx < width * height :=
sorry
-- </vc-theorems>