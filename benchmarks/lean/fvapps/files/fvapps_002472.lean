-- <vc-preamble>
def ℂ := Float × Float

def mkComplex (r i : Float) : ℂ := (r, i)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def magnitude : ℂ → Float :=
sorry

def phase : ℂ → Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_polar_coords_zero :
  let z := mkComplex 0 0
  magnitude z = 0 ∧ phase z = 0 := by
sorry

theorem get_polar_coords_real_positive :
  let z := mkComplex 1 0
  magnitude z = 1 ∧ phase z = 0 := by
sorry

theorem get_polar_coords_real_negative :
  let z := mkComplex (-1) 0
  magnitude z = 1 ∧ phase z = 3.141592653589793 := by
sorry

theorem get_polar_coords_complex :
  let z := mkComplex 1 2
  Float.abs (magnitude z - 2.23606797749979) < 1e-10 ∧
  Float.abs (phase z - 1.1071487177940904) < 1e-10 := by
sorry
-- </vc-theorems>