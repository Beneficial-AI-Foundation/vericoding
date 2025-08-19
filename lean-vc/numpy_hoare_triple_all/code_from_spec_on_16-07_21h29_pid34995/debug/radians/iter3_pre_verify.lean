import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.radians: Convert angles from degrees to radians.

    Converts angles from degrees to radians element-wise.
    The conversion formula is: radians = degrees * π / 180

    Parameters:
    - x: Input array in degrees

    Returns:
    - y: Array of the same shape as x, containing the corresponding radian values
-/
def numpy_radians {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map (fun deg => deg * 3.141592653589793 / 180))

/-- Specification: numpy.radians converts each element from degrees to radians.

    Precondition: True (no special preconditions for degree to radian conversion)
    Postcondition: For all indices i, result[i] = x[i] * π / 180

    Mathematical properties verified:
    - Linear conversion: radians = degrees * (π / 180)
    - 0 degrees = 0 radians
    - 180 degrees = π radians  
    - 360 degrees = 2π radians
    - Maintains array shape and element-wise mapping
    - Preserves the relationship between angle measures
-/
theorem numpy_radians_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_radians x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x.get i * 3.141592653589793 / 180 ∧
                 -- Specific cases that validate the conversion
                 (x.get i = 0 → result.get i = 0) ∧  -- 0 degrees = 0 radians
                 (x.get i = 180 → result.get i > 3.14 ∧ result.get i < 3.15) ∧  -- 180 degrees ≈ π radians
                 (x.get i = 360 → result.get i > 6.28 ∧ result.get i < 6.29)    -- 360 degrees ≈ π radians
                ⌝⦄ := by
  unfold numpy_radians
  apply Triple.pure
  intro i
  constructor
  · simp [Vector.get, Vector.map]
  · constructor
    · intro h_zero
      simp [Vector.get, Vector.map, h_zero]
    · constructor
      · intro h_180
        simp [Vector.get, Vector.map, h_180]
        ring
      · intro h_360
        simp [Vector.get, Vector.map, h_360]
        ring