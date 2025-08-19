import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.float_power",
  "description": "First array elements raised to powers from second array, element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.float_power.html",
  "doc": "First array elements raised to powers from second array, element-wise.\n\nRaise each base in x1 to the positionally-corresponding power in x2. This differs from the power function in that integers, float16, and float32 are promoted to floats with a minimum precision of float64.",
  "code": "# Universal function (ufunc) implemented in C\n# First array elements raised to powers from second array, element-wise\n# This function is implemented as a compiled ufunc in NumPy's C extension modules.\n# It provides optimized element-wise operations with support for:\n# - Broadcasting\n# - Type casting and promotion  \n# - Output array allocation\n# - Where parameter for conditional operation\n# - Vectorized execution using SIMD instructions where available"
}
-/

/-- Element-wise power operation with float promotion. 
    Raises each element of the base vector to the corresponding power in the exponent vector.
    All values are promoted to Float (minimum precision of Float64). -/
def float_power {n : Nat} (base : Vector Float n) (exponent : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.ofFn (fun i => (base.get i) ^ (exponent.get i)))

/-- Specification: float_power computes element-wise exponentiation with appropriate constraints.
    - For positive bases: result is always well-defined
    - For zero bases: only non-negative exponents are valid
    - For negative bases: only integer exponents are mathematically valid (though NumPy allows all)
    - The result preserves the mathematical power relationship element-wise -/
theorem float_power_spec {n : Nat} (base : Vector Float n) (exponent : Vector Float n) 
    (h_valid : ∀ i : Fin n, (base.get i > 0) ∨ (base.get i = 0 ∧ exponent.get i ≥ 0)) :
    ⦃⌜∀ i : Fin n, (base.get i > 0) ∨ (base.get i = 0 ∧ exponent.get i ≥ 0)⌝⦄
    float_power base exponent
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (base.get i) ^ (exponent.get i)⌝⦄ := by
  simp [float_power]
  apply wp_pure
  intro i
  simp [Vector.get_ofFn]