import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "NPY_PI_4",
  "category": "C API Mathematical constants",
  "description": "Pi divided by 4",
  "doc": "π/4 = 0.785398163397448309615660845819875721",
  "code": "#define NPY_PI_4 0.785398163397448309615660845819875721"
}
-/

open Std.Do

/-- NPY_PI_4: Mathematical constant representing π/4.
    
    This constant provides the value of pi divided by 4, which is commonly used in
    trigonometric calculations, particularly for 45-degree angle computations.
    
    Value: π/4 ≈ 0.785398163397448309615660845819875721
-/
def NPY_PI_4 : Id Float :=
  pure 0.785398163397448309615660845819875721

/-- Specification: NPY_PI_4 returns the mathematical constant π/4.
    
    Precondition: True (no preconditions for accessing a constant)
    Postcondition: The result equals π/4, which is approximately 0.7853981633974483
    
    Mathematical properties:
    - NPY_PI_4 = π/4
    - NPY_PI_4 = arctan(1)  
    - sin(NPY_PI_4) = cos(NPY_PI_4) = √2/2
    - tan(NPY_PI_4) = 1
    - 4 * NPY_PI_4 = π
-/
theorem NPY_PI_4_spec :
    ⦃⌜True⌝⦄
    NPY_PI_4
    ⦃⇓result => ⌜result = 0.785398163397448309615660845819875721 ∧
                  result > 0.785 ∧ result < 0.786 ∧
                  result * 4 > 3.141 ∧ result * 4 < 3.142⌝⦄ := by
  simp [NPY_PI_4]
  norm_num