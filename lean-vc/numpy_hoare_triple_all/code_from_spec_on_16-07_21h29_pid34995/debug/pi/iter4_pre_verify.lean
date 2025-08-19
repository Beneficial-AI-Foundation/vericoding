import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.pi",
  "category": "Mathematical constants",
  "description": "Ratio of a circle's circumference to its diameter",
  "url": "https://numpy.org/doc/stable/reference/constants.html#numpy.pi",
  "doc": "pi = 3.1415926535897932384626433...\n\nPi is the ratio of a circle's circumference to its diameter. It is a mathematical constant that appears in many formulas in mathematics and physics.",
  "code": "#define NPY_PI 3.141592653589793238462643383279502884\n# Exposed in Python as:\nnumpy.pi = 3.141592653589793"
}
-/

open Std.Do

/-- The mathematical constant pi (π), approximately 3.14159... -/
def pi : Id Float :=
  pure 3.141592653589793

-- LLM HELPER
lemma pi_properties : 
  let result := 3.141592653589793
  3.14159 < result ∧ result < 3.14160 ∧
  3 < result ∧ result < 4 ∧
  9.869 < result * result ∧ result * result < 9.870 ∧
  6.283 < 2 * result ∧ 2 * result < 6.284 ∧
  1.570 < result / 2 ∧ result / 2 < 1.571 ∧
  0.785 < result / 4 ∧ result / 4 < 0.786 := by
  simp [Float.lt_def]
  norm_num

/-- Specification: pi represents the ratio of a circle's circumference to its diameter,
    and satisfies key mathematical properties -/
theorem pi_spec :
    ⦃⌜True⌝⦄
    pi
    ⦃⇓result => ⌜
      -- Pi is approximately 3.14159...
      3.14159 < result ∧ result < 3.14160 ∧
      -- Pi is between 3 and 4 (basic sanity check)
      3 < result ∧ result < 4 ∧
      -- Pi squared is approximately 9.8696... (useful for area calculations)
      9.869 < result * result ∧ result * result < 9.870 ∧
      -- 2*pi is approximately 6.28318... (useful for full circle calculations)
      6.283 < 2 * result ∧ 2 * result < 6.284 ∧
      -- pi/2 is approximately 1.5708... (useful for quarter circle calculations)
      1.570 < result / 2 ∧ result / 2 < 1.571 ∧
      -- pi/4 is approximately 0.7854... (useful for eighth circle calculations)
      0.785 < result / 4 ∧ result / 4 < 0.786
    ⌝⦄ := by
  simp [pi]
  apply Triple.Pure.mk
  exact pi_properties