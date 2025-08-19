import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.False_",
  "category": "Boolean constants",
  "description": "NumPy boolean scalar representing False",
  "url": "https://numpy.org/doc/stable/reference/arrays.scalars.html",
  "doc": "NumPy's boolean type. Character code: '?'. Alias for numpy.bool_.\n\nComparison operations in NumPy return numpy.True_ or numpy.False_ instead of Python's built-in True or False.",
  "code": "# NumPy boolean scalar\nnumpy.False_ = numpy.bool_(False)"
}
-/

open Std.Do

/-- NumPy's boolean False value, used in comparison operations and boolean arrays -/
def False_ : Id Bool :=
  pure false

/-- Specification: False_ represents the boolean false value with properties:
    1. It equals false
    2. It is the identity for logical OR
    3. It is the absorbing element for logical AND
    4. It is the negation of True_ -/
theorem False__spec :
    ⦃⌜True⌝⦄
    False_
    ⦃⇓result => ⌜result = false ∧ 
                 (∀ b : Bool, result || b = b) ∧
                 (∀ b : Bool, result && b = false) ∧
                 result = !true⌝⦄ := by
  rw [False_]
  apply pure_spec
  simp [Bool.false_or, Bool.false_and]