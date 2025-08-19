/-
NumPy Constants Module for Lean 4

This module consolidates all NumPy mathematical constants in Lean.
Each section contains both the implementation and specification
for a specific constant.
-/

/- ============================================================================
   Euler's constant (e)
   ============================================================================
   Euler's constant, base of natural logarithms, Napier's constant.
   e = 2.71828182845904523536028747135266249775724709369995...
-/

-- Implementation
def numpy_e : Float := 2.71828182845904523536028747135266249775724709369995

-- Specification
def numpy_e_spec : {x : Float // x = numpy_e} := ⟨numpy_e, rfl⟩


/- ============================================================================
   Euler-Mascheroni constant (gamma)
   ============================================================================
   γ = 0.5772156649015328606065120900824024310421...
-/

-- Implementation
def numpy_euler_gamma : Float := 0.577215664901532860606512090082402431042

-- Specification
def numpy_euler_gamma_spec : {x : Float // x = numpy_euler_gamma} := ⟨numpy_euler_gamma, rfl⟩


/- ============================================================================
   Infinity
   ============================================================================
   IEEE 754 floating point representation of (positive) infinity.
-/

-- Implementation
def numpy_inf (_ : Unit) : Float :=
  (1 : Float) / 0

-- Specification
def numpy_inf_spec (_ : Unit) : {x : Float // x = (1 : Float) / 0} :=
  ⟨(1 : Float) / 0, rfl⟩


/- ============================================================================
   Not a Number (NaN)
   ============================================================================
   IEEE 754 floating point representation of Not a Number (NaN).
-/

-- Implementation
def numpy_nan (_ : Unit) : Float :=
  (0 : Float) / 0

-- Specification
def numpy_nan_spec (_ : Unit) : {x : Float // x = (0 : Float) / 0} :=
  ⟨(0 : Float) / 0, rfl⟩