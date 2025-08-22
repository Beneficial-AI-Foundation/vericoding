
## Specification Formats

### 1. One Theorem Format (`one_thm/`)


**Structure:**
- Single namespace per file
- One main function definition with `sorry`
- One comprehensive theorem that combines all specifications; the missing proof is marked with `sorry`

**Example:**
```lean
namespace NpAbs

def absInt (x : Int) : Int := if x < 0 then -x else x

def abs {n : Nat} (a : Vector Int n) : Vector Int n := sorry

theorem abs_spec {n : Nat} (a : Vector Int n) :
  (abs a).toList.length = n ∧
  (∀ i : Fin n, (abs a)[i] = Int.natAbs (a[i])) ∧
  (∀ i : Fin n, (abs a)[i] ≥ 0) :=
sorry

end NpAbs
```

### 2. Separated Theorems Format (`sep_thm/`)


**Structure:**
- Namespace under `DafnySpecs.{FunctionName}`
- Helper functions (if needed)
- Main function definition with `sorry`
- Multiple separate theorems for different aspects of the specification; their missing proofs are marked with `sorry`

**Example:**
```lean
/-
# NumPy Abs Specification

Port of np_abs.dfy to Lean 4
-/

namespace DafnySpecs.NpAbs

/-- Absolute value of an integer -/
def absInt (x : Int) : Int := if x < 0 then -x else x

/-- Element-wise absolute value of a vector -/
def abs {n : Nat} (a : Vector Int n) : Vector Int n := sorry

/-- Specification: The result has the same length as input -/
theorem abs_length {n : Nat} (a : Vector Int n) :
  (abs a).toList.length = n := sorry

/-- Specification: Each element is the absolute value of the corresponding input element -/
theorem abs_spec {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n, (abs a)[i] = absInt (a[i]) := sorry

/-- Specification: All elements in the result are non-negative -/
theorem abs_nonnegative {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n, (abs a)[i] ≥ 0 := sorry

end DafnySpecs.NpAbs
```

