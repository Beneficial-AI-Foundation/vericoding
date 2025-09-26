import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Represents different kinds of data types that can be tested -/
inductive DataType
  /-- Scalar integer type -/
  | scalar_int : DataType
  /-- Scalar floating point type -/
  | scalar_float : DataType
  /-- Scalar complex number type -/
  | scalar_complex : DataType
  /-- Scalar boolean type -/
  | scalar_bool : DataType
  /-- Scalar string type -/
  | scalar_string : DataType
  /-- Array type -/
  | array_type : DataType
  /-- Composite type -/
  | composite_type : DataType
  /-- Unknown type -/
  | unknown_type : DataType

/-- Helper function to check if a DataType is a scalar type -/
def isScalarType (dt : DataType) : Bool :=
  match dt with
  | DataType.scalar_int => true
  | DataType.scalar_float => true
  | DataType.scalar_complex => true
  | DataType.scalar_bool => true
  | DataType.scalar_string => true
  | DataType.array_type => false
  | DataType.composite_type => false
  | DataType.unknown_type => false
-- </vc-preamble>

-- <vc-helpers>
-- Helper lemmas for the proof
lemma isScalarType_iff (dt : DataType) : 
  isScalarType dt = true ↔ (dt = DataType.scalar_int ∨ 
                            dt = DataType.scalar_float ∨ 
                            dt = DataType.scalar_complex ∨ 
                            dt = DataType.scalar_bool ∨ 
                            dt = DataType.scalar_string) := by
  cases dt <;> simp [isScalarType]
-- </vc-helpers>

-- <vc-definitions>
def issctype (rep : DataType) : Id Bool :=
  pure (isScalarType rep)
-- </vc-definitions>

-- <vc-theorems>
theorem issctype_spec (rep : DataType) :
    ⦃⌜True⌝⦄
    issctype rep
    ⦃⇓result => ⌜result = true ↔ (rep = DataType.scalar_int ∨ 
                                  rep = DataType.scalar_float ∨ 
                                  rep = DataType.scalar_complex ∨ 
                                  rep = DataType.scalar_bool ∨ 
                                  rep = DataType.scalar_string)⌝⦄ := by
  unfold issctype
  simp [Id.run, pure]
  intro _
  exact isScalarType_iff rep
-- </vc-theorems>
