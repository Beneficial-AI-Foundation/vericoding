-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- NumPy data type representation -/
inductive NumpyDType where
  /-- Boolean data type -/
  | Bool : NumpyDType
  /-- 8-bit signed integer -/
  | Int8 : NumpyDType
  /-- 16-bit signed integer -/
  | Int16 : NumpyDType
  /-- 32-bit signed integer -/
  | Int32 : NumpyDType
  /-- 64-bit signed integer -/
  | Int64 : NumpyDType
  /-- 8-bit unsigned integer -/
  | UInt8 : NumpyDType
  /-- 16-bit unsigned integer -/
  | UInt16 : NumpyDType
  /-- 32-bit unsigned integer -/
  | UInt32 : NumpyDType
  /-- 64-bit unsigned integer -/
  | UInt64 : NumpyDType
  /-- 16-bit floating point -/
  | Float16 : NumpyDType
  /-- 32-bit floating point -/
  | Float32 : NumpyDType
  /-- 64-bit floating point -/
  | Float64 : NumpyDType
  /-- 64-bit complex number -/
  | Complex64 : NumpyDType
  /-- 128-bit complex number -/
  | Complex128 : NumpyDType
  deriving DecidableEq, Repr

/-- NumPy data type kind categories -/
inductive DTypeKind where
  /-- Boolean kind -/
  | Bool : DTypeKind
  /-- Signed integer kind -/
  | SignedInteger : DTypeKind
  /-- Unsigned integer kind -/
  | UnsignedInteger : DTypeKind
  /-- Any integer kind (signed or unsigned) -/
  | Integral : DTypeKind
  /-- Real floating point kind -/
  | RealFloating : DTypeKind
  /-- Complex floating point kind -/
  | ComplexFloating : DTypeKind
  /-- Any numeric kind -/
  | Numeric : DTypeKind
  deriving DecidableEq, Repr

/-- Get the fundamental kind of a NumPy dtype -/
def getDTypeKind (dtype : NumpyDType) : DTypeKind :=
  match dtype with
  | .Bool => .Bool
  | .Int8 | .Int16 | .Int32 | .Int64 => .SignedInteger
  | .UInt8 | .UInt16 | .UInt32 | .UInt64 => .UnsignedInteger
  | .Float16 | .Float32 | .Float64 => .RealFloating
  | .Complex64 | .Complex128 => .ComplexFloating
/-- Check if a NumPy dtype belongs to a specific kind category -/
def isOfKind (dtype : NumpyDType) (kind : DTypeKind) : Bool :=
  match kind with
  | .Bool => getDTypeKind dtype = .Bool
  | .SignedInteger => getDTypeKind dtype = .SignedInteger
  | .UnsignedInteger => getDTypeKind dtype = .UnsignedInteger
  | .Integral => getDTypeKind dtype = .SignedInteger ∨ getDTypeKind dtype = .UnsignedInteger
  | .RealFloating => getDTypeKind dtype = .RealFloating
  | .ComplexFloating => getDTypeKind dtype = .ComplexFloating
  | .Numeric => getDTypeKind dtype ∈ [.Bool, .SignedInteger, .UnsignedInteger, .RealFloating, .ComplexFloating]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_isdtype (dtype : NumpyDType) (kind : DTypeKind) : Id Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_isdtype_spec (dtype : NumpyDType) (kind : DTypeKind) :
    ⦃⌜True⌝⦄
    numpy_isdtype dtype kind
    ⦃⇓result => ⌜result = isOfKind dtype kind⌝⦄ := by
  sorry
-- </vc-theorems>