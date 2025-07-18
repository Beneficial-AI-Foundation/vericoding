import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Enumeration for NumPy data types -/
inductive NumpyDType
  | UInt8 | UInt16 | UInt32 | UInt64
  | Int8 | Int16 | Int32 | Int64
  | Float16 | Float32 | Float64
  | Complex64 | Complex128
  deriving Repr, DecidableEq

/-- Define type sizes in bits -/
def dtype_size : NumpyDType → Nat
  | .UInt8 => 8
  | .UInt16 => 16
  | .UInt32 => 32
  | .UInt64 => 64
  | .Int8 => 8
  | .Int16 => 16
  | .Int32 => 32
  | .Int64 => 64
  | .Float16 => 16
  | .Float32 => 32
  | .Float64 => 64
  | .Complex64 => 64
  | .Complex128 => 128

/-- Define type hierarchy (order of preference) -/
def dtype_kind_order : NumpyDType → Nat
  | .UInt8 | .UInt16 | .UInt32 | .UInt64 => 0  -- unsigned integers first
  | .Int8 | .Int16 | .Int32 | .Int64 => 1      -- signed integers second
  | .Float16 | .Float32 | .Float64 => 2       -- floats third
  | .Complex64 | .Complex128 => 3             -- complex last

/-- Check if a type can represent a given float value -/
def can_represent_value (dt : NumpyDType) (value : Float) : Prop :=
  match dt with
  | .UInt8 => 0 ≤ value ∧ value ≤ 255 ∧ value = value.floor
  | .UInt16 => 0 ≤ value ∧ value ≤ 65535 ∧ value = value.floor
  | .UInt32 => 0 ≤ value ∧ value ≤ 4294967295 ∧ value = value.floor
  | .UInt64 => 0 ≤ value ∧ value ≤ 18446744073709551615 ∧ value = value.floor
  | .Int8 => -128 ≤ value ∧ value ≤ 127 ∧ value = value.floor
  | .Int16 => -32768 ≤ value ∧ value ≤ 32767 ∧ value = value.floor
  | .Int32 => -2147483648 ≤ value ∧ value ≤ 2147483647 ∧ value = value.floor
  | .Int64 => -9223372036854775808 ≤ value ∧ value ≤ 9223372036854775807 ∧ value = value.floor
  | .Float16 | .Float32 | .Float64 | .Complex64 | .Complex128 => True

/-- numpy.min_scalar_type: For scalar a, returns the data type with the smallest size 
    and smallest scalar kind which can hold its value.

    This function determines the minimal NumPy data type that can represent a given scalar value.
    The function prioritizes:
    1. Smallest possible size (in bits)
    2. Smallest scalar kind (unsigned int < signed int < float < complex)
    
    For integer values, it finds the smallest integer type that can hold the value.
    For floating point values, it finds the smallest float type that can represent it.
-/
def min_scalar_type (value : Float) : Id NumpyDType :=
  sorry

/-- Specification: min_scalar_type returns the minimal data type that can hold the given value.

    Precondition: True (works for any scalar value)
    Postcondition: The returned type is the minimal type that can hold the value, meaning:
    1. The type can represent the given value
    2. No type with smaller size can represent the value
    3. Among types of the same size, it has the smallest kind order
-/
theorem min_scalar_type_spec (value : Float) :
    ⦃⌜True⌝⦄
    min_scalar_type value
    ⦃⇓result => ⌜
      -- The result type can represent the value
      can_represent_value result value ∧
      -- No smaller type can represent the value
      (∀ dt : NumpyDType, dtype_size dt < dtype_size result → 
        ¬can_represent_value dt value) ∧
      -- Among types of same size, it has smallest kind order
      (∀ dt : NumpyDType, dtype_size dt = dtype_size result → 
        can_represent_value dt value → 
        dtype_kind_order result ≤ dtype_kind_order dt)
    ⌝⦄ := by
  sorry