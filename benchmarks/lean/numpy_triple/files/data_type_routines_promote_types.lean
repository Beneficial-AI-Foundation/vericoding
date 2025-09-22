-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Define enumeration for NumPy data types -/
inductive NumpyDType
  /-- 8-bit unsigned integer -/  | UInt8
  /-- 16-bit unsigned integer -/ | UInt16
  /-- 32-bit unsigned integer -/ | UInt32
  /-- 64-bit unsigned integer -/ | UInt64
  /-- 8-bit signed integer -/    | Int8
  /-- 16-bit signed integer -/   | Int16
  /-- 32-bit signed integer -/   | Int32
  /-- 64-bit signed integer -/   | Int64
  /-- 16-bit floating point -/   | Float16
  /-- 32-bit floating point -/   | Float32
  /-- 64-bit floating point -/   | Float64
  /-- 64-bit complex number -/   | Complex64
  /-- 128-bit complex number -/  | Complex128
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
/-- Define type promotion rules hierarchy -/
def promotion_hierarchy : NumpyDType → Nat
  | .UInt8 => 0
  | .UInt16 => 1
  | .UInt32 => 2
  | .UInt64 => 3
  | .Int8 => 4
  | .Int16 => 5
  | .Int32 => 6
  | .Int64 => 7
  | .Float16 => 8
  | .Float32 => 9
  | .Float64 => 10
  | .Complex64 => 11
  | .Complex128 => 12
/-- Check if a type is a signed integer -/
def is_signed_integer (dt : NumpyDType) : Bool :=
  match dt with
  | .Int8 | .Int16 | .Int32 | .Int64 => true
  | _ => false
/-- Check if a type is an unsigned integer -/
def is_unsigned_integer (dt : NumpyDType) : Bool :=
  match dt with
  | .UInt8 | .UInt16 | .UInt32 | .UInt64 => true
  | _ => false
/-- Check if a type is a floating point type -/
def is_float (dt : NumpyDType) : Bool :=
  match dt with
  | .Float16 | .Float32 | .Float64 => true
  | _ => false
/-- Check if a type is a complex type -/
def is_complex (dt : NumpyDType) : Bool :=
  match dt with
  | .Complex64 | .Complex128 => true
  | _ => false
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def promote_types (type1 type2 : NumpyDType) : Id NumpyDType :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem promote_types_spec (type1 type2 : NumpyDType) :
    ⦃⌜True⌝⦄
    promote_types type1 type2
    ⦃⇓result => ⌜
      -- Symmetry property - function is commutative
      (promote_types type1 type2 = promote_types type2 type1) ∧

      -- Type promotion hierarchy rules
      -- If either input is complex, result must be complex
      (is_complex type1 ∨ is_complex type2) → is_complex result ∧

      -- If either input is float (and not complex), result is float or complex
      (is_float type1 ∨ is_float type2) → (is_float result ∨ is_complex result) ∧

      -- Size constraint: result size >= max of input sizes
      (dtype_size result ≥ max (dtype_size type1) (dtype_size type2)) ∧

      -- Promotion hierarchy: result rank >= max of input ranks
      (promotion_hierarchy result ≥ max (promotion_hierarchy type1) (promotion_hierarchy type2)) ∧

      -- Safety constraints: both input types can be safely cast to result
      -- Complex types can hold any numeric value
      (is_complex result →
        (is_complex type1 ∨ is_float type1 ∨ is_signed_integer type1 ∨ is_unsigned_integer type1) ∧
        (is_complex type2 ∨ is_float type2 ∨ is_signed_integer type2 ∨ is_unsigned_integer type2)) ∧

      -- Float types can hold integers and smaller floats
      (is_float result ∧ ¬is_complex result →
        (¬is_complex type1 ∧ ¬is_complex type2) ∧
        (dtype_size result ≥ dtype_size type1 ∨ ¬is_float type1) ∧
        (dtype_size result ≥ dtype_size type2 ∨ ¬is_float type2)) ∧

      -- Specific promotion rules for common cases from NumPy documentation
      -- Integer + Float → Float with sufficient precision (like 'i8' + 'f4' → 'f8')
      ((is_signed_integer type1 ∨ is_unsigned_integer type1) ∧ is_float type2 →
        is_float result ∧ dtype_size result ≥ dtype_size type2) ∧

      -- Float + Integer → Float with sufficient precision  
      (is_float type1 ∧ (is_signed_integer type2 ∨ is_unsigned_integer type2) →
        is_float result ∧ dtype_size result ≥ dtype_size type1) ∧

      -- Complex + any non-complex → Complex with sufficient precision
      (is_complex type1 ∧ ¬is_complex type2 →
        is_complex result ∧ dtype_size result ≥ dtype_size type1) ∧
      (is_complex type2 ∧ ¬is_complex type1 →
        is_complex result ∧ dtype_size result ≥ dtype_size type2) ∧

      -- Same types promote to themselves (reflexivity)
      (type1 = type2 → result = type1) ∧

      -- Float precision promotion (like 'f4' + 'f8' → 'f8')
      (is_float type1 ∧ is_float type2 →
        is_float result ∧ dtype_size result ≥ max (dtype_size type1) (dtype_size type2))
    ⌝⦄ := by
  sorry
-- </vc-theorems>