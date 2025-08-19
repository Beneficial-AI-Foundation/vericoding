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

/-- numpy.promote_types: Returns the data type with the smallest size and smallest scalar kind
    to which both type1 and type2 may be safely cast.
    
    This function is symmetric but rarely associative. It returns a "canonical" dtype.
    
    Examples from NumPy documentation:
    - promote_types('f4', 'f8') = 'f8' (float64)
    - promote_types('i8', 'f4') = 'f8' (float64)
    - promote_types('i4', 'S8') = 'S11' (string, but we focus on numeric types)
-/
def promote_types (type1 type2 : NumpyDType) : Id NumpyDType :=
  if is_complex type1 || is_complex type2 then
    -- Complex types: promote to the highest complex type
    if is_complex type1 && is_complex type2 then
      if promotion_hierarchy type1 >= promotion_hierarchy type2 then type1 else type2
    else if is_complex type1 then
      type1
    else
      type2
  else if is_float type1 || is_float type2 then
    -- Float types: promote to the highest float type with sufficient precision
    if is_float type1 && is_float type2 then
      if promotion_hierarchy type1 >= promotion_hierarchy type2 then type1 else type2
    else if is_float type1 then
      -- Integer + Float -> Float with sufficient precision for the integer
      if is_signed_integer type2 && dtype_size type2 > 32 then .Float64 else type1
    else
      -- Float + Integer -> Float with sufficient precision for the integer
      if is_signed_integer type1 && dtype_size type1 > 32 then .Float64 else type2
  else
    -- Both are integers: promote based on sign and size
    if is_signed_integer type1 && is_signed_integer type2 then
      if promotion_hierarchy type1 >= promotion_hierarchy type2 then type1 else type2
    else if is_unsigned_integer type1 && is_unsigned_integer type2 then
      if promotion_hierarchy type1 >= promotion_hierarchy type2 then type1 else type2
    else
      -- Mixed signed/unsigned: promote to signed with sufficient size
      let max_size := max (dtype_size type1) (dtype_size type2)
      if max_size <= 8 then .Int16
      else if max_size <= 16 then .Int32
      else if max_size <= 32 then .Int64
      else .Int64

/-- Specification: promote_types returns the smallest safe common type for two dtypes.
    
    Key properties based on NumPy's type promotion rules:
    1. Symmetry: promote_types(a, b) = promote_types(b, a)
    2. Safety: Both input types can be safely cast to the result type
    3. Minimality: The result is the smallest type that satisfies the safety requirement
    4. Type promotion hierarchy: 
       - If either input is complex, result is complex
       - If either input is float, result is float (unless both are complex)
       - Signed integers promote to larger signed integers
       - Unsigned integers promote to larger unsigned integers
       - Mixed signed/unsigned promote to signed of sufficient size
    5. Size consideration: Result has size >= max(size(type1), size(type2))
    6. Specific examples:
       - Float32 + Float64 → Float64 (larger precision)
       - Int64 + Float32 → Float64 (float with sufficient precision)
       - Complex64 + Float32 → Complex64 (complex dominates)
-/
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
  simp only [promote_types]
  simp only [Std.Do.Triple.mk]
  simp only [Id.run]
  simp only [and_imp]
  constructor
  · -- Symmetry
    simp [promote_types]
    by_cases h1 : is_complex type1
    · by_cases h2 : is_complex type2
      · simp [h1, h2]
        split_ifs <;> simp [max_comm]
      · simp [h1, h2]
    · by_cases h2 : is_complex type2
      · simp [h1, h2]
      · simp [h1, h2]
        by_cases f1 : is_float type1
        · by_cases f2 : is_float type2
          · simp [f1, f2]
            split_ifs <;> simp [max_comm]
          · simp [f1, f2]
        · by_cases f2 : is_float type2
          · simp [f1, f2]
          · simp [f1, f2]
            split_ifs <;> simp [max_comm]
  constructor
  · -- Complex promotion rule
    intro h
    simp [promote_types]
    cases h with
    | inl h1 => simp [h1]; split_ifs <;> simp [is_complex]
    | inr h2 => simp [h2]; split_ifs <;> simp [is_complex]
  constructor
  · -- Float promotion rule
    intro h
    simp [promote_types]
    cases h with
    | inl h1 => 
      by_cases hc1 : is_complex type1
      · simp [hc1, is_complex]
      · by_cases hc2 : is_complex type2
        · simp [hc1, hc2, is_complex]
        · simp [hc1, hc2, h1]
          split_ifs <;> simp [is_float]
    | inr h2 => 
      by_cases hc1 : is_complex type1
      · simp [hc1, is_complex]
      · by_cases hc2 : is_complex type2
        · simp [hc1, hc2, is_complex]
        · simp [hc1, hc2, h2]
          split_ifs <;> simp [is_float]
  constructor
  · -- Size constraint
    simp [promote_types]
    split_ifs <;> simp [dtype_size, max_le_iff] <;> norm_num
  constructor
  · -- Promotion hierarchy constraint
    simp [promote_types]
    split_ifs <;> simp [promotion_hierarchy, max_le_iff] <;> norm_num
  constructor
  · -- Safety for complex result
    intro h
    simp [is_complex, is_float, is_signed_integer, is_unsigned_integer]
    split_ifs at h <;> simp at h <;> cases type1 <;> cases type2 <;> simp
  constructor
  · -- Safety for float result
    intro h
    simp [promote_types] at h
    simp [is_complex, is_float, is_signed_integer, is_unsigned_integer]
    split_ifs at h <;> simp at h <;> cases type1 <;> cases type2 <;> simp [dtype_size] <;> norm_num
  constructor
  · -- Integer + Float promotion
    intro h
    simp [promote_types]
    cases h with
    | mk h1 h2 =>
      by_cases hc1 : is_complex type1
      · simp [hc1] at h1
      · by_cases hc2 : is_complex type2
        · simp [hc2] at h2
        · simp [hc1, hc2, h2]
          split_ifs <;> simp [is_float, dtype_size] <;> norm_num
  constructor
  · -- Float + Integer promotion
    intro h
    simp [promote_types]
    cases h with
    | mk h1 h2 =>
      by_cases hc1 : is_complex type1
      · simp [hc1] at h1
      · by_cases hc2 : is_complex type2
        · simp [hc2] at h2
        · simp [hc1, hc2, h1]
          split_ifs <;> simp [is_float, dtype_size] <;> norm_num
  constructor
  · -- Complex + non-complex promotion (type1 complex)
    intro h
    simp [promote_types]
    cases h with
    | mk h1 h2 =>
      simp [h1, h2]
      split_ifs <;> simp [is_complex, dtype_size] <;> norm_num
  constructor
  · -- Complex + non-complex promotion (type2 complex)
    intro h
    simp [promote_types]
    cases h with
    | mk h1 h2 =>
      simp [h1, h2]
      split_ifs <;> simp [is_complex, dtype_size] <;> norm_num
  constructor
  · -- Reflexivity
    intro h
    simp [promote_types, h]
    split_ifs <;> simp [Nat.max_self, le_refl]
  · -- Float precision promotion
    intro h
    simp [promote_types]
    cases h with
    | mk h1 h2 =>
      by_cases hc1 : is_complex type1
      · simp [hc1] at h1
      · by_cases hc2 : is_complex type2
        · simp [hc2] at h2
        · simp [hc1, hc2, h1, h2]
          split_ifs <;> simp [is_float, dtype_size, max_le_iff] <;> norm_num