import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Represents a NumPy type class for hierarchy testing -/
inductive NumpyTypeClass where
  /-- Integer types -/
  | IntegerType
  /-- Floating point types -/
  | FloatingType
  /-- Complex number types -/
  | ComplexType
  /-- Boolean type -/
  | BooleanType
  /-- Scalar types (superclass of all numeric types) -/
  | ScalarType
  /-- Number types (excludes boolean) -/
  | NumberType
  /-- Inexact types (floating and complex) -/
  | InexactType
  /-- 8-bit signed integer type -/
  | Int8Type
  /-- 16-bit signed integer type -/
  | Int16Type
  /-- 32-bit signed integer type -/
  | Int32Type
  /-- 64-bit signed integer type -/
  | Int64Type
  /-- 8-bit unsigned integer type -/
  | UInt8Type
  /-- 16-bit unsigned integer type -/
  | UInt16Type
  /-- 32-bit unsigned integer type -/
  | UInt32Type
  /-- 64-bit unsigned integer type -/
  | UInt64Type
  /-- 32-bit floating point type -/
  | Float32Type
  /-- 64-bit floating point type -/
  | Float64Type
  /-- 64-bit complex number type -/
  | Complex64Type
  /-- 128-bit complex number type -/
  | Complex128Type
  /-- Generic object type -/
  | ObjectType
  deriving BEq

/-- Defines the class hierarchy relationships for NumPy types -/
def NumpyTypeClass.isSubclass : NumpyTypeClass → NumpyTypeClass → Bool
  -- Reflexivity: every class is a subclass of itself
  | t, t' => if t == t' then true else
  -- Concrete integer types are subclasses of IntegerType
  match t, t' with
  | Int8Type, IntegerType => true
  | Int16Type, IntegerType => true
  | Int32Type, IntegerType => true
  | Int64Type, IntegerType => true
  | UInt8Type, IntegerType => true
  | UInt16Type, IntegerType => true
  | UInt32Type, IntegerType => true
  | UInt64Type, IntegerType => true
  -- Concrete floating types are subclasses of FloatingType
  | Float32Type, FloatingType => true
  | Float64Type, FloatingType => true
  -- Concrete complex types are subclasses of ComplexType
  | Complex64Type, ComplexType => true
  | Complex128Type, ComplexType => true
  -- Integer types are subclasses of NumberType
  | IntegerType, NumberType => true
  -- Floating types are subclasses of InexactType and NumberType
  | FloatingType, InexactType => true
  | FloatingType, NumberType => true
  -- Complex types are subclasses of InexactType and NumberType
  | ComplexType, InexactType => true
  | ComplexType, NumberType => true
  -- All numeric types are subclasses of ScalarType
  | NumberType, ScalarType => true
  | BooleanType, ScalarType => true
  | IntegerType, ScalarType => true
  | FloatingType, ScalarType => true
  | ComplexType, ScalarType => true
  | InexactType, ScalarType => true
  -- Default case
  | _, _ => false

/-- numpy.issubclass_: Determine if a class is a subclass of a second class.
    
    This function is equivalent to the Python built-in issubclass, except that it returns 
    False instead of raising a TypeError if one of the arguments is not a class.
    
    In the context of NumPy, this tests relationships between NumPy data type classes
    such as whether int32 is a subclass of integer, or whether float64 is a subclass of float.
-/
def issubclass_ (arg1 arg2 : NumpyTypeClass) : Id Bool :=
  return arg1.isSubclass arg2

-- LLM HELPER
lemma isSubclass_trans (t1 t2 t3 : NumpyTypeClass) : 
  t1.isSubclass t2 = true → t2.isSubclass t3 = true → t1.isSubclass t3 = true := by
  intro h1 h2
  simp [NumpyTypeClass.isSubclass] at h1 h2 ⊢
  cases' t1 with
  | IntegerType => 
    cases' t2 with
    | IntegerType => 
      cases' t3 with
      | IntegerType => simp
      | NumberType => simp
      | ScalarType => simp
      | _ => simp at h2
    | NumberType => 
      cases' t3 with
      | NumberType => simp
      | ScalarType => simp
      | _ => simp at h2
    | ScalarType => 
      cases' t3 with
      | ScalarType => simp
      | _ => simp at h2
    | _ => simp at h1
  | FloatingType => 
    cases' t2 with
    | FloatingType => 
      cases' t3 with
      | FloatingType => simp
      | InexactType => simp
      | NumberType => simp
      | ScalarType => simp
      | _ => simp at h2
    | InexactType => 
      cases' t3 with
      | InexactType => simp
      | ScalarType => simp
      | _ => simp at h2
    | NumberType => 
      cases' t3 with
      | NumberType => simp
      | ScalarType => simp
      | _ => simp at h2
    | ScalarType => 
      cases' t3 with
      | ScalarType => simp
      | _ => simp at h2
    | _ => simp at h1
  | ComplexType => 
    cases' t2 with
    | ComplexType => 
      cases' t3 with
      | ComplexType => simp
      | InexactType => simp
      | NumberType => simp
      | ScalarType => simp
      | _ => simp at h2
    | InexactType => 
      cases' t3 with
      | InexactType => simp
      | ScalarType => simp
      | _ => simp at h2
    | NumberType => 
      cases' t3 with
      | NumberType => simp
      | ScalarType => simp
      | _ => simp at h2
    | ScalarType => 
      cases' t3 with
      | ScalarType => simp
      | _ => simp at h2
    | _ => simp at h1
  | BooleanType => 
    cases' t2 with
    | BooleanType => 
      cases' t3 with
      | BooleanType => simp
      | ScalarType => simp
      | _ => simp at h2
    | ScalarType => 
      cases' t3 with
      | ScalarType => simp
      | _ => simp at h2
    | _ => simp at h1
  | Int32Type => 
    cases' t2 with
    | Int32Type => 
      cases' t3 with
      | Int32Type => simp
      | IntegerType => simp
      | NumberType => simp
      | ScalarType => simp
      | _ => simp at h2
    | IntegerType => 
      cases' t3 with
      | IntegerType => simp
      | NumberType => simp
      | ScalarType => simp
      | _ => simp at h2
    | NumberType => 
      cases' t3 with
      | NumberType => simp
      | ScalarType => simp
      | _ => simp at h2
    | ScalarType => 
      cases' t3 with
      | ScalarType => simp
      | _ => simp at h2
    | _ => simp at h1
  | _ => 
    simp [NumpyTypeClass.isSubclass] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ <;> simp_all

/-- Specification: issubclass_ correctly determines class hierarchy relationships.
    
    This function tests whether arg1 is a subclass of arg2 according to NumPy's type
    hierarchy. The specification ensures that:
    1. The function respects the established type hierarchy (e.g., int32 ⊆ integer ⊆ number ⊆ scalar)
    2. It handles reflexivity correctly (every class is a subclass of itself)
    3. It returns False for unrelated classes
    4. It never raises exceptions (returns False instead of error for invalid inputs)
    
    Precondition: True (no special preconditions, handles all inputs gracefully)
    Postcondition: Returns True if arg1 is a subclass of arg2, False otherwise
-/
theorem issubclass_spec (arg1 arg2 : NumpyTypeClass) :
    ⦃⌜True⌝⦄
    issubclass_ arg1 arg2
    ⦃⇓result => ⌜
      -- Result matches the defined hierarchy
      result = arg1.isSubclass arg2 ∧
      -- Reflexivity: every class is a subclass of itself
      (arg1 = arg2 → result = true) ∧
      -- Concrete examples from NumPy documentation
      (arg1 = NumpyTypeClass.Int32Type ∧ arg2 = NumpyTypeClass.IntegerType → result = true) ∧
      (arg1 = NumpyTypeClass.Float64Type ∧ arg2 = NumpyTypeClass.FloatingType → result = true) ∧
      (arg1 = NumpyTypeClass.Int32Type ∧ arg2 = NumpyTypeClass.FloatingType → result = false) ∧
      -- Transitivity: int32 → integer → number → scalar
      (arg1 = NumpyTypeClass.Int32Type ∧ arg2 = NumpyTypeClass.NumberType → 
       NumpyTypeClass.Int32Type.isSubclass NumpyTypeClass.IntegerType ∧
       NumpyTypeClass.IntegerType.isSubclass NumpyTypeClass.NumberType) ∧
      -- All numeric types are subclasses of ScalarType
      (arg1 = NumpyTypeClass.IntegerType ∧ arg2 = NumpyTypeClass.ScalarType → result = true) ∧
      (arg1 = NumpyTypeClass.FloatingType ∧ arg2 = NumpyTypeClass.ScalarType → result = true) ∧
      (arg1 = NumpyTypeClass.ComplexType ∧ arg2 = NumpyTypeClass.ScalarType → result = true)
    ⌝⦄ := by
  simp [issubclass_]
  constructor
  · simp
  constructor
  · intro h
    simp [h, NumpyTypeClass.isSubclass]
  constructor
  · intro h
    cases h with
    | mk h1 h2 => simp [h1, h2, NumpyTypeClass.isSubclass]
  constructor
  · intro h
    cases h with
    | mk h1 h2 => simp [h1, h2, NumpyTypeClass.isSubclass]
  constructor
  · intro h
    cases h with
    | mk h1 h2 => simp [h1, h2, NumpyTypeClass.isSubclass]
  constructor
  · intro h
    cases h with
    | mk h1 h2 => simp [h1, h2, NumpyTypeClass.isSubclass]
  constructor
  · intro h
    cases h with
    | mk h1 h2 => simp [h1, h2, NumpyTypeClass.isSubclass]
  constructor
  · intro h
    cases h with
    | mk h1 h2 => simp [h1, h2, NumpyTypeClass.isSubclass]
  · intro h
    cases h with
    | mk h1 h2 => simp [h1, h2, NumpyTypeClass.isSubclass]