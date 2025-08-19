import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- NumPy scalar data types represented as an inductive type -/
inductive NumpyScalarType
  | int32 : NumpyScalarType
  | int64 : NumpyScalarType
  | float32 : NumpyScalarType
  | float64 : NumpyScalarType
  | complex64 : NumpyScalarType
  | complex128 : NumpyScalarType
  | object : NumpyScalarType
  | string : NumpyScalarType
  | bool : NumpyScalarType
  deriving Repr, DecidableEq

/-- Object representation for type introspection -/
inductive NumpyObject
  | int_val : Int → NumpyObject
  | float_val : Float → NumpyObject
  | array_int : ∀ {n : Nat}, Vector Int n → NumpyObject
  | array_float : ∀ {n : Nat}, Vector Float n → NumpyObject
  | array_complex : ∀ {n : Nat}, Vector (Float × Float) n → NumpyObject
  | generic_obj : Unit → NumpyObject
  | string_val : String → NumpyObject
  | bool_val : Bool → NumpyObject
  deriving Repr

/-- Helper predicate: Check if object matches given scalar type -/
def NumpyObject.matches_scalar_type (obj : NumpyObject) (dtype : NumpyScalarType) : Prop :=
  match obj, dtype with
  | NumpyObject.int_val _, NumpyScalarType.int64 => True
  | NumpyObject.float_val _, NumpyScalarType.float64 => True
  | NumpyObject.string_val _, NumpyScalarType.string => True
  | NumpyObject.bool_val _, NumpyScalarType.bool => True
  | _, _ => False

/-- Helper predicate: Check if object is an array with given element type -/
def NumpyObject.is_array_with_element_type (obj : NumpyObject) (dtype : NumpyScalarType) : Prop :=
  match obj, dtype with
  | NumpyObject.array_int _, NumpyScalarType.int64 => True
  | NumpyObject.array_float _, NumpyScalarType.float64 => True
  | NumpyObject.array_complex _, NumpyScalarType.complex128 => True
  | _, _ => False

/-- Helper predicate: Check if object is a generic object -/
def NumpyObject.is_generic_object (obj : NumpyObject) : Prop :=
  match obj with
  | NumpyObject.generic_obj _ => True
  | _ => False

/-- numpy.obj2sctype: Return the scalar dtype or NumPy equivalent of Python type of an object.

    Takes any object and returns its corresponding NumPy scalar data type.
    If the object's type cannot be determined, returns the default value if provided,
    otherwise returns none.

    This function performs type introspection to determine the appropriate NumPy
    scalar type for any given object, including arrays, scalars, and generic objects.
-/
def obj2sctype (rep : NumpyObject) (default : Option NumpyScalarType) : Id (Option NumpyScalarType) :=
  match rep with
  | NumpyObject.int_val _ => pure (some NumpyScalarType.int64)
  | NumpyObject.float_val _ => pure (some NumpyScalarType.float64)
  | NumpyObject.array_int _ => pure (some NumpyScalarType.int64)
  | NumpyObject.array_float _ => pure (some NumpyScalarType.float64)
  | NumpyObject.array_complex _ => pure (some NumpyScalarType.complex128)
  | NumpyObject.string_val _ => pure (some NumpyScalarType.string)
  | NumpyObject.bool_val _ => pure (some NumpyScalarType.bool)
  | NumpyObject.generic_obj _ => pure default

/-- Specification: obj2sctype returns the appropriate NumPy scalar type for the input object.

    The function correctly identifies:
    1. Scalar types from their corresponding objects
    2. Array element types from array objects
    3. Generic object types
    4. Returns default for unrecognized types
    5. Returns none when no default is provided for unrecognized types

    Precondition: True (works with any object)
    Postcondition: The result correctly represents the scalar type of the input object
-/
theorem obj2sctype_spec (rep : NumpyObject) (default : Option NumpyScalarType) :
    ⦃⌜True⌝⦄
    obj2sctype rep default
    ⦃⇓result => ⌜
      (match rep with
       | NumpyObject.int_val _ => result = some NumpyScalarType.int64
       | NumpyObject.float_val _ => result = some NumpyScalarType.float64
       | NumpyObject.array_int _ => result = some NumpyScalarType.int64
       | NumpyObject.array_float _ => result = some NumpyScalarType.float64
       | NumpyObject.array_complex _ => result = some NumpyScalarType.complex128
       | NumpyObject.string_val _ => result = some NumpyScalarType.string
       | NumpyObject.bool_val _ => result = some NumpyScalarType.bool
       | NumpyObject.generic_obj _ => result = default) ∧
      (match result with
       | some dtype => (
           (rep.matches_scalar_type dtype) ∨ 
           (rep.is_array_with_element_type dtype) ∨
           (rep.is_generic_object ∧ result = default)
         )
       | none => rep.is_generic_object ∧ default = none)
    ⌝⦄ := by
  unfold obj2sctype
  cases rep with
  | int_val a => 
    simp [Triple.pure_spec]
    constructor
    · rfl
    · left
      simp [NumpyObject.matches_scalar_type]
  | float_val a => 
    simp [Triple.pure_spec]
    constructor
    · rfl
    · left
      simp [NumpyObject.matches_scalar_type]
  | array_int a => 
    simp [Triple.pure_spec]
    constructor
    · rfl
    · right
      left
      simp [NumpyObject.is_array_with_element_type]
  | array_float a => 
    simp [Triple.pure_spec]
    constructor
    · rfl
    · right
      left
      simp [NumpyObject.is_array_with_element_type]
  | array_complex a => 
    simp [Triple.pure_spec]
    constructor
    · rfl
    · right
      left
      simp [NumpyObject.is_array_with_element_type]
  | string_val a => 
    simp [Triple.pure_spec]
    constructor
    · rfl
    · left
      simp [NumpyObject.matches_scalar_type]
  | bool_val a => 
    simp [Triple.pure_spec]
    constructor
    · rfl
    · left
      simp [NumpyObject.matches_scalar_type]
  | generic_obj a => 
    simp [Triple.pure_spec]
    constructor
    · rfl
    · cases default with
      | some dtype => 
        right
        right
        constructor
        · simp [NumpyObject.is_generic_object]
        · rfl
      | none => 
        constructor
        · simp [NumpyObject.is_generic_object]
        · rfl