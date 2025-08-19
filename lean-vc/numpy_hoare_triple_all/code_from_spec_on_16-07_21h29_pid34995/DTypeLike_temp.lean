import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "DTypeLike",
  "category": "Core Type Aliases",
  "description": "Union type representing objects that can be converted to dtypes",
  "url": "https://numpy.org/doc/stable/reference/typing.html#numpy.typing.DTypeLike",
  "doc": "A union type representing objects that can be coerced into a dtype.\n\nAmong others this includes the likes of:\n- Type objects (e.g. np.int32)\n- Character codes (e.g. 'i4')\n- Objects with a .dtype attribute\n- Tuples for structured types\n- None (which gives the default dtype)\n\nThe DTypeLike type tries to avoid creation of dtype objects using dictionary of fields like np.dtype({'field1': ..., 'field2': ..., ...}) and direct usage of dictionaries as a dtype is disallowed.",
  "code": "# From numpy._typing._dtype_like.py\nDTypeLike: TypeAlias = Union[\n    dtype[Any],\n    # default data type (float64)\n    None,\n    # array-scalar types and generic types\n    type[Any],\n    # character codes, type strings or comma-separated fields, e.g., 'float64'\n    str,\n    # (flexible_dtype, itemsize)\n    tuple[_DTypeLikeNested, int],\n    # (fixed_dtype, shape)\n    tuple[_DTypeLikeNested, _ShapeLike],\n    # (base_dtype, new_dtype)\n    tuple[_DTypeLikeNested, _DTypeLikeNested],\n    # a list of fields\n    list[tuple[str, _DTypeLikeNested]],\n    # (field_name, field_dtype, field_shape)\n    _DTypeDict,\n    # e.g., [('x', '<i4'), ('y', '<i4')]\n    tuple[_DTypeLikeNested, ...],\n]"
}
-/

/-- Lean representation of NumPy's DTypeLike union type.
    
    This inductive type captures all the valid ways to specify a data type
    in NumPy, including type objects, character codes, tuples for structured
    types, and None for default typing.

    Based on numpy._typing._dtype_like.py, DTypeLike represents objects that
    can be coerced into a dtype, providing a unified interface for dtype
    specification across NumPy operations.

    The design excludes problematic patterns like dictionary-based dtype
    creation while supporting all standard dtype specification methods.
-/
inductive DTypeLike where
  /-- None (default float64) -/
  | none : DTypeLike                                    
  /-- Character codes like 'i4', 'float64', etc. -/
  | typeCode : String → DTypeLike                       
  /-- Type objects like np.int32 -/
  | typeClass : String → DTypeLike                      
  /-- (dtype, itemsize) for flexible types -/
  | flexibleTuple : DTypeLike → Nat → DTypeLike         
  /-- (dtype, shape) for fixed types -/
  | fixedTuple : DTypeLike → List Nat → DTypeLike   
  /-- (base_dtype, new_dtype) for type composition -/
  | baseTuple : DTypeLike → DTypeLike → DTypeLike       
  /-- List of field specifications for structured types -/
  | fieldList : List (String × DTypeLike) → DTypeLike 
  deriving Repr, BEq

-- LLM HELPER
def isValidTypeCode (code : String) : Bool :=
  code.length > 0 && (code.startsWith "i" || code.startsWith "f" || 
                      code.startsWith "U" || code.startsWith "S" ||
                      code = "bool" || code = "float64" || code = "int32")

-- LLM HELPER
def hasNoDuplicateNames (fields : List (String × DTypeLike)) : Bool :=
  let names := fields.map (·.1)
  names.Nodup

-- LLM HELPER
def allNonEmptyNames (fields : List (String × DTypeLike)) : Bool :=
  fields.all (fun field => field.1.length > 0)

/-- numpy.typing.DTypeLike: Validates whether an object can be converted to a dtype.

    Determines if a given DTypeLike specification is valid according to NumPy's
    dtype coercion rules. This includes checking format validity for character
    codes, ensuring sensible itemsizes, and validating field specifications.

    This validation function ensures that only meaningful dtype specifications
    are accepted, preventing common errors in dtype creation while maintaining
    compatibility with NumPy's flexible dtype system.

    From NumPy documentation:
    - Input: A DTypeLike specification (various forms allowed)
    - Returns: Boolean indicating whether the specification is valid
    
    Mathematical Properties:
    1. Reflexivity: All well-formed DTypeLike values are valid
    2. Character code validation: String codes must follow NumPy format conventions
    3. Itemsize constraints: Flexible tuples must have positive itemsizes
    4. Field name uniqueness: Field lists cannot have duplicate names
    5. Field name validity: Field names must be non-empty strings
-/
def isValidDTypeLike (dtype : DTypeLike) : Id Bool :=
  match dtype with
  | .none => true
  | .typeCode code => isValidTypeCode code
  | .typeClass _ => true
  | .flexibleTuple inner itemsize => itemsize > 0 && isValidDTypeLike inner
  | .fixedTuple inner shape => isValidDTypeLike inner && shape.all (· > 0)
  | .baseTuple base new => isValidDTypeLike base && isValidDTypeLike new
  | .fieldList fields => hasNoDuplicateNames fields && allNonEmptyNames fields

/-- Specification: isValidDTypeLike correctly identifies valid dtype specifications.

    Mathematical Properties:
    1. None is always valid (represents default float64)
    2. Type codes must be non-empty and follow NumPy conventions
    3. Flexible tuples require positive itemsizes and valid inner dtypes
    4. Fixed tuples require positive shape dimensions and valid inner dtypes
    5. Base tuples require both base and new dtypes to be valid
    6. Field lists require unique names and non-empty field names
    7. Recursive validation for nested DTypeLike values in tuples

    Precondition: True (any DTypeLike value can be validated)
    Postcondition: Returns true iff the dtype specification follows NumPy's coercion rules
-/
theorem isValidDTypeLike_spec (dtype : DTypeLike) :
    ⦃⌜True⌝⦄
    isValidDTypeLike dtype
    ⦃⇓result => ⌜result = true ↔ (
      match dtype with
      | .none => True
      | .typeCode code => code.length > 0 ∧ (
          code.startsWith "i" = true ∨ code.startsWith "f" = true ∨ 
          code.startsWith "U" = true ∨ code.startsWith "S" = true ∨
          code = "bool" ∨ code = "float64" ∨ code = "int32")
      | .typeClass _ => True
      | .flexibleTuple inner itemsize => itemsize > 0 ∧ isValidDTypeLike inner = true
      | .fixedTuple inner shape => isValidDTypeLike inner = true ∧ ∀ x ∈ shape, x > 0
      | .baseTuple base new => isValidDTypeLike base = true ∧ isValidDTypeLike new = true
      | .fieldList fields => 
          (∀ x ∈ fields, ∀ y ∈ fields, x ≠ y → x.1 ≠ y.1) ∧
          (∀ field ∈ fields, field.1.length > 0))⌝⦄ := by
  cases dtype with
  | none => 
    simp [isValidDTypeLike]
    rfl
  | typeCode code => 
    simp [isValidDTypeLike, isValidTypeCode]
    rfl
  | typeClass _ => 
    simp [isValidDTypeLike]
    rfl
  | flexibleTuple inner itemsize =>
    simp [isValidDTypeLike]
    rfl
  | fixedTuple inner shape =>
    simp [isValidDTypeLike]
    rfl
  | baseTuple base new =>
    simp [isValidDTypeLike]
    rfl
  | fieldList fields =>
    simp [isValidDTypeLike, hasNoDuplicateNames, allNonEmptyNames]
    constructor
    · intro h
      constructor
      · exact List.Nodup.pairwise_ne h.1
      · exact h.2
    · intro h
      constructor
      · exact List.pairwise_ne_nodup h.1
      · exact h.2

-- Additional properties for comprehensive specification

/-- None is always a valid DTypeLike (represents default float64) -/
theorem none_valid : isValidDTypeLike .none = true := by
  simp [isValidDTypeLike]

/-- Valid type codes are recognized correctly -/
theorem typeCode_valid_examples : 
    isValidDTypeLike (.typeCode "i4") = true ∧
    isValidDTypeLike (.typeCode "float64") = true ∧
    isValidDTypeLike (.typeCode "bool") = true := by
  simp [isValidDTypeLike, isValidTypeCode]
  constructor
  · simp [String.startsWith, String.length]
    norm_num
  · constructor
    · simp [String.length]
      norm_num
    · simp [String.length]
      norm_num

/-- Invalid type codes are rejected -/
theorem typeCode_invalid_examples :
    isValidDTypeLike (.typeCode "") = false ∧
    isValidDTypeLike (.typeCode "invalid") = false := by
  simp [isValidDTypeLike, isValidTypeCode]
  constructor
  · simp [String.length]
    norm_num
  · simp [String.startsWith, String.length]
    norm_num

/-- Flexible tuples with zero itemsize are invalid -/
theorem flexibleTuple_zero_itemsize_invalid :
    isValidDTypeLike (.flexibleTuple .none 0) = false := by
  simp [isValidDTypeLike]

-- LLM HELPER
theorem List.pairwise_ne_nodup {α : Type*} {l : List α} : 
    (∀ x ∈ l, ∀ y ∈ l, x ≠ y → x ≠ y) → l.Nodup := by
  intro h
  apply List.nodup_iff_pairwise.mpr
  intro x hx y hy hne
  exact h x hx y hy hne

/-- Field lists with duplicate names are invalid -/
theorem fieldList_duplicate_names_invalid 
    (fields : List (String × DTypeLike)) 
    (h : ∃ x ∈ fields, ∃ y ∈ fields, x ≠ y ∧ x.1 = y.1) :
    isValidDTypeLike (.fieldList fields) = false := by
  simp [isValidDTypeLike, hasNoDuplicateNames]
  obtain ⟨x, hx_mem, y, hy_mem, hxy_ne, hxy_eq⟩ := h
  have : ¬List.Nodup (fields.map (·.1)) := by
    simp [List.Nodup, List.nodup_iff_pairwise]
    use x.1
    constructor
    · simp [List.mem_map]
      exact ⟨x, hx_mem, rfl⟩
    · use y.1
      constructor
      · simp [List.mem_map]
        exact ⟨y, hy_mem, rfl⟩
      · constructor
        · rw [hxy_eq]
        · rw [hxy_eq]
  simp [this]