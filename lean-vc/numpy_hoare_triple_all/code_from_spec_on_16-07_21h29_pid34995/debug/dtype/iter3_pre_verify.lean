import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Represents a NumPy data type object with its essential attributes -/
structure DType where
  /-- The fundamental numeric type category -/
  kind : String
  /-- The element size in bytes -/
  itemsize : Nat
  /-- The alignment requirement in bytes -/
  alignment : Nat
  /-- A descriptive name for the data type -/
  name : String
  /-- Whether the data type is signed (for numeric types) -/
  signed : Bool
  
/-- numpy.dtype: Create a data type object.

    A numpy array is homogeneous, and contains elements described by a dtype object. 
    A dtype object can be constructed from different combinations of fundamental numeric types.
    
    This specification focuses on creating basic numeric data types like int16, int32, float32, float64.
    The function maps type specifications to their corresponding DType objects with proper
    attributes like size, alignment, and signedness.
-/
def numpy_dtype (type_spec : String) : Id DType :=
  match type_spec with
  | "int8" => pure { kind := "i", itemsize := 1, alignment := 1, name := "int8", signed := true }
  | "int16" => pure { kind := "i", itemsize := 2, alignment := 2, name := "int16", signed := true }
  | "int32" => pure { kind := "i", itemsize := 4, alignment := 4, name := "int32", signed := true }
  | "int64" => pure { kind := "i", itemsize := 8, alignment := 8, name := "int64", signed := true }
  | "float32" => pure { kind := "f", itemsize := 4, alignment := 4, name := "float32", signed := false }
  | "float64" => pure { kind := "f", itemsize := 8, alignment := 8, name := "float64", signed := false }
  | "bool" => pure { kind := "b", itemsize := 1, alignment := 1, name := "bool", signed := false }
  | _ => pure { kind := "i", itemsize := 4, alignment := 4, name := "int32", signed := true }

/-- Specification: numpy.dtype creates a valid data type object with consistent attributes.

    Precondition: The type_spec is a valid NumPy type specification
    Postcondition: The resulting DType has consistent attributes that match the specified type
-/
theorem numpy_dtype_spec (type_spec : String) 
    (h_valid : type_spec ∈ ["int8", "int16", "int32", "int64", "float32", "float64", "bool"]) :
    ⦃⌜type_spec ∈ ["int8", "int16", "int32", "int64", "float32", "float64", "bool"]⌝⦄
    numpy_dtype type_spec
    ⦃⇓dt => ⌜
      -- The data type has a valid kind character
      (dt.kind ∈ ["i", "f", "b"]) ∧
      -- The itemsize is positive and matches the type specification
      (dt.itemsize > 0) ∧
      -- The alignment is positive and does not exceed the itemsize
      (dt.alignment > 0 ∧ dt.alignment ≤ dt.itemsize) ∧
      -- The name is non-empty
      (dt.name.length > 0) ∧
      -- Size consistency for specific types
      ((type_spec = "int8" → dt.itemsize = 1 ∧ dt.signed = true ∧ dt.kind = "i") ∧
       (type_spec = "int16" → dt.itemsize = 2 ∧ dt.signed = true ∧ dt.kind = "i") ∧
       (type_spec = "int32" → dt.itemsize = 4 ∧ dt.signed = true ∧ dt.kind = "i") ∧
       (type_spec = "int64" → dt.itemsize = 8 ∧ dt.signed = true ∧ dt.kind = "i") ∧
       (type_spec = "float32" → dt.itemsize = 4 ∧ dt.kind = "f") ∧
       (type_spec = "float64" → dt.itemsize = 8 ∧ dt.kind = "f") ∧
       (type_spec = "bool" → dt.itemsize = 1 ∧ dt.kind = "b"))
    ⌝⦄ := by
  intro h_pre
  unfold numpy_dtype
  simp only [List.mem_cons, List.mem_singleton] at h_valid h_pre
  cases h_valid with
  | inl h => 
    simp [h]
    constructor
    · simp
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · simp
    constructor
    · intro; simp
    constructor
    · intro; contradiction
    constructor
    · intro; contradiction
    constructor
    · intro; contradiction
    constructor
    · intro; contradiction
    constructor
    · intro; contradiction
    · intro; contradiction
  | inr h => cases h with
    | inl h => 
      simp [h]
      constructor
      · simp
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · simp
      constructor
      · intro; contradiction
      constructor
      · intro; simp
      constructor
      · intro; contradiction
      constructor
      · intro; contradiction
      constructor
      · intro; contradiction
      constructor
      · intro; contradiction
      · intro; contradiction
    | inr h => cases h with
      | inl h => 
        simp [h]
        constructor
        · simp
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · simp
        constructor
        · intro; contradiction
        constructor
        · intro; contradiction
        constructor
        · intro; simp
        constructor
        · intro; contradiction
        constructor
        · intro; contradiction
        constructor
        · intro; contradiction
        · intro; contradiction
      | inr h => cases h with
        | inl h => 
          simp [h]
          constructor
          · simp
          constructor
          · norm_num
          constructor
          · norm_num
          constructor
          · simp
          constructor
          · intro; contradiction
          constructor
          · intro; contradiction
          constructor
          · intro; contradiction
          constructor
          · intro; simp
          constructor
          · intro; contradiction
          constructor
          · intro; contradiction
          · intro; contradiction
        | inr h => cases h with
          | inl h => 
            simp [h]
            constructor
            · simp
            constructor
            · norm_num
            constructor
            · norm_num
            constructor
            · simp
            constructor
            · intro; contradiction
            constructor
            · intro; contradiction
            constructor
            · intro; contradiction
            constructor
            · intro; contradiction
            constructor
            · intro; simp
            constructor
            · intro; contradiction
            · intro; contradiction
          | inr h => cases h with
            | inl h => 
              simp [h]
              constructor
              · simp
              constructor
              · norm_num
              constructor
              · norm_num
              constructor
              · simp
              constructor
              · intro; contradiction
              constructor
              · intro; contradiction
              constructor
              · intro; contradiction
              constructor
              · intro; contradiction
              constructor
              · intro; contradiction
              constructor
              · intro; simp
              · intro; contradiction
            | inr h => 
              simp [h]
              constructor
              · simp
              constructor
              · norm_num
              constructor
              · norm_num
              constructor
              · simp
              constructor
              · intro; contradiction
              constructor
              · intro; contradiction
              constructor
              · intro; contradiction
              constructor
              · intro; contradiction
              constructor
              · intro; contradiction
              constructor
              · intro; contradiction
              · intro; simp