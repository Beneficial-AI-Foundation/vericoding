-- <vc-preamble>
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
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_dtype (type_spec : String) : Id DType :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
  sorry
-- </vc-theorems>