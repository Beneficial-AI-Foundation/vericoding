-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- A format descriptor for structured data types -/
inductive FormatDescriptor where
  /-- 64-bit floating point ('f8') -/
  | float64 : FormatDescriptor
  /-- 32-bit integer ('i4') -/
  | int32   : FormatDescriptor
  /-- Variable length string ('S5' for string of length 5) -/
  | string  : Nat → FormatDescriptor
  /-- 64-bit integer ('i8') -/
  | int64   : FormatDescriptor
  /-- 32-bit floating point ('f4') -/
  | float32 : FormatDescriptor
  deriving Repr, BEq

/-- A field in a structured data type -/
structure Field where
  /-- Field name -/
  name : String
  /-- Format descriptor -/
  format : FormatDescriptor
  /-- Optional title for the field -/
  title : Option String := none
  deriving Repr, BEq

/-- A structured data type specification -/
structure DType (n : Nat) where
  /-- Vector of fields -/
  fields : Vector Field n
  /-- Whether fields are aligned as C-compiler would -/
  aligned : Bool := false
  deriving Repr, BEq
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_format_parser {n : Nat} 
    (formats : Vector String n) 
    (names : Vector String n) 
    (titles : Option (Vector String n) := none)
    (aligned : Bool := false) : Id (DType n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_format_parser_spec {n : Nat} 
    (formats : Vector String n) 
    (names : Vector String n) 
    (titles : Option (Vector String n) := none)
    (aligned : Bool := false)
    (h_valid_formats : ∀ i : Fin n, formats.get i ∈ ["f8", "f4", "i4", "i8"] ∨ 
                       ∃ k : Nat, formats.get i = s!"S{k}") :
    ⦃⌜∀ i : Fin n, formats.get i ∈ ["f8", "f4", "i4", "i8"] ∨ 
       ∃ k : Nat, formats.get i = s!"S{k}"⌝⦄
    numpy_format_parser formats names titles aligned
    ⦃⇓dtype => ⌜
      -- Each field has the correct name
      (∀ i : Fin n, (dtype.fields.get i).name = names.get i) ∧
      -- Each field has a valid format descriptor
      (∀ i : Fin n, match formats.get i with
        | "f8" => (dtype.fields.get i).format = FormatDescriptor.float64
        | "f4" => (dtype.fields.get i).format = FormatDescriptor.float32
        | "i4" => (dtype.fields.get i).format = FormatDescriptor.int32
        | "i8" => (dtype.fields.get i).format = FormatDescriptor.int64
        | s => ∃ k : Nat, s = s!"S{k}" ∧ (dtype.fields.get i).format = FormatDescriptor.string k) ∧
      -- If titles are provided, each field has the correct title
      (match titles with
        | some title_vec => ∀ i : Fin n, (dtype.fields.get i).title = some (title_vec.get i)
        | none => ∀ i : Fin n, (dtype.fields.get i).title = Option.none) ∧
      -- The alignment setting is preserved
      (dtype.aligned = aligned)
    ⌝⦄ := by
  sorry
-- </vc-theorems>