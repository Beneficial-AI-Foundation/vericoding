-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Scalar data type enumeration for numpy types -/
inductive ScalarType
  | /-- 32-bit signed integer -/ int32
  | /-- 64-bit signed integer -/ int64
  | /-- 32-bit floating point -/ float32
  | /-- 64-bit floating point -/ float64
  | /-- 64-bit complex number -/ complex64
  | /-- 128-bit complex number -/ complex128
  | /-- Byte string -/ bytes
  | /-- Generic object -/ object
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sctype2char (sctype : ScalarType) : Id String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sctype2char_spec (sctype : ScalarType) :
    ⦃⌜True⌝⦄
    sctype2char sctype
    ⦃⇓result => ⌜
      (sctype = ScalarType.int32 → result = "l") ∧
      (sctype = ScalarType.int64 → result = "q") ∧
      (sctype = ScalarType.float32 → result = "f") ∧
      (sctype = ScalarType.float64 → result = "d") ∧
      (sctype = ScalarType.complex64 → result = "F") ∧
      (sctype = ScalarType.complex128 → result = "D") ∧
      (sctype = ScalarType.bytes → result = "S") ∧
      (sctype = ScalarType.object → result = "O")
    ⌝⦄ := by
  sorry
-- </vc-theorems>