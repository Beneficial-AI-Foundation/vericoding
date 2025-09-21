-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Structure representing integer type information -/
structure IntegerInfo where
  bits : Nat
  min : Int
  max : Int

/-- Enumeration of supported integer types -/
inductive IntegerType
  | Int8
  | Int16
  | Int32
  | Int64
  | UInt8
  | UInt16
  | UInt32
  | UInt64
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def iinfo (intType : IntegerType) : Id IntegerInfo :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem iinfo_spec (intType : IntegerType) :
    ⦃⌜True⌝⦄
    iinfo intType
    ⦃⇓info => ⌜match intType with
      | IntegerType.Int8 => 
          info.bits = 8 ∧ info.min = -128 ∧ info.max = 127
      | IntegerType.Int16 => 
          info.bits = 16 ∧ info.min = -32768 ∧ info.max = 32767
      | IntegerType.Int32 => 
          info.bits = 32 ∧ info.min = -2147483648 ∧ info.max = 2147483647
      | IntegerType.Int64 => 
          info.bits = 64 ∧ info.min = -9223372036854775808 ∧ info.max = 9223372036854775807
      | IntegerType.UInt8 => 
          info.bits = 8 ∧ info.min = 0 ∧ info.max = 255
      | IntegerType.UInt16 => 
          info.bits = 16 ∧ info.min = 0 ∧ info.max = 65535
      | IntegerType.UInt32 => 
          info.bits = 32 ∧ info.min = 0 ∧ info.max = 4294967295
      | IntegerType.UInt64 => 
          info.bits = 64 ∧ info.min = 0 ∧ info.max = 18446744073709551615⌝⦄ := by
  sorry
-- </vc-theorems>