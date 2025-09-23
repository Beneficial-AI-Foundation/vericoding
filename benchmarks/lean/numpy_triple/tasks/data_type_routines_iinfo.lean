-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- Integer type information structure containing machine limits for integer types -/
structure IntInfo where
  /-- Number of bits occupied by the type -/
  bits : Nat      
  /-- Smallest integer expressible by the type -/
  min : Int       
  /-- Largest integer expressible by the type -/
  max : Int

/-- Enumeration of supported integer types -/
inductive IntType where
  /-- 8-bit signed integer type -/
  | Int8 : IntType
  /-- 16-bit signed integer type -/
  | Int16 : IntType
  /-- 32-bit signed integer type -/
  | Int32 : IntType
  /-- 64-bit signed integer type -/
  | Int64 : IntType
  /-- 8-bit unsigned integer type -/
  | UInt8 : IntType
  /-- 16-bit unsigned integer type -/
  | UInt16 : IntType
  /-- 32-bit unsigned integer type -/
  | UInt32 : IntType
  /-- 64-bit unsigned integer type -/
  | UInt64 : IntType
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def iinfo (int_type : IntType) : Id IntInfo :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem iinfo_spec (int_type : IntType) :
    ⦃⌜True⌝⦄
    iinfo int_type
    ⦃⇓info => ⌜
      match int_type with
      | IntType.Int8 => info.bits = 8 ∧ info.min = -128 ∧ info.max = 127
      | IntType.Int16 => info.bits = 16 ∧ info.min = -32768 ∧ info.max = 32767
      | IntType.Int32 => info.bits = 32 ∧ info.min = -2147483648 ∧ info.max = 2147483647
      | IntType.Int64 => info.bits = 64 ∧ info.min = -9223372036854775808 ∧ info.max = 9223372036854775807
      | IntType.UInt8 => info.bits = 8 ∧ info.min = 0 ∧ info.max = 255
      | IntType.UInt16 => info.bits = 16 ∧ info.min = 0 ∧ info.max = 65535
      | IntType.UInt32 => info.bits = 32 ∧ info.min = 0 ∧ info.max = 4294967295
      | IntType.UInt64 => info.bits = 64 ∧ info.min = 0 ∧ info.max = 18446744073709551615
    ⌝⦄ := by
  sorry
-- </vc-theorems>