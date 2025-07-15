import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.iinfo",
  "category": "Machine limits",
  "description": "Machine limits for integer types",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.iinfo.html",
  "doc": "Machine limits for integer types.\n\nParameters:\nint_type : integer type, dtype, or instance\n    The kind of integer data type to get information about.\n\nAttributes:\n- bits : int - The number of bits occupied by the type\n- dtype : dtype - The dtype for which iinfo returns information\n- min : int - Minimum value of given dtype\n- max : int - Maximum value of given dtype",
  "code": "# Example usage:\nimport numpy as np\n\n# For int32:\niinfo_32 = np.iinfo(np.int32)\nprint(f\"min: {iinfo_32.min}\")  # -2147483648\nprint(f\"max: {iinfo_32.max}\")  # 2147483647\nprint(f\"bits: {iinfo_32.bits}\")  # 32\n\n# For int64:\niinfo_64 = np.iinfo(np.int64)\nprint(f\"min: {iinfo_64.min}\")  # -9223372036854775808\nprint(f\"max: {iinfo_64.max}\")  # 9223372036854775807\nprint(f\"bits: {iinfo_64.bits}\")  # 64"
}
-/

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

/-- Machine limits for integer types - returns information about the given integer type including 
    the number of bits, minimum value, and maximum value -/
def iinfo (intType : IntegerType) : Id IntegerInfo :=
  sorry

/-- Specification: iinfo returns correct machine limits for integer types.
    The returned IntegerInfo structure contains:
    - bits: the number of bits used by the type
    - min: the minimum representable value (-(2^(bits-1)) for signed, 0 for unsigned)
    - max: the maximum representable value (2^(bits-1) - 1 for signed, 2^bits - 1 for unsigned) -/
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