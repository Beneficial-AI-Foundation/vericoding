import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_799_RotateLeftBits",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_799_RotateLeftBits",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Rotates bits in a 32-bit value left by specified number of positions.

@param n The 32-bit value to rotate
@param d The number of positions to rotate left (must be between 0 and 31)
@return The rotated value
-/
def RotateLeftBits (n : UInt32) (d : Int) : UInt32 := sorry

/--
Specification for RotateLeftBits:
- Requires d to be between 0 and 31 inclusive
- Ensures result is n rotated left by d bits
-/
theorem RotateLeftBits_spec (n : UInt32) (d : Int) :
  0 ≤ d ∧ d < 32 →
  RotateLeftBits n d = ((UInt32.shiftLeft n (UInt32.ofNat d.toNat)) ||| (UInt32.shiftRight n (UInt32.ofNat (32 - d).toNat))) := sorry

end DafnyBenchmarks
