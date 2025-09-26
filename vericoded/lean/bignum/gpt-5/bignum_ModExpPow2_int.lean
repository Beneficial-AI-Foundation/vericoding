import Mathlib
-- <vc-preamble>
namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)


-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed for this module
-- </vc-helpers>


-- <vc-definitions>
def ModExpPow2_int (x y n z : Nat) : Nat :=
  Exp_int x y % z
-- </vc-definitions>

-- <vc-theorems>
theorem ModExpPow2_int_spec (x y n z : Nat) (hy : y = Exp_int 2 n) (hz : z > 0) :
  ModExpPow2_int x y n z = Exp_int x y % z := by
  rfl
-- </vc-theorems>

