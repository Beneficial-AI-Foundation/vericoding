import Mathlib
-- <vc-preamble>
namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)


-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem lt_of_gt {a b : Nat} (h : a > b) : b < a := h
-- </vc-helpers>


-- <vc-definitions>
def ModExp_int (x y n z : Nat) : Nat :=
  Exp_int x y % z
-- </vc-definitions>

-- <vc-theorems>
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z := by
  rfl
-- </vc-theorems>

