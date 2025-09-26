import Mathlib
-- <vc-preamble>
namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def ModExpPow2_int (x y n z : Nat) : Nat :=
  sorry

axiom ModExpPow2_int_spec (x y n z : Nat) (hy : y = Exp_int 2 n) (hz : z > 0) :
  ModExpPow2_int x y n z = Exp_int x y % z


-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma Exp_int_zero (x : Nat) : Exp_int x 0 = 1 := by
  simp [Exp_int]
-- </vc-helpers>


-- <vc-definitions>
def ModExp_int (x y n z : Nat) : Nat :=
  Exp_int x y % z
-- </vc-definitions>

-- <vc-theorems>
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z := by
  simp [ModExp_int]
-- </vc-theorems>

