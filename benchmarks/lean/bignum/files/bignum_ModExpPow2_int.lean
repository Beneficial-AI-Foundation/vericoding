-- <vc-preamble>
def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ModExpPow2_int (x y n z : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ModExpPow2_int_spec (x y n z : Nat) (hy : y = Exp_int 2 n) (hz : z > 0) :
  ModExpPow2_int x y n z = Exp_int x y % z := by
  sorry
-- </vc-theorems>