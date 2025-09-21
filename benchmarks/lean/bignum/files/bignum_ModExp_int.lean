-- <vc-preamble>
def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ModExp_int (x y n z : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z := by
  sorry
-- </vc-theorems>