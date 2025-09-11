namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
def modexp_pow2_aux (x n z : Nat) : Nat := Exp_int x (Exp_int 2 n) % z

theorem modexp_pow2_aux_spec (x n z : Nat) (hz : z > 0) :
  modexp_pow2_aux x n z = Exp_int x (Exp_int 2 n) % z := by
  rfl
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2_int (x y n z : Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
if z = 0 then 0
else if y = Exp_int 2 n then
  -- when y = 2^n, compute x^(2^n) mod z by repeated squaring
  modexp_pow2_aux x n z
else
  x % z
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_int_spec (x y n z : Nat) (hy : y = Exp_int 2 n) (hz : z > 0) :
  ModExpPow2_int x y n z = Exp_int x y % z := by
-- </vc-theorem>
-- <vc-proof>
-- z > 0 implies z ≠ 0
  have nz : z ≠ 0 := by
    intro h
    subst h
    exact (Nat.lt_irrefl 0 hz)
  -- simplify the definition using z ≠ 0 and hy
  dsimp [ModExpPow2_int]
  simp [nz, hy]
  -- apply the helper specification
  exact modexp_pow2_aux_spec x n z hz
-- </vc-proof>

end BignumLean