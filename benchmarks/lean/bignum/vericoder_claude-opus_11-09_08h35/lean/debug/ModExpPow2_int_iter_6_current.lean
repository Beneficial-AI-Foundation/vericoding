namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- No helpers needed, the Exp_int definition is already provided
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2_int (x y n z : Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
if n = 0 then
    x % z
  else
    let r := ModExpPow2_int x (Exp_int 2 (n - 1)) (n - 1) z
    (r * r) % z
termination_by n
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_int_spec (x y n z : Nat) (hy : y = Exp_int 2 n) (hz : z > 0) :
  ModExpPow2_int x y n z = Exp_int x y % z := by
-- </vc-theorem>
-- <vc-proof>
induction n generalizing x y with
  | zero =>
    simp [ModExpPow2_int]
    rw [hy]
    simp [Exp_int]
  | succ n' ih =>
    simp [ModExpPow2_int]
    have hsub : n' + 1 - 1 = n' := Nat.add_sub_cancel n' 1
    rw [hsub]
    have hexp2 : Exp_int 2 n' = Exp_int 2 n' := rfl
    rw [ih x (Exp_int 2 n') hexp2 hz]
    rw [hy]
    -- Exp_int 2 (n' + 1) = 2 * Exp_int 2 n'
    have h2pow : Exp_int 2 (n' + 1) = 2 * Exp_int 2 n' := by
      simp [Exp_int, Nat.add_sub_cancel]
    rw [h2pow]
    -- Exp_int x (2 * Exp_int 2 n') = (Exp_int x (Exp_int 2 n'))^2
    have hexp_mul : Exp_int x (2 * Exp_int 2 n') = Exp_int x (Exp_int 2 n') * Exp_int x (Exp_int 2 n') := by
      have h2eq : 2 * Exp_int 2 n' = Exp_int 2 n' + Exp_int 2 n' := by
        ring
      rw [h2eq]
      clear h2eq
      -- Now prove Exp_int x (a + b) = Exp_int x a * Exp_int x b
      generalize ha : Exp_int 2 n' = a
      induction a with
      | zero => simp [Exp_int]
      | succ a' iha =>
        simp [Exp_int, Nat.add_sub_cancel]
        ring
    rw [hexp_mul]
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
-- </vc-proof>

end BignumLean