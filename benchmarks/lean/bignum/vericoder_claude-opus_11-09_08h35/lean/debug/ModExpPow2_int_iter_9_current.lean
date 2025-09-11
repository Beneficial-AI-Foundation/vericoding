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
    unfold ModExpPow2_int
    rw [hy]
    unfold Exp_int
    rfl
  | succ n' ih =>
    unfold ModExpPow2_int
    split_ifs with h
    · exfalso
      exact Nat.succ_ne_zero n' h
    · have hsub : n' + 1 - 1 = n' := Nat.add_sub_cancel n' 1
      rw [hsub]
      rw [ih x (Exp_int 2 n') rfl hz]
      rw [hy]
      have h2pow : Exp_int 2 (n' + 1) = 2 * Exp_int 2 n' := by
        unfold Exp_int
        split_ifs with h2
        · exfalso
          exact Nat.succ_ne_zero n' h2
        · rw [Nat.add_sub_cancel]
      rw [h2pow]
      have hexp_mul : Exp_int x (2 * Exp_int 2 n') = Exp_int x (Exp_int 2 n') * Exp_int x (Exp_int 2 n') := by
        generalize ha : Exp_int 2 n' = a
        clear hy h2pow h hsub ih
        induction a with
        | zero => 
          unfold Exp_int
          rfl
        | succ a' iha =>
          unfold Exp_int at *
          split_ifs with h3
          · rw [h3]
            unfold Exp_int
            split_ifs
            · rfl
            · contradiction
          · have : 2 * (a' + 1) - 1 = 2 * a' + 1 := by
              rw [Nat.mul_succ, Nat.add_sub_cancel]
            rw [this]
            unfold Exp_int
            split_ifs with h4
            · exfalso
              exact Nat.succ_ne_zero (2 * a') h4
            · have : 2 * a' + 1 - 1 = 2 * a' := Nat.add_sub_cancel (2 * a') 1
              rw [this]
              rw [← iha]
              unfold Exp_int
              split_ifs with h5
              · exfalso
                exact Nat.succ_ne_zero a' h5
              · ring
      rw [hexp_mul]
      rw [Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod]
      · exact Nat.one_lt_iff_ne_zero_and_ne_one.mp (Nat.one_lt_of_lt hz)
-- </vc-proof>

end BignumLean