namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def ModExpPow2_int (x y n z : Nat) : Nat :=
  sorry

axiom ModExpPow2_int_spec (x y n z : Nat) (hy : y = Exp_int 2 n) (hz : z > 0) :
  ModExpPow2_int x y n z = Exp_int x y % z

-- <vc-helpers>
-- LLM HELPER
lemma Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  induction b generalizing a with
  | zero => simp [Exp_int]
  | succ b ih =>
    rw [Nat.add_succ, Exp_int]
    simp only [Nat.add_sub_cancel]
    rw [ih, Exp_int]
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    ring

-- LLM HELPER
lemma Exp_int_mul (x a b : Nat) : Exp_int x (a * b) = Exp_int (Exp_int x a) b := by
  induction b generalizing a with
  | zero => simp [Exp_int]
  | succ b ih =>
    rw [Nat.mul_succ, Exp_int_add, Exp_int]
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    rw [ih]

-- LLM HELPER
lemma Exp_int_2_pos (n : Nat) : Exp_int 2 n > 0 := by
  induction n with
  | zero => simp [Exp_int]
  | succ n ih =>
    rw [Exp_int]
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    omega

-- LLM HELPER
lemma mod_mul_mod (a b c : Nat) (hc : c > 0) : (a * b) % c = ((a % c) * (b % c)) % c := by
  rw [Nat.mul_mod, Nat.mod_mod_of_dvd, Nat.mul_mod]
  omega
-- </vc-helpers>

-- <vc-spec>
def ModExp_int (x y n z : Nat) : Nat :=
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
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z := by
-- </vc-theorem>
-- <vc-proof>
induction y using Nat.strong_induction_on generalizing x n with
  | ind y ih =>
    unfold ModExp_int
    split_ifs with h0 h_pow
    · -- Case: y = 0
      simp [h0, Exp_int]
    · -- Case: y = 2^n
      rw [ModExpPow2_int_spec]
      · exact h_pow
      · omega
    · -- Case: y > 0 and y ≠ 2^n
      have hy_pos : y > 0 := by
        by_contra h
        simp at h
        omega
      have y_div2_lt : y / 2 < y := Nat.div_lt_self hy_pos (by norm_num)
      have y_div2_bound : y / 2 < Exp_int 2 (n + 1) := Nat.lt_trans y_div2_lt hy
      
      let r := ModExp_int x (y / 2) n z
      have hr : r = Exp_int x (y / 2) % z := ih (y / 2) y_div2_lt x n y_div2_bound hz
      
      split_ifs with h_even
      · -- Case: y is even
        have y_eq : y = 2 * (y / 2) := by
          rw [Nat.mul_comm]
          exact Nat.eq_mul_of_div_eq_right (by norm_num) rfl
        rw [y_eq, Exp_int_add]
        simp [Exp_int, hr]
        rw [mod_mul_mod _ _ z (by omega)]
      · -- Case: y is odd
        have y_eq : y = 2 * (y / 2) + 1 := by
          have : y % 2 = 1 := by
            by_contra h
            have : y % 2 = 0 ∨ y % 2 = 1 := Nat.mod_two_eq_zero_or_one y
            cases this with
            | inl h' => contradiction
            | inr h' => exact h'
          exact Nat.div_add_mod y 2 ▸ (by rw [this]; ring)
        rw [y_eq, Exp_int_add, Exp_int]
        simp only [Nat.sub_self]
        simp [Exp_int, hr]
        rw [mod_mul_mod _ _ z (by omega), mod_mul_mod _ _ z (by omega)]
        ring_nf
-- </vc-proof>

end BignumLean