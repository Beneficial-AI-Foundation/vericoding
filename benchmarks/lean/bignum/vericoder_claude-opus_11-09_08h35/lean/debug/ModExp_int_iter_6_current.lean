namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
lemma exp_int_zero (x : Nat) : Exp_int x 0 = 1 := by
  simp [Exp_int]

-- LLM HELPER  
lemma exp_int_succ (x y : Nat) (hy : y > 0) : Exp_int x y = x * Exp_int x (y - 1) := by
  simp [Exp_int, ne_of_gt hy]

-- LLM HELPER
lemma mod_mul_mod (a b n : Nat) (hn : n > 0) : (a * b) % n = ((a % n) * (b % n)) % n := by
  rw [Nat.mul_mod, Nat.mul_mod]
-- </vc-helpers>

-- <vc-spec>
def ModExp_int (x y n z : Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
if y = 0 then 1 % z
else (x % z * ModExp_int x (y - 1) n z) % z
termination_by y
-- </vc-code>

-- <vc-theorem>
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z := by
-- </vc-theorem>
-- <vc-proof>
induction y using Nat.strong_induction_on with
| _ y ih =>
  unfold ModExp_int
  by_cases h : y = 0
  · simp [h, Exp_int]
  · have hy_pos : y > 0 := Nat.pos_of_ne_zero h
    simp [h]
    rw [exp_int_succ x y hy_pos]
    have ih_apply : ModExp_int x (y - 1) n z = Exp_int x (y - 1) % z := by
      apply ih
      · exact Nat.sub_lt hy_pos (Nat.zero_lt_one)
      · calc y - 1 < y := Nat.sub_lt hy_pos Nat.zero_lt_one
             _ < Exp_int 2 (n + 1) := hy
    rw [ih_apply]
    rw [mod_mul_mod]
    · rw [Nat.mul_mod]
    · exact Nat.zero_lt_of_lt hz
-- </vc-proof>

end BignumLean