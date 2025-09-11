namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
lemma exp_int_power_mult (x a b : Nat) : Exp_int x (a * b) = Exp_int (Exp_int x a) b := by
  induction b generalizing a with
  | zero => 
    simp [Exp_int]
  | succ b' ih =>
    unfold Exp_int
    split_ifs with h
    · contradiction
    · rw [Nat.mul_succ, ih, Nat.add_sub_cancel]
      unfold Exp_int
      split_ifs with h2
      · simp at h2
      · rfl

-- LLM HELPER  
lemma exp_int_two_succ (n : Nat) : Exp_int 2 (n + 1) = 2 * Exp_int 2 n := by
  unfold Exp_int
  split_ifs with h
  · contradiction
  · rw [Nat.add_sub_cancel]
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
    simp
    rw [hy]
    unfold Exp_int
    simp
  | succ n' ih =>
    unfold ModExpPow2_int
    split_ifs with h
    · contradiction
    · have hsub : n' + 1 - 1 = n' := Nat.add_sub_cancel n' 1
      rw [hsub]
      have h2 : Exp_int 2 n' = Exp_int 2 n' := rfl
      rw [ih x (Exp_int 2 n') h2]
      rw [hy]
      rw [exp_int_two_succ]
      have : Exp_int x (2 * Exp_int 2 n') = (Exp_int x (Exp_int 2 n'))^2 := by
        rw [← exp_int_power_mult]
        unfold Exp_int
        split_ifs with h1
        · simp at h1
          rw [h1]
          unfold Exp_int
          simp
        · rw [Nat.mul_sub_left_distrib]
          simp
          unfold Exp_int
          split_ifs with h2
          · contradiction
          · simp [Nat.pow_two]
      rw [this]
      simp [Nat.pow_two]
      rw [Nat.mul_mod]
-- </vc-proof>

end BignumLean