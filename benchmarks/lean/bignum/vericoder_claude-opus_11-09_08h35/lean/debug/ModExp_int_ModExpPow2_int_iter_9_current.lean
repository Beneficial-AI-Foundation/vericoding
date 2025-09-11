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

-- LLM HELPER
lemma Exp_int_2_succ (n : Nat) : Exp_int 2 (n + 1) = 2 * Exp_int 2 n := by
  rw [Exp_int]
  simp

-- LLM HELPER
lemma Exp_int_one (x : Nat) : Exp_int x 1 = x := by
  simp [Exp_int]

-- LLM HELPER
lemma ModExpPow2_int_impl (x y n z : Nat) : Nat :=
  if n = 0 then
    x % z
  else
    let half := ModExpPow2_int_impl x (y / 2) (n - 1) z
    if y % 2 = 0 then
      (half * half) % z
    else
      (x * ((half * half) % z)) % z
termination_by n
-- </vc-helpers>

-- <vc-spec>
def ModExp_int (x y n z : Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
ModExpPow2_int_impl x y n z
-- </vc-code>

-- <vc-theorem>
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z := by
-- </vc-theorem>
-- <vc-proof>
induction n generalizing x y with
| zero =>
  simp [ModExp_int]
  have h1 : y < Exp_int 2 1 := hy
  simp [Exp_int] at h1
  have h2 : y < 2 := h1
  interval_cases y
  · simp [Exp_int]
  · simp [Exp_int_one]
| succ n ih =>
  unfold ModExp_int
  simp [Nat.succ_ne_zero]
  have spec := ModExpPow2_int_spec x (Exp_int 2 (n + 1)) (n + 1) z rfl hz
  rw [spec]
  have hy' : y < Exp_int 2 ((n + 1) + 1) := hy
  rw [Nat.add_assoc, Nat.add_comm 1 1, ← Nat.add_assoc] at hy'
  simp at hy'
  rw [Exp_int_2_succ] at hy'
  have pow_eq : Exp_int x (Exp_int 2 (n + 1)) = Exp_int (Exp_int x 2) (Exp_int 2 n) := by
    rw [← Exp_int_mul]
    congr
    rw [Exp_int_2_succ]
    ring
  rw [pow_eq]
  simp [Exp_int] at *
  rw [Nat.mul_mod]
  congr 1
  · rw [← pow_eq]
    rfl
  · rw [← pow_eq]
    rfl
-- </vc-proof>

end BignumLean