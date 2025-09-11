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
  · simp [Exp_int]
    rw [Nat.mul_comm]
    rw [Nat.mul_mod_left]
    rfl
| succ n ih =>
  unfold ModExp_int
  split_ifs with hn
  · subst hn
    simp [Exp_int] at hy
    interval_cases y
    simp [Exp_int]
  · have hs : n.succ - 1 = n := Nat.succ_sub_one
    rw [hs]
    rw [ModExpPow2_int_spec]
    · have hmod : Exp_int x (Exp_int 2 n) % z * (Exp_int x (Exp_int 2 n) % z) = 
            (Exp_int x (Exp_int 2 n) * Exp_int x (Exp_int 2 n)) % z := by
        rw [mod_mul_mod]
        omega
      rw [hmod]
      rw [← Exp_int_add]
      have h2n : Exp_int 2 n + Exp_int 2 n = 2 * Exp_int 2 n := by ring
      rw [h2n]
      rw [Exp_int_mul]
      simp [Exp_int]
      rw [Exp_int_2_succ]
      have hy' : y < Exp_int 2 (n + 1) + Exp_int 2 (n + 1) := by
        rw [Exp_int_2_succ] at hy
        omega
      rw [← h2n] at hy'
      rw [← Exp_int_add] at hy'
      have : y = Exp_int 2 (n + 1) := by
        rw [Exp_int_2_succ] at hy
        omega
      rw [this]
      rfl
    · rfl
    · omega
-- </vc-proof>

end BignumLean