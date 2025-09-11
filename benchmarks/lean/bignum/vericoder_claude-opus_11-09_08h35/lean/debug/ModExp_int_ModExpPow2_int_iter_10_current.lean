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
def ModExpPow2_int_impl (x y n z : Nat) : Nat :=
  if n = 0 then
    if y = 0 then 1 % z else x % z
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
if hz : z > 0 then
  if hy : y < Exp_int 2 (n + 1) then
    ModExpPow2_int_impl x y n z
  else
    0
else
  0
-- </vc-code>

-- <vc-theorem>
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp_int
simp [hz]
have hz_pos : z > 0 := Nat.lt_trans (Nat.zero_lt_one) hz
simp [hz_pos, hy]
generalize hn : n = n'
rw [← hn] at *
clear hn
induction n' generalizing x y n with
| zero =>
  simp at *
  subst n
  simp [ModExpPow2_int_impl]
  have h1 : y < Exp_int 2 1 := hy
  simp [Exp_int] at h1
  interval_cases y
  · simp [Exp_int]
  · simp [Exp_int_one]
| succ n' ih =>
  simp at *
  subst n
  simp [ModExpPow2_int_impl]
  split_ifs with h
  · subst y
    simp [Exp_int]
  · split_ifs with heven
    · have y_div_bound : y / 2 < Exp_int 2 (n' + 1) := by
        have : y < Exp_int 2 (n' + 1 + 1) := hy
        rw [Exp_int_2_succ] at this
        omega
      have half_eq := ih x (y / 2) n' y_div_bound rfl
      rw [half_eq]
      have y_even : ∃ k, y = 2 * k := by
        use y / 2
        omega
      obtain ⟨k, hk⟩ := y_even
      rw [hk]
      simp [Exp_int_add, Exp_int]
      rw [Nat.pow_mod, Nat.mul_mod, Nat.mul_mod]
    · have y_div_bound : y / 2 < Exp_int 2 (n' + 1) := by
        have : y < Exp_int 2 (n' + 1 + 1) := hy
        rw [Exp_int_2_succ] at this
        omega
      have half_eq := ih x (y / 2) n' y_div_bound rfl
      rw [half_eq]
      have y_odd : ∃ k, y = 2 * k + 1 := by
        use y / 2
        omega
      obtain ⟨k, hk⟩ := y_odd
      rw [hk]
      simp [Exp_int_add, Exp_int]
      rw [Nat.pow_mod, Nat.mul_mod, Nat.mul_mod, Nat.mul_mod]
      ring_nf
-- </vc-proof>

end BignumLean