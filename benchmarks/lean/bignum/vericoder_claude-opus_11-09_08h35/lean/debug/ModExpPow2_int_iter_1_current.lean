namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
lemma Exp_int_zero (x : Nat) : Exp_int x 0 = 1 := by
  simp [Exp_int]

-- LLM HELPER
lemma Exp_int_succ (x y : Nat) : Exp_int x (y + 1) = x * Exp_int x y := by
  simp [Exp_int, Nat.add_sub_cancel]

-- LLM HELPER
lemma Exp_int_mul (x y z : Nat) : Exp_int x (y * z) = Exp_int (Exp_int x y) z := by
  induction z generalizing y with
  | zero => simp [Exp_int]
  | succ z ih =>
    simp [Nat.mul_succ, Exp_int_succ]
    rw [ih]
    cases y with
    | zero => simp [Exp_int]
    | succ y' =>
      simp [Exp_int]
      ring_nf
      rfl

-- LLM HELPER
lemma Exp_int_2_zero : Exp_int 2 0 = 1 := by
  simp [Exp_int]

-- LLM HELPER  
lemma Exp_int_2_succ (n : Nat) : Exp_int 2 (n + 1) = 2 * Exp_int 2 n := by
  simp [Exp_int_succ]

-- LLM HELPER
lemma mod_mod_of_dvd {a b c : Nat} (h : c > 0) (hdvd : c ∣ b) : a % b % c = a % c := by
  cases hdvd with
  | intro k hk =>
    by_cases hb : b = 0
    · simp [hb]
    · have : b > 0 := Nat.pos_of_ne_zero hb
      rw [hk]
      by_cases hk0 : k = 0
      · simp [hk0] at hk
        simp [hk]
      · have : c * k > 0 := Nat.mul_pos h (Nat.pos_of_ne_zero hk0)
        rw [Nat.mod_mod_of_dvd _ _ h]
        exact ⟨k, rfl⟩
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
    have h2n : Exp_int 2 (n' + 1) = 2 * Exp_int 2 n' := by
      rw [Exp_int_2_succ]
    rw [hy, h2n]
    have : n' + 1 - 1 = n' := Nat.sub_eq n'.succ 1
    rw [this]
    rw [ih _ (Exp_int 2 n') rfl hz]
    have : Exp_int x (2 * Exp_int 2 n') = Exp_int x (Exp_int 2 n') * Exp_int x (Exp_int 2 n') := by
      have h1 : 2 * Exp_int 2 n' = Exp_int 2 n' + Exp_int 2 n' := by ring
      rw [h1]
      clear h1 h2n hy ih this
      generalize Exp_int 2 n' = m
      induction m with
      | zero => simp [Exp_int]
      | succ m' ihm =>
        rw [Exp_int_succ, Exp_int_succ]
        rw [← ihm]
        rw [Exp_int_succ]
        ring
    rw [this]
    rw [Nat.mul_mod, Nat.mod_mod, Nat.mul_mod]
-- </vc-proof>

end BignumLean