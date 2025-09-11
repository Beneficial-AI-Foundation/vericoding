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
lemma Exp_int_add (x y z : Nat) : Exp_int x (y + z) = Exp_int x y * Exp_int x z := by
  induction z generalizing y with
  | zero => simp [Exp_int]
  | succ z' ih =>
    rw [Nat.add_succ, Exp_int_succ, ih]
    rw [Exp_int_succ]
    ring

-- LLM HELPER
lemma Exp_int_2_zero : Exp_int 2 0 = 1 := by
  simp [Exp_int]

-- LLM HELPER  
lemma Exp_int_2_succ (n : Nat) : Exp_int 2 (n + 1) = 2 * Exp_int 2 n := by
  simp [Exp_int_succ]
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
    have hsub : n' + 1 - 1 = n' := Nat.sub_eq n'.succ 1
    rw [hsub]
    rw [ih x (Exp_int 2 n') rfl hz]
    have hexp : Exp_int x (2 * Exp_int 2 n') = Exp_int x (Exp_int 2 n') * Exp_int x (Exp_int 2 n') := by
      have h1 : 2 * Exp_int 2 n' = Exp_int 2 n' + Exp_int 2 n' := by ring
      rw [h1]
      rw [Exp_int_add]
    rw [hexp]
    rw [Nat.mul_mod, Nat.mod_mod, Nat.mul_mod]
-- </vc-proof>

end BignumLean