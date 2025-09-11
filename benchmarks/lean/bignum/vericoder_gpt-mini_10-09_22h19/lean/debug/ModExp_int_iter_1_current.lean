namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
theorem Exp_int_pow_double (x : Nat) : ∀ k, Exp_int (x * x) k = Exp_int x (2 * k)
| 0 => by
  simp [Exp_int]
  rfl
| k+1 => by
  simp [Exp_int]
  have IH := Exp_int_pow_double x k
  -- Exp_int (x*x) (k+1) = (x*x) * Exp_int (x*x) k
  -- = (x*x) * Exp_int x (2*k) = Exp_int x (2*k + 2) = Exp_int x (2*(k+1))
  calc
    Exp_int (x * x) (k + 1) = (x * x) * Exp_int (x * x) k := by simp [Exp_int]
    _ = (x * x) * Exp_int x (2 * k) := by rw [IH]
    _ = x * (x * Exp_int x (2 * k)) := by simp [mul_assoc]
    _ = x * Exp_int x (2 * k + 1) := by
      -- show x * Exp_int x (2*k) = x * Exp_int x (2*k) (trivial),
      -- but we need to relate to Exp_int x (2*k + 1) via definition:
      -- Exp_int x (2*k + 1) = x * Exp_int x (2*k)
      simp [Exp_int]
    _ = Exp_int x (2 * (k + 1)) := by
      -- Exp_int x (2*(k+1)) = Exp_int x (2*k + 2) = x * Exp_int x (2*k + 1)
      simp [Exp_int]
      rfl

-- LLM HELPER
theorem Exp_int_mod_base (a z : Nat) : ∀ k, Exp_int (a % z) k % z = Exp_int a k % z
| 0 => by
  simp [Exp_int]
  rfl
| k+1 => by
  simp [Exp_int]
  -- We use the multiplicative property of mod:
  -- (a * b) % z = (a % z * b % z) % z
  have IH := Exp_int_mod_base a z k
  calc
    (a % z * Exp_int (a % z) k) % z
        = (a % z * (Exp_int (a % z) k % z)) % z := by
      -- b % z ≡ b (mod z), so replacing b by b%z under multiplication before a final %z is ok
      congr
      rfl
    _ = (a % z * (Exp_int a k % z)) % z := by rw [IH]
    _ = (a * Exp_int a k) % z := by
      -- Use Nat.mul_mod: (a * b) % z = (a % z * b % z) % z.
      -- Here rewrite the RHS of that lemma to get the needed equality.
      calc
        (a * Exp_int a k) % z = (a % z * (Exp_int a k % z)) % z := by
          apply Nat.mul_mod
        _ = (a % z * (Exp_int a k % z)) % z := rfl
    _ = Exp_int a (k + 1) % z := by simp [Exp_int]
-- </vc-helpers>

-- <vc-spec>
def ModExp_int (x y n z : Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
def ModExp_int (x y n z : Nat) : Nat :=
  if n = 0 then
    if y = 0 then 1 % z else x % z
  else
    let y1 := y / 2
    let rec := ModExp_int ((x * x) % z) y1 (n - 1) z
    if y % 2 = 1 then (x % z * rec) % z else rec
-- </vc-code>

-- <vc-theorem>
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z := by
  induction
-- </vc-theorem>
end BignumLean