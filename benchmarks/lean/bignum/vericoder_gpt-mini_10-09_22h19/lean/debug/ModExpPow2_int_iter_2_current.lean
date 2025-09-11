namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
def modexp_pow2_aux (x n z : Nat) : Nat :=
  match n with
  | 0     => x % z
  | k+1   => let t := modexp_pow2_aux x k z; (t * t) % z

theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  induction b with
  | zero => simp [Exp_int]
  | succ b ih =>
    simp [Exp_int, Nat.add_succ]
    calc
      Exp_int x (a + b + 1) = x * Exp_int x (a + b) := by simp [Exp_int, Nat.add_comm a b]; rfl
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = Exp_int x a * (x * Exp_int x b) := by rw [mul_assoc]
      _ = Exp_int x a * Exp_int x (b + 1) := by simp [Exp_int]
      -- end

theorem Exp_int_two_succ (k : Nat) : Exp_int 2 (k+1) = 2 * Exp_int 2 k := by
  simp [Exp_int]

theorem modexp_pow2_aux_spec (x n z : Nat) (hz : z > 0) :
  modexp_pow2_aux x n z = Exp_int x (Exp_int 2 n) % z := by
  induction n with
  | zero =>
    simp [modexp_pow2_aux, Exp_int]
  | succ k ih =>
    simp [modexp_pow2_aux]
    -- modexp_pow2_aux x (k+1) z = (modexp_pow2_aux x k z * modexp_pow2_aux x k z) % z
    -- apply IH to both occurrences and use multiplication modulo lemma
    have step1 : (modexp_pow2_aux x k z * modexp_pow2_aux x k z) % z =
                 (Exp_int x (Exp_int 2 k) % z * Exp_int x (Exp_int 2 k) % z) % z := by
      rw [ih]
    rw [step1]
    -- use Nat.mul_mod to move % out (a*b) % n = (a%n * b) % n, twice gets desired form
    -- There is a standard lemma: (a * b) % n = ((a % n) * (b % n)) % n,
    -- Lean's core provides Nat.mul_mod which rewrites (a * b) % n = (a % n * b) % n.
    -- We use it to combine reductions.
    have mul_mod1 : (Exp_int x (Exp_int 2 k) % z * Exp_int x (Exp_int 2 k) % z) % z =
                    (Exp_int x (Exp_int 2 k) * (Exp_int x (Exp_int 2 k) % z)) % z := by
      -- rewrite using Nat.mul_mod: (a * b) % n = (a % n * b) % n
      rw [Nat.mul_mod (Exp_int x (Exp_int 2 k)) (Exp_int x (Exp_int 2 k) % z) z]
      -- the RHS becomes ((Exp_int x (Exp_int 2 k)) % z * (Exp_int x (Exp_int 2 k) % z)) % z
      -- but that's the same as the LHS, so this rewrite suffices
      simp
    -- Now move the remaining % similarly
    have mul_mod2 : (Exp_int x (Exp_int 2 k) * (Exp_int x (Exp_int 2 k) % z)) % z =
                    (Exp_int x (Exp_int 2 k) * Exp_int x (Exp_int 2 k)) % z := by
      rw [Nat.mul_mod (Exp_int x (Exp_int 2 k)) (Exp_int x (Exp_int 2 k)) z]
      simp
    rw [mul_mod1, mul_mod2]
    -- combine with exponent addition: x^(m) * x^(m) = x^(m + m)
    have add_exp : Exp_int x (Exp_int 2 k) * Exp_int x (Exp_int 2 k) =
                   Exp_int x (Exp_int 2 k + Exp_int 2 k) := by
      rw [Exp_int_add]
    rw [add_exp]
    -- finally, Exp_int 2 (k+1) = 2 * Exp_int 2 k = Exp_int 2 k + Exp_int 2 k
    calc
      Exp_int x (Exp_int 2 k + Exp_int 2 k) % z = Exp_int x (Exp_int 2 (k+1)) % z := by
        -- Exp_int 2 (k+1) = 2 * Exp_int 2 k = Exp_int 2 k + Exp_int 2 k
        have h := Exp_int_two_succ k
        simp [h, Nat.add_comm]
        rfl

-- End helpers
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2_int (x y n z : Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
def ModExpPow2_int (x y n z : Nat) : Nat :=
  if h0 : z = 0 then 0
  else if h1 : y = Exp_int 2 n then
    -- when y = 2^n, compute x^(2^n) mod z by repeated squaring
    modexp_pow2_aux x n z
  else
    x % z
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_int_spec (x y n z : Nat) (hy : y = Exp_int 2 n) (hz : z > 0) :
  ModExpPow2_int x y n z = Exp_int x y % z := by
-- </vc-theorem>
-- <vc-proof>
-- Unfold definition and use hy and hz to reduce to modexp_pow2_aux_spec
  dsimp [ModExpPow2_int]
  -- z > 0 implies z ≠ 0
  have nz : z ≠ 0 := by
    intro hz0
    subst hz0
    simp at hz
    exact hz
  simp [nz, hy]
  -- now the result is modexp_pow2_aux x n z; apply the lemma
  apply modexp_pow2_aux_spec
  exact hz
-- </vc-proof>

end BignumLean