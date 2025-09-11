namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
theorem nat_eq_zero_or_one_of_lt_two (n : Nat) (h : n < 2) : n = 0 ∨ n = 1 := by
  cases n with
  | zero => left; rfl
  | succ n' =>
    cases n' with
    | zero => right; rfl
    | succ _ =>
      have two_le : 2 ≤ succ (succ n') := by
        apply Nat.succ_le_succ; apply Nat.succ_le_succ; apply Nat.zero_le
      linarith

-- LLM HELPER
theorem Exp_int_pow_double (x : Nat) : ∀ k, Exp_int (x * x) k = Exp_int x (2 * k) := by
  intro k
  induction k with
  | zero =>
    dsimp [Exp_int]; rfl
  | succ k ih =>
    -- Exp_int (x*x) (k+1) = (x*x) * Exp_int (x*x) k
    have hleft : Exp_int (x * x) (k + 1) = (x * x) * Exp_int (x * x) k := by dsimp [Exp_int]; rfl
    rw [hleft, ih]
    -- Now goal: (x*x) * Exp_int x (2*k) = Exp_int x (2*(k+1))
    dsimp [Exp_int] -- expands RHS to x * Exp_int x (2*k + 1)
    -- Exp_int x (2*k + 1) = x * Exp_int x (2*k) by definition
    dsimp [Exp_int] at *
    rfl

-- LLM HELPER
theorem Exp_int_mod_base (a z : Nat) : ∀ k, Exp_int (a % z) k % z = Exp_int a k % z := by
  intro k
  induction k with
  | zero =>
    dsimp [Exp_int]; rfl
  | succ k ih =>
    dsimp [Exp_int]
    -- LHS: ((a % z) * Exp_int (a % z) k) % z
    -- RHS: (a * Exp_int a k) % z
    -- Use property (a * b) % z = ((a % z) * (b % z)) % z and IH to relate factors
    have mod_mul : (a * Exp_int a k) % z = ((a % z) * (Exp_int a k % z)) % z := by
      -- this follows from the general multiplicative mod property
      exact Nat.mul_mod a (Exp_int a k) z
    -- replace RHS with version reduced factors
    rw [←mod_mul]
    -- use IH to replace (Exp_int a k % z) with (Exp_int (a % z) k % z)
    rw [ih]
    -- Now RHS is ((a % z) * (Exp_int (a % z) k % z)) % z
    -- but (x * (y % z)) % z = (x * y) % z, so this equals LHS
    have mul_right_mod : ((a % z) * (Exp_int (a % z) k % z)) % z = ((a % z) * Exp_int (a % z) k) % z := by
      -- use Nat.mul_mod to move the modulus on the right factor (equationally)
      exact (by
        -- Using the identity (x * (y % m)) % m = (x * y) % m which is a specialization of Nat.mul_mod
        rw [Nat.mul_mod (a % z) (Exp_int (a % z) k) z])
    rw [←mul_right_mod]
    rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp_int (x y n z : Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
def ModExp_int (x y n z : Nat) : Nat :=
  match n with
  | 0 =>
    if y = 0 then 1 % z else x % z
  | Nat.succ n' =>
    let y1 := y / 2
    let r := ModExp_int ((x * x) % z) y1 n' z
    if y % 2 = 1 then (x % z * r) % z else r
-- </vc-code>

-- <vc-theorem>
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z :=
-- </vc-theorem>
-- <vc-proof>
by
  induction n generalizing x y z with
  | zero =>
    dsimp [ModExp_int]
    -- Exp_int 2 1 = 2, so y < 2
    have hE : Exp_int 2 1 = 2 := by dsimp [Exp_int]; rfl
    have hy2 : y < 2 := by rwa [←hE] at hy
    cases y with
    | zero =>
      dsimp [ModExp_int, Exp_int]; rfl
    | succ y' =>
      cases y' with
      | zero =>
        dsimp [ModExp_int, Exp_int]; rfl
      | succ _ =>
        -- y ≥ 2 contradicts y < 2
        have two_le : 2 ≤ succ (succ y') := by
          apply Nat.succ_le_succ; apply Nat.succ_le_succ; apply Nat.zero_le
        linarith
  | succ k ih =>
    intro x y z hy hz
    dsimp [ModExp_int]
    let y1 := y / 2
    -- Exp_int 2 (k+2) = 2 * Exp_int 2 (k+1)
    have two_pow_step : Exp_int 2 (k + 2) = 2 * Exp_int 2 (k + 1) := by dsimp [Exp_int]; rfl
    -- hy : y < Exp_int 2 (k+2) = 2 * Exp_int 2 (k+1)
    have y_lt : y < 2 * Exp_int 2 (k + 1) := by rwa [←two_pow_step] at hy
    -- use div_add_mod to connect y, y1, and y % 2
    have y_div_mod := Nat.div_add_mod y 2
    have two_y1_le_y : 2 * y1 ≤ y := by
      rw [y_div_mod]; apply Nat.le_add_right
    have two_y1_lt : 2 * y1 < 2 * Exp_int 2 (k + 1) := by
      calc
        2 * y1 ≤ y := two_y1_le_y
        _ < 2 * Exp_int 2 (k + 1) := y_lt
    have y1_lt : y1 < Exp_int 2 (k + 1) := by
      have hpos : 0 < 2 := by decide
      exact Nat.lt_of_mul_lt_mul_left two_y1_lt hpos
    -- apply induction hypothesis to compute r
    have rec_eq := ih ((x * x) % z) y1 z y1_lt hz
    -- handle parity cases of y % 2
    have mod_lt_two : y % 2 < 2 := Nat.mod_lt y (by decide)
    have mod_cases := nat_eq_zero_or_one_of_lt_two (y % 2) mod_lt_two
    cases mod_cases with
    | inl hmod0 =>
      have y_is : y = 2 * y1 := by
        rw [y_div_mod, hmod0]; simp
      calc
        ModExp_int x y (k + 1) z
            = ModExp_int ((x * x) % z) y1 k z := by
          dsimp [ModExp_int]; simp [hmod0]
        _ = Exp_int ((x * x) % z) y1 % z := by rw [rec_eq]
        _ = Exp_int (x * x) y1 % z := by rw [Exp_int_mod_base (x * x) z y1]
        _ = Exp_int x (2 * y1) % z := by rw [Exp_int_pow_double x y1]
        _ = Exp_int x y % z := by rw [y_is]
    | inr hmod1 =>
      have y_is : y = 2 * y1 + 1 := by
        rw [y_div_mod, hmod1]; simp
      calc
        ModExp_int x y (k + 1) z
            = (x % z * (ModExp_int ((x * x) % z) y1 k z)) % z := by
          dsimp [ModExp_int]; simp [hmod1]
        _ = (x % z * (Exp_int ((x * x) % z) y1 % z)) % z := by rw [rec_eq]
        _ = (x % z * (Exp_int (x * x) y1 % z)) % z := by rw [Exp_int_mod_base (x * x) z y1]
        _ = (x % z * (Exp_int x (2 * y1) % z)) % z := by rw [Exp_int_pow_double x y1]
        _ = (x * Exp_int x (2 * y1)) % z := by
          -- use multiplicative modulo identity to change the reduced factors to the full product
          have h := Nat.mul_mod x (Exp_int x (2 * y1)) z
          rw [←h]
        _ = Exp_int x (2 * y1 + 1) % z := by dsimp [Exp_int]; rfl
        _ = Exp_int x y % z := by rw [y_is]
-- </vc-proof>

end BignumLean