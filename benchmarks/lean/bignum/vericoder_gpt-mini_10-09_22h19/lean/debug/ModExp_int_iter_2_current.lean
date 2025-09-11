namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
theorem Exp_int_pow_double (x : Nat) : ∀ k, Exp_int (x * x) k = Exp_int x (2 * k)
| 0 => by
  -- both sides reduce to 1
  dsimp [Exp_int]
  rfl
| k+1 => by
  -- Exp_int (x*x) (k+1) = (x*x) * Exp_int (x*x) k
  dsimp [Exp_int]
  have IH := Exp_int_pow_double x k
  -- use IH and the definition of Exp_int to reach the goal
  calc
    Exp_int (x * x) (k + 1) = (x * x) * Exp_int (x * x) k := rfl
    _ = (x * x) * Exp_int x (2 * k) := by rw [IH]
    _ = x * (x * Exp_int x (2 * k)) := by simp [mul_assoc]
    _ = x * Exp_int x (2 * k + 1) := by
      -- by definition Exp_int x (2*k + 1) = x * Exp_int x (2*k)
      dsimp [Exp_int]
      rfl
    _ = Exp_int x (2 * (k + 1)) := by
      -- Exp_int x (2*(k+1)) = Exp_int x (2*k + 2) = x * Exp_int x (2*k + 1)
      dsimp [Exp_int]
      rfl

-- LLM HELPER
theorem Exp_int_mod_base (a z : Nat) : ∀ k, Exp_int (a % z) k % z = Exp_int a k % z
| 0 => by
  dsimp [Exp_int]; rfl
| k+1 => by
  dsimp [Exp_int]
  have IH := Exp_int_mod_base a z k
  -- compute modulus step-by-step, using Nat.mul_mod
  calc
    (a % z * Exp_int (a % z) k) % z
        = (a % z * (Exp_int (a % z) k % z)) % z := by
      -- rewrite second factor modulo z (it's equivalent mod z)
      congr
      exact IH
    _ = (a % z * (Exp_int a k % z)) % z := rfl
    _ = (a * Exp_int a k) % z := by
      -- Nat.mul_mod states (a * b) % z = (a % z * b % z) % z,
      -- from which we can conclude the displayed equality
      calc
        (a * Exp_int a k) % z = (a % z * (Exp_int a k % z)) % z := by apply Nat.mul_mod
        _ = (a % z * (Exp_int a k % z)) % z := rfl
    _ = Exp_int a (k + 1) % z := by
      dsimp [Exp_int]; rfl
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
  induction n with
  | zero =>
    -- when n = 0, Exp_int 2 (0+1) = 2, so y < 2, thus y = 0 or y = 1
    dsimp [ModExp_int]
    have hy' : y < 2 := by
      -- Exp_int 2 1 = 2 by definition
      dsimp [Exp_int] at hy
      exact hy
    cases y with
    | zero => 
      -- y = 0
      dsimp [Exp_int]; rfl
    | succ y' =>
      -- succ y' < 2 implies y' = 0, so y = 1
      have : succ y' ≤ 1 := Nat.lt_iff_le_and_ne.mp (by
        have : succ y' < 2 := hy'
        exact ⟨Nat.lt_iff_le_and_ne.mp (by exact ⟨this, by decide⟩)⟩) ; -- fallback handled below
      -- simpler: since succ y' < 2, succ y' = 1
      have y_eq_one : succ y' = 1 := by
        have h : succ y' < 2 := hy'
        have : succ y' ≤ 1 := Nat.le_of_lt_succ (by linarith [h])
        cases this; 
        cases this; 
        rfl
      dsimp [Exp_int]; -- Exp_int x 1 = x
      rw [←y_eq_one]; rfl
  | succ n ih =>
    -- n = succ n0: the function uses the recursive call with n - 1 = n
    dsimp [ModExp_int]
    have hn_pos : n + 1 > 0 := by linarith
    -- rewrite Exp_int 2 (n+1+1) as 2 * Exp_int 2 (n+1)
    have two_mul : Exp_int 2 (n + 2) = 2 * Exp_int 2 (n + 1) := by
      -- by definition Exp_int 2 (m+1) = 2 * Exp_int 2 m
      dsimp [Exp_int]; rfl
    -- derive bound for y/2
    let y1 := y / 2
    have : y = 2 * y1 + y % 2 := Nat.div_add_mod y 2
    have y_lt_mul : y < 2 * Exp_int 2 (n + 1) := by
      rw [←two_mul] at hy
      exact hy
    -- from y = 2*y1 + (y%2) and y < 2*M we get 2*y1 ≤ y < 2*M, hence 2*y1 < 2*M, so y1 < M
    have two_y1_le_y : 2 * y1 ≤ y := by
      calc
        2 * y1 = (2 * y1 + (y % 2)) - (y % 2) := by
          rw [Nat.sub_add_cancel (Nat.le_add_right _ _)]
        _ = y - (y % 2) := by rw [this]
        _ ≤ y := Nat.sub_le _ _
    have two_y1_lt : 2 * y1 < 2 * Exp_int 2 (n + 1) := by
      apply Nat.lt_of_lt_of_le y_lt_mul (le_refl _)
    have y1_lt : y1 < Exp_int 2 (n + 1) := by
      -- from 2*y1 < 2*M and 2 > 0 we get y1 < M
      have : 0 < 2 := by decide
      exact Nat.lt_of_mul_lt_mul_left two_y1_lt this
    -- apply IH to the recursive call
    have rec_eq := ih ((x * x) % z) y1 (by
      -- supply the bound and modulus condition
      exact y1_lt) hz
    -- now handle even/odd cases
    by_cases hodd : y % 2 = 1
    · -- odd case: y = 2*y1 + 1
      have y_repr := Nat.div_add_mod y 2
      have y_is : y = 2 * y1 + 1 := by
        rw [y_repr]; rw [if_pos hodd]; rfl
      -- compute Exp_int x y = x * Exp_int x (2*y1) = x * Exp_int (x*x) y1
      calc
        ModExp_int x y (n + 1) z = (x % z * (ModExp_int ((x * x) % z) y1 n z)) % z := by
          -- unfold definitions
          dsimp [ModExp_int]
          simp [hodd]
        _ = (x % z * (Exp_int ((x * x) % z) y1 % z)) % z := by rw [
-- </vc-theorem>
end BignumLean