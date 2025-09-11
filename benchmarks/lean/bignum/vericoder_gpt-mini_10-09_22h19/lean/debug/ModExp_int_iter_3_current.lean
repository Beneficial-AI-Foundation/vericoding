namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

-- <vc-helpers>
-- LLM HELPER
theorem Exp_int_pow_double (x : Nat) : ∀ k, Exp_int (x * x) k = Exp_int x (2 * k)
| 0 => by
  dsimp [Exp_int]; rfl
| k+1 => by
  dsimp [Exp_int]
  have IH := Exp_int_pow_double x k
  -- Exp_int (x*x) (k+1) = (x*x) * Exp_int (x*x) k
  calc
    Exp_int (x * x) (k + 1) = (x * x) * Exp_int (x * x) k := rfl
    _ = (x * x) * Exp_int x (2 * k) := by rw [IH]
    _ = x * (x * Exp_int x (2 * k)) := by simp [mul_assoc]
    _ = x * Exp_int x (2 * k + 1) := by
      -- by definition Exp_int x (2*k + 1) = x * Exp_int x (2*k)
      dsimp [Exp_int]; rfl
    _ = Exp_int x (2 * (k + 1)) := by
      -- 2*(k+1) = 2*k + 2 and Exp_int x (2*k + 2) = x * Exp_int x (2*k + 1)
      dsimp [Exp_int]; rfl

-- LLM HELPER
theorem Exp_int_mod_base (a z : Nat) : ∀ k, Exp_int (a % z) k % z = Exp_int a k % z
| 0 => by
  dsimp [Exp_int]; rfl
| k+1 => by
  dsimp [Exp_int]
  have IH := Exp_int_mod_base a z k
  calc
    (a % z * Exp_int (a % z) k) % z
        = (a % z * (Exp_int (a % z) k % z)) % z := by
      -- replace second factor by its congruent mod z value
      congr
      exact IH
    _ = (a % z * (Exp_int a k % z)) % z := rfl
    _ = (a * Exp_int a k) % z := by
      -- nat.mul_mod: (a * b) % z = (a % z * b % z) % z
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
    have hy2 : y < 2 := by
      -- Exp_int 2 1 = 2
      dsimp [Exp_int] at hy
      exact hy
    cases y with
    | zero => 
      -- y = 0
      dsimp [Exp_int]; rfl
    | succ y' =>
      -- y = 1 is the only possibility
      cases y' with
      | zero =>
        -- y = 1
        dsimp [Exp_int]; rfl
      | succ y'' =>
        -- succ (succ y'') < 2 impossible
        have : succ (succ y'') < 2 := hy2
        have : 2 ≤ succ (succ y'') := by
          apply Nat.succ_le_succ; apply Nat.succ_le_succ; apply Nat.zero_le
        linarith
  | succ n ih =>
    -- n is the predecessor; original parameter is succ n
    dsimp [ModExp_int]
    let y1 := y / 2
    -- bound on y gives bound on y1
    have two_pow : Exp_int 2 (n + 2) = 2 * Exp_int 2 (n + 1) := by
      dsimp [Exp_int]; rfl
    have y_lt : y < 2 * Exp_int 2 (n + 1) := by
      rw [←two_pow] at hy
      exact hy
    have y_div_mod := Nat.div_add_mod y 2
    have two_y1_le_y : 2 * y1 ≤ y := by
      rw [y_div_mod]; apply Nat.le_add_right
    have two_y1_lt : 2 * y1 < 2 * Exp_int 2 (n + 1) := by
      calc
        2 * y1 ≤ y := two_y1_le_y
        _ < 2 * Exp_int 2 (n + 1) := y_lt
    have y1_lt : y1 < Exp_int 2 (n + 1) := by
      have hpos : 0 < 2 := by decide
      exact Nat.lt_of_mul_lt_mul_left two_y1_lt hpos
    -- apply IH to recursive call
    have rec_eq := ih ((x * x) % z) y1 (by exact y1_lt) hz
    by_cases hodd : y % 2 = 1
    · -- odd case: y = 2*y1 + 1
      have y_repr := Nat.div_add_mod y 2
      have y_is : y = 2 * y1 + 1 := by
        rw [y_repr]; rw [if_pos hodd]; rfl
      -- compute ModExp_int and reduce using rec_eq and helpers
      calc
        ModExp_int x y (n + 1) z
            = (x % z * (ModExp_int ((x * x) % z) y1 n z)) % z := by
          dsimp [ModExp_int]; simp [hodd]
        _ = (x % z * (Exp_int ((x * x) % z) y1 % z)) % z := by rw [rec_eq]
        _ = (x % z * (Exp_int (x * x) y1 % z)) % z := by
          -- replace a%z base with a using Exp_int_mod_base
          have := Exp_int_mod_base (x * x) z y1
          rw [←this]
        _ = (x % z * (Exp_int x (2 * y1) % z)) % z := by
          rw [Exp_int_pow_double x y1]
        _ = (x * Exp_int x (2 * y1)) % z := by
          -- use nat.mul_mod: (a * b) % z = (a % z * b % z) % z
          calc
            (x * Exp_int x (2 * y1)) % z = (x % z * (Exp_int x (2 * y1) % z)) % z := by apply Nat.mul_mod
            _ = (x % z * (Exp_int x (2 * y1) % z)) % z := rfl
        _ = Exp_int x (2 * y1 + 1) % z := by
          dsimp [Exp_int]; rfl
        _ = Exp_int x y % z := by rw [y_is]
    · -- even case: y = 2*y1
      have y_repr := Nat.div_add_mod y 2
      have y_is : y = 2 * y1 := by
        rw [y_repr]; rw [if_neg hodd]; rfl
      calc
        ModExp_int x y (n + 1) z
            = ModExp_int ((x * x) % z) y1 n z := by
          dsimp [ModExp_int]; simp [hodd]
        _ = Exp_int ((x * x) % z) y1 % z := by rw [rec_eq]
        _ = Exp_int (x * x) y1 % z := by
          have := Exp_int_mod_base (x * x) z y1
          rw [←this]
        _ = Exp_int x (2 * y1) % z := by rw [Exp_int_pow_double x y1]
        _ = Exp_int x y % z := by rw [y_is]
-- </vc-theorem>
end BignumLean