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
  calc
    Exp_int (x * x) (k + 1) = (x * x) * Exp_int (x * x) k := by dsimp [Exp_int]; rfl
    _ = (x * x) * Exp_int x (2 * k) := by rw [IH]
    _ = x * (x * Exp_int x (2 * k)) := by simp [mul_assoc]
    _ = x * Exp_int x (2 * k + 1) := by
      -- Exp_int x (2*k + 1) = x * Exp_int x (2*k)
      dsimp [Exp_int]; rfl
    _ = Exp_int x (2 * (k + 1)) := by
      -- Exp_int x (2*(k+1)) = Exp_int x (2*k + 2) = x * Exp_int x (2*k + 1)
      dsimp [Exp_int]; rfl

-- LLM HELPER
theorem Exp_int_mod_base (a z : Nat) : ∀ k, Exp_int (a % z) k % z = Exp_int a k % z
| 0 => by
  dsimp [Exp_int]; rfl
| k+1 => by
  dsimp [Exp_int]
  have IH := Exp_int_mod_base a z k
  calc
    Exp_int (a % z) (k + 1) % z = ((a % z) * Exp_int (a % z) k) % z := by dsimp [Exp_int]; rfl
    _ = (a % z * (Exp_int a k % z)) % z := by rw [IH]
    _ = (a * Exp_int a k) % z := by
      -- (a * b) % z = (a % z * (b % z)) % z, so rewrite the other direction
      have h := Nat.mul_mod a (Exp_int a k) z
      rw [←h]
    _ = Exp_int a (k + 1) % z := by dsimp [Exp_int]; rfl
-- </vc-helpers>

-- <vc-spec>
def ModExp_int (x y n z : Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
if n = 0 then
  if y = 0 then 1 % z else x % z
else
  let y1 := y / 2
  let rec := ModExp_int ((x * x) % z) y1 (n - 1) z
  if y % 2 = 1 then (x % z * rec) % z else rec
-- </vc-code>

-- <vc-theorem>
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z :=
-- </vc-theorem>
-- <vc-proof>
by
  induction n with
  | zero =>
    -- n = 0 case
    dsimp [ModExp_int]
    -- Exp_int 2 1 = 2
    have hE : Exp_int 2 1 = 2 := by dsimp [Exp_int]; rfl
    have hy2 : y < 2 := by
      rwa [←hE] at hy
    cases y with
    | zero =>
      dsimp [Exp_int, ModExp_int]; rfl
    | succ y' =>
      cases y' with
      | zero =>
        dsimp [Exp_int, ModExp_int]; rfl
      | succ y'' =>
        -- y >= 2 contradicts y < 2
        have two_le : 2 ≤ succ (succ y'') := by
          apply Nat.succ_le_succ; apply Nat.succ_le_succ; apply Nat.zero_le
        linarith
  | succ n ih =>
    dsimp [ModExp_int]
    let y1 := y / 2
    -- compute bound for y to get bound for y1
    have two_pow : Exp_int 2 (n + 2) = 2 * Exp_int 2 (n + 1) := by dsimp [Exp_int]; rfl
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
    -- apply induction hypothesis to the recursive call
    have rec_eq := ih ((x * x) % z) y1 z y1_lt hz
    by_cases hodd : y % 2 = 1
    ·
      -- odd case: y = 2*y1 + 1
      have y_repr := Nat.div_add_mod y 2
      have y_is : y = 2 * y1 + 1 := by
        rw [y_repr]; rw [if_pos hodd]; rfl
      calc
        ModExp_int x y (n + 1) z
            = (x % z * (ModExp_int ((x * x) % z) y1 n z)) % z := by
          dsimp [ModExp_int]; simp [hodd]
        _ = (x % z * (Exp_int ((x * x) % z) y1 % z)) % z := by rw [rec_eq]
        _ = (x % z * (Exp_int (x * x) y1 % z)) % z := by
          rw [Exp_int_mod_base (x * x) z y1]
        _ = (x % z * (Exp_int x (2 * y1) % z)) % z := by
          rw [Exp_int_pow_double x y1]
        _ = (x * Exp_int x (2 * y1)) % z := by
          have h := Nat.mul_mod (x) (Exp_int x (2 * y1)) z
          rw [←h]
        _ = Exp_int x (2 * y1 + 1) % z := by
          dsimp [Exp_int]; rfl
        _ = Exp_int x y % z := by rw [y_is]
    ·
      -- even case: y = 2*y1
      have y_repr := Nat.div_add_mod y 2
      have y_is : y = 2 * y1 := by
        rw [y_repr]; rw [if_neg hodd]; rfl
      calc
        ModExp_int x y (n + 1) z
            = ModExp_int ((x * x) % z) y1 n z := by
          dsimp [ModExp_int]; simp [hodd]
        _ = Exp_int ((x * x) % z) y1 % z := by rw [rec_eq]
        _ = Exp_int (x * x) y1 % z := by
          rw [Exp_int_mod_base (x * x) z y1]
        _ = Exp_int x (2 * y1) % z := by rw [Exp_int_pow_double x y1]
        _ = Exp_int x y % z := by rw [y_is]
-- </vc-proof>

end BignumLean