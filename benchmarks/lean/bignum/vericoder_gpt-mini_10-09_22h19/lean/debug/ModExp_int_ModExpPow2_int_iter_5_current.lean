namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def ModExpPow2_int (x y n z : Nat) : Nat :=
  sorry

axiom ModExpPow2_int_spec (x y n z : Nat) (hy : y = Exp_int 2 n) (hz : z > 0) :
  ModExpPow2_int x y n z = Exp_int x y % z

-- <vc-helpers>
-- LLM HELPER
theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  induction a with
  | zero =>
    -- Exp_int x 0 = 1, so Exp_int x (0 + b) = 1 * Exp_int x b
    have h0 : Exp_int x 0 = 1 := by
      dsimp [Exp_int]
    dsimp [Exp_int] at h0
    dsimp [Exp_int]
    rw [h0]
    simp [Nat.add_zero]
  | succ a ih =>
    calc
      Exp_int x (a.succ + b) = Exp_int x ((a + b).succ) := by rw [Nat.succ_add]
      _ = x * Exp_int x (a + b) := by dsimp [Exp_int]
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = (x * Exp_int x a) * Exp_int x b := by rw [Nat.mul_assoc]
      _ = Exp_int x a.succ * Exp_int x b := by dsimp [Exp_int]
-- </vc-helpers>

-- <vc-spec>
def ModExp_int (x y n z : Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
match n with
| 0 =>
  if y = 0 then 1 % z else x % z
| n+1 =>
  if h : y < Exp_int 2 n then
    ModExp_int x y n z
  else
    let p := Exp_int 2 n
    let a := ModExpPow2_int x p n z
    let b := ModExp_int x (y - p) n z
    (a * b) % z
-- </vc-code>

-- <vc-theorem>
theorem ModExp_int_spec (x y n z : Nat) (hy : y < Exp_int 2 (n + 1)) (hz : z > 1) :
  ModExp_int x y n z = Exp_int x y % z := by
-- </vc-theorem>
-- <vc-proof>
revert y hy
induction n with
| zero =>
  intro y hy
  -- when n = 0, Exp_int 2 (0 + 1) = 2, so y ∈ {0,1}
  cases y with
  | zero =>
    -- y = 0
    dsimp [ModExp_int, Exp_int]
    -- ModExp_int x 0 0 z = 1 % z and Exp_int x 0 % z = 1 % z
    rfl
  | succ y' =>
    cases y' with
    | zero =>
      -- y = 1
      dsimp [ModExp_int, Exp_int]
      -- ModExp_int x 1 0 z = x % z and Exp_int x 1 % z = x % z
      rfl
    | succ y'' =>
      -- y >= 2 contradicts y < 2
      have two_le : 2 ≤ succ (succ y'') := by
        apply Nat.succ_le_succ
        apply Nat.succ_le_succ
        exact Nat.zero_le _
      have not_lt : ¬ (succ (succ y'') < 2) := Nat.not_lt_of_ge two_le
      exact (not_lt hy) not_lt
| succ n ih =>
  intro y hy
  let p := Exp_int 2 n
  by_cases h : y < p
  · -- y < p: use the smaller n case
    dsimp [ModExp_int]
    rw [if_pos h]
    exact ih y h
  · -- y ≥ p
    dsimp [ModExp_int]
    rw [if_neg h]
    have hle : p ≤ y := Nat.le_of_not_lt h
    have eq1 : p + (y - p) = y := Nat.add_sub_of_le hle
    -- from y < p + p we get (y - p) < p
    have hsum : p + (y - p) < p + p := by
      rw [eq1]; exact hy
    have hy' : y - p < p := (Nat.add_lt_add_iff_left p).1 hsum
    have hz0 : z > 0 := Nat.lt_trans (by norm_num : 0 < 1) hz
    -- apply specification for ModExpPow2_int on p = Exp_int 2 n
    have ha := ModExpPow2_int_spec x p n z rfl hz0
    have hb := ih (y - p) hy'
    -- replace a and b with their modular values
    dsimp at ha hb
    -- a = Exp_int x p % z, b = Exp_int x (y - p) % z
    -- compute (a * b) % z = (Exp_int x p * Exp_int x (y - p)) % z
    rw [ha, hb]
    rw [←Nat.mul_mod]
    -- use Exp_int_add and p + (y - p) = y
    rw [Exp_int_add]
    rw [eq1]
    rfl
-- </vc-proof>

end BignumLean