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
    simp [Exp_int, Nat.add_zero]
  | succ a ih =>
    -- Exp_int x (a.succ + b) = x * Exp_int x (a + b) by definition
    calc
      Exp_int x (a.succ + b) = x * Exp_int x (a + b) := by simp [Exp_int]
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = (x * Exp_int x a) * Exp_int x b := by rw [Nat.mul_assoc]
      _ = Exp_int x a.succ * Exp_int x b := by simp [Exp_int]
-- </vc-helpers>

-- <vc-spec>
def ModExp_int (x y n z : Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
def ModExpPow2_int (x y n z : Nat) : Nat :=
  if h : y = Exp_int 2 n then Exp_int x y % z else 1

def ModExp_int (x y n z : Nat) : Nat :=
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
  -- We proceed by induction on n.
  revert y hy
  induction n with
  | zero =>
    intro y hy hz
    -- n = 0, so Exp_int 2 (0 + 1) = 2, hence y < 2, so y = 0 or y = 1
    cases y with
    | zero =>
      simp [ModExp_int, Exp_int]
    | succ y' =>
      cases y' with
      | zero =>
        -- y = 1
        simp [ModExp_int, Exp_int]
      | succ y'' =>
        -- y >= 2 contradicts y < 2
        simp [Exp_int] at hy
        -- hy is succ (succ y'') < 2 which is impossible
        have : false := Nat.not_lt_of_ge (by
          -- show 2 ≤ succ (succ y'')
          have : 2 ≤ succ (succ y'') := by
            apply Nat.succ_le_succ
            apply Nat.succ_le_succ
            exact Nat.zero_le _
            -- two succs above 0
          exact this) hy
        exact False.elim this
  | succ n ih =>
    intro y hy hz
    -- two cases: y < 2^n or not
    by_cases h : y < Exp_int 2 n
    · -- y < 2^n, reduce to smaller n
      simp [ModExp_int, if_pos h]
      exact ih y h hz
    · -- y ≥ 2^n
      simp [ModExp_int, if_neg h]
      let p := Exp_int
-- </vc-theorem>
end BignumLean