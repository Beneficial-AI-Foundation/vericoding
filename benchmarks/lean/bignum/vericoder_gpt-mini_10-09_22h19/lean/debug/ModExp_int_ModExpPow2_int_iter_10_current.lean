namespace BignumLean

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def ModExpPow2_int (x y n z : Nat) : Nat :=
  sorry

axiom ModExpPow2_int_spec (x y n z : Nat) (hy : y = Exp_int 2 n) (hz : z > 0) :
  ModExpPow2_int x y n z = Exp_int x y % z

-- <vc-helpers>
-- LLM HELPER
theorem Exp_int_zero (x : Nat) : Exp_int x 0 = 1 := by
  dsimp [Exp_int]; -- if 0 = 0 then 1 else ...
  rw [if_pos (by rfl : 0 = 0)]
  rfl

-- LLM HELPER
theorem Exp_int_succ {x m : Nat} (hm : m ≠ 0) : Exp_int x m = x * Exp_int x (m - 1) := by
  dsimp [Exp_int]
  have : (m = 0) = False := by
    by_cases h : m = 0
    · contradiction
    · rfl
  rw [if_neg (by intro h; apply hm; exact h)]
  rfl

-- LLM HELPER
theorem Exp_int_one (x : Nat) : Exp_int x 1 = x := by
  dsimp [Exp_int]
  have : 1 = 0 → False := by intro h; cases h
  rw [if_neg (by intro h; exact this h)]
  rfl

-- LLM HELPER
theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  induction a with
  | zero =>
    simp [Nat.zero_add]
    rw [Exp_int_zero]; simp
  | succ a ih =>
    simp [Nat.succ_add]
    have hne : Nat.succ (a + b) ≠ 0 := Nat.succ_ne_zero (a + b)
    rw [Exp_int_succ hne]
    rw [ih]
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
    dsimp [ModExp_int]
    -- Exp_int x 0 = 1
    rw [Exp_int_zero]
    rfl
  | succ y' =>
    cases y' with
    | zero =>
      -- y = 1
      dsimp [ModExp_int]
      -- ModExp_int for n = 0 and y = 1 gives x % z
      have : Exp_int x 1 = x := Exp_int_one x
      rw [this]
      rfl
    | succ _ =>
      -- y >= 2 contradicts y < 2
      have two_le_y : 2 ≤ y := by
        -- y = succ (succ y'), so y ≥ 2
        apply Nat.succ_le_succ
        apply Nat.succ_le_succ
        apply Nat.zero_le
      exact (Nat.not_lt_of_ge two_le_y) hy
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
    -- ha : ModExpPow2_int x p n z = Exp_int x p % z
    -- hb : ModExp_int x (y - p) n z = Exp_int x (y - p) % z
    rw [ha, hb]
    -- multiply and take mod
    rw [←Nat.mul_mod]
    -- use Exp_int_add and p + (y - p) = y
    rw [Exp_int_add]
    rw [eq1]
    rfl
-- </vc-proof>

end BignumLean