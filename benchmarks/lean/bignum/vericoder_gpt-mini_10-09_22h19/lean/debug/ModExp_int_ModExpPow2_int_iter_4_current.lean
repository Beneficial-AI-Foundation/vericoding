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
      simp [Exp_int]
    simp [h0, Nat.add_zero]
  | succ a ih =>
    calc
      Exp_int x (a.succ + b) = Exp_int x ((a + b).succ) := by
        rw [Nat.succ_add]
      _ = x * Exp_int x (a + b) := by
        -- unfold one step of Exp_int at a successor
        simp [Exp_int]
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = (x * Exp_int x a) * Exp_int x b := by rw [Nat.mul_assoc]
      _ = Exp_int x a.succ * Exp_int x b := by simp [Exp_int]
-- </vc-helpers>

-- <vc-spec>
def ModExp_int (x y n z : Nat) : Nat :=
-- </vc-spec>
-- <vc-code>
def ModExpPow2_int (x y n z : Nat) : Nat :=
  if h : y = Exp_int 2 n then
    match n with
    | 0 => x % z
    | n+1 =>
      let rec aux : Nat -> Nat
        | 0 => x % z
        | k+1 => let t := aux k; (t * t) % z
      aux n
  else 1

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
  cases y with
  | zero =>
    -- y = 0, n = 0
    simp [ModExp_int, Exp_int]
  | succ y' =>
    cases y' with
    | zero =>
      -- y = 1
      simp [ModExp_int, Exp_int]
    | succ y'' =>
      -- y >= 2 contradicts y < 2
      have : 2 ≤ succ (succ y'') := by
        apply Nat.succ_le_succ
        apply Nat.succ_le_succ
        exact Nat.zero_le _
      have : ¬ (succ (succ y'') < 2) := Nat.not_lt_of_ge this
      contradiction
| succ n ih =>
  intro y hy
  -- two cases: y < 2^n or not
  let p := Exp_int 2 n
  by_cases h : y < p
  · -- y < 2^n, reduce to smaller n
    -- unfold ModExp_int for (n+1) and pick the if-branch
    dsimp [ModExp_int]
    rw [if_pos h]
    exact ih y h
  · -- y ≥ 2^n
    dsimp [ModExp_int]
    rw [if_neg h]
    -- from ¬(y < p) we get p ≤ y
    have hle : p ≤ y := Nat.le_of_not_lt h
    -- p + (y - p) = y
    have eq1 : p + (y - p) = y := Nat.add_sub_of_le hle
    -- from y = p + (y - p) and y < 2*p we get (y - p) < p
    have hsum : p + (y - p) < p + p := by
      rw [eq1]; exact hy
    have hy' : y - p < p := (Nat.add_lt_add_iff_left p).1 hsum
    -- z > 0 from z > 1
    have hz0 : z > 0 := Nat.lt_trans (by norm_num : 0 < 1) hz
    -- apply spec for ModExpPow2_int on p = Exp_int 2 n
    have ha : ModExpPow2_int x p n z = Exp_int x p % z := ModExpPow2_int_spec x p n z rfl hz0
    -- apply induction hypothesis to y - p
    have hb : ModExp_int x (y - p) n z = Exp_int x (y - p) % z := ih (y - p) hy'
    -- assemble equalities
    dsimp at ha hb
    rw [ha, hb]
    -- now reduce to multiplicative modular property and Exp_int_add
    -- convert (Exp_int x p % z * Exp_int x (y - p) % z) % z to (Exp_int x p * Exp_int x (y - p)) % z
    rw [←Nat.mul_mod]
    -- use Exp_int_add and p + (y - p) = y
    rw [Exp_int_add]
    rw [eq1]
-- </vc-proof>

end BignumLean