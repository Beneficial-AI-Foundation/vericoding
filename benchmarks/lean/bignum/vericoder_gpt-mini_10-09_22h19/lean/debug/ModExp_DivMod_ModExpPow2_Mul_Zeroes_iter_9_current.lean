namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
theorem Exp_int_succ (x n : Nat) : Exp_int x (n + 1) = x * Exp_int x n := by
  have hne : (n + 1) ≠ 0 := Nat.succ_ne_zero n
  dsimp [Exp_int]
  simp [if_neg hne]
  -- after simplification we have x * Exp_int x ((n + 1) - 1) = x * Exp_int x n
  have : (n + 1) - 1 = n := by simp
  rw [this]
  rfl

-- LLM HELPER
theorem Exp_int_add (x a : Nat) : ∀ b, Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  intro b
  induction b with
  | zero =>
    rw [Nat.add_zero]
    have E0 : Exp_int x 0 = 1 := by dsimp [Exp_int]; simp
    calc
      Exp_int x (a + 0) = Exp_int x a := by rw [Nat.add_zero]
      _ = Exp_int x a * 1 := by simp
      _ = Exp_int x a * Exp_int x 0 := by rw [E0]
  | succ b ih =>
    have h1 : a + succ b = succ (a + b) := by simp
    calc
      Exp_int x (a + succ b) = Exp_int x (succ (a + b)) := by rw [h1]
      _ = x * Exp_int x (a + b) := by apply Exp_int_succ
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = Exp_int x a * (x * Exp_int x b) := by ring
      _ = Exp_int x a * Exp_int x (succ b) := by rw [Exp_int_succ x b]

-- LLM HELPER
theorem Exp_int_two_mul (x e : Nat) : Exp_int x (2 * e) = Exp_int x e * Exp_int x e := by
  -- 2 * e = e + e, so apply Exp_int_add
  have : 2 * e = e + e := by simp [Nat.add_comm]
  rw [this]
  exact Exp_int_add x e e

-- LLM HELPER
def ModMul (a b m : String) : String := (DivMod (Mul a b) m).2

-- LLM HELPER
theorem ModMul_spec (a b m : String) (ha : ValidBitString a) (hb : ValidBitString b) (hm : ValidBitString m) (hpos : Str2Int m > 0) :
  ValidBitString (ModMul a b m) ∧ Str2Int (ModMul a b m) = (Str2Int a * Str2Int b) % Str2Int m := by
  let prod := Mul a b
  -- deconstruct multiplication spec
  let mult_spec := Mul_spec a b ha hb
  let hprod_valid := mult_spec.left
  let hprod_eq := mult_spec.right
  -- deconstruct division spec
  have dspec := DivMod_spec prod m hprod_valid hm hpos
  -- dspec is nested conjunction: ValidBitString quotient ∧ (ValidBitString remainder ∧ (quotient_eq ∧ remainder_eq))
  -- destruct it
  match dspec with
  | And.intro q_valid rest =>
    match rest with
    | And.intro r_valid rest2 =>
      match rest2 with
      | And.intro q_eq r_eq =>
        constructor
        · -- validity of remainder (which is DivMod prod m).2
          exact r_valid
        · -- numeric equality: Str2Int (ModMul a b m) = Str2Int prod % Str2Int m = Str2Int a * Str2Int b % Str2Int m
          calc
            Str2Int (ModMul a b m) = Str2Int ((DivMod prod m).2) := rfl
            _ = Str2Int ((DivMod prod m).2) := rfl
            _ = Str2Int ((DivMod prod m).2) := by rfl
            _ = Str2Int ((DivMod prod m).2) := by rfl
            _ = Str2Int ((DivMod prod m).2) := by rfl
            _ = Str2Int ((DivMod prod m).2) := by rfl
            _ = Str2Int ((DivMod prod m).2) := by rfl
            _ = Str2Int ((DivMod prod m).2) := by rfl
            _ = Str2Int ((DivMod prod m).2) := by rfl
            _ = Str2Int ((DivMod prod m).2) := by rfl
            _ = Str2Int ((DivMod prod m).2) := by rfl
            -- use r_eq then hprod_eq
            _ = Str2Int prod % Str2Int m := by rw [r_eq]
            _ = (Str2Int a * Str2Int b) % Str2Int m := by rw [hprod_eq]
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
def ModExp (sx sy sz : String) : String :=
  let step := fun (acc : String) (ch : Char) =>
    let acc2 := ModMul acc acc sz
    if ch = '1' then ModMul acc2 sx sz else acc2
  sy.data.foldl step "1"
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
-- </vc-theorem>
-- <vc-proof>
by
  let m := Str2Int sz
  have hmpos : m > 0 := by linarith
  let step := fun (acc : String) (ch : Char) =>
    let acc2 := ModMul acc acc sz
    if ch = '1' then ModMul acc2 sx sz else acc2
  let expfold := fun (accv : Nat) (ch : Char) => 2 * accv + (if ch = '1' then 1 else 0)
  -- general induction over the list of chars, tracking numeric value of accumulator
  have IH_general :
    ∀ (l : List Char) (acc : String) (acc_val : Nat),
      ValidBitString acc →
      Str2Int acc = Exp_int (Str2Int sx) acc_val % m →
      ValidBitString (l.foldl step acc) ∧
      Str2Int (l.foldl step acc) = Exp_int (Str2Int sx) (l.foldl expfold acc_val) % m := by
    intro l
    induction l generalizing acc acc_val with
    | nil =>
      intros acc acc_val Hvalid Heq
      simp [List.foldl]
      exact ⟨Hvalid, Heq⟩
    | cons hd tl ih =>
      intros acc acc_val Hvalid Heq
      -- compute acc2 = ModMul acc acc sz
      have acc2_spec := ModMul_spec acc acc sz Hvalid Hvalid hz hmpos
      have Hacc2_valid := acc2_spec.left
      have Hacc2_eq := acc2_spec.right
      by_cases h1 : hd = '1'
      · -- hd = '1' branch
        -- acc' = ModMul acc2 sx sz
        have acc'_spec := ModMul_spec (ModMul acc acc sz) sx sz Hacc2_valid hx hz hmpos
        have Hacc'_valid := acc'_spec.left
        have Hacc'_eq := acc'_spec.right
        let new_acc_val := expfold acc_val hd
        -- compute numeric value of new accumulator
        have Hnew : Str2Int (ModMul (ModMul acc acc sz) sx sz) = Exp_int (Str2Int sx) new_acc_val % m := by
          -- start from definition
          calc
            Str2Int (ModMul (ModMul acc acc sz) sx sz)
                = (Str2Int (ModMul acc acc sz) * Str2Int sx) % m := by rw [Hacc'_eq]
            _ = ((Str2Int acc * Str2Int acc) % m * Str2Int sx) % m := by rw [Hacc2_eq]
            _ = ((Exp_int (Str2Int sx) acc_val % m) * (Exp_int (Str2Int sx) acc_val % m) * Str2Int sx) % m := by
              rw [Heq, Heq]
            -- now convert product of residues to product then use Exp_int identity
            _ = (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val * Str2Int sx) % m := by
              -- use Nat.mul_mod to move mods away (apply twice)
              have A := Nat.mul_mod (Exp_int (Str2Int sx) acc_val % m) (Exp_int (Str2Int sx) acc_val * Str2Int sx) m
              have B := Nat.mul_mod (Exp_int (Str2Int sx) acc_val) (Exp_int (Str2Int sx) acc_val * Str2Int sx) m
              -- rewrite via these lemmas and symmetry
              rw [←B]
              -- now rewrite again to eliminate the remaining % on the second factor
              rw [←Nat.mul_mod (Exp_int (Str2Int sx) acc_val) (Exp_int (Str2Int sx) acc_val) m]
            _ = Exp_int (Str2Int sx) (2 * acc_val + 1) % m := by
              have : Exp_int (Str2Int sx) (2 * acc_val + 1) = Exp_int (Str2Int sx) (acc_val + acc_val + 1) := by rfl
              rw [this]
              -- Exp_int (a + b + 1) = Exp_int (a+b) * Exp_int 1 = (Exp_int a * Exp_int b) * a
              have Eadd := Exp_int_add (Str2Int sx) acc_val acc_val
              rw [Exp_int_succ (Str2Int sx) (acc_val + acc_val)] at Eadd
              -- compute:
              calc
                Exp_int (Str2Int sx) (acc_val + acc_val + 1)
                    = Exp_int (Str2Int sx) (acc_val + acc_val) * Exp_int (Str2Int sx) 1 := by
                  rw [Exp_int_succ (Str2Int sx) (acc_val + acc_val - 0)] -- harmless rewrite (keeps structure)
                _ = (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val) * (Exp_int (Str2Int sx) 1) := by
                  rw [Eadd]
                _ = (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val) * Str2Int
-- </vc-proof>

end BignumLean