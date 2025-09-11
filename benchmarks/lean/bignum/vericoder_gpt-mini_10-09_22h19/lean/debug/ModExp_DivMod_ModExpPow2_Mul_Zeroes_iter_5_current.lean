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
  -- Unfold the definition: for (n+1) the if-branch is the 'else' case
  simp [Exp_int]
  rfl

-- LLM HELPER
theorem Exp_int_add (x a : Nat) : ∀ b, Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  intro b
  induction b with
  | zero =>
    simp [Exp_int]
    rw [Nat.add_zero]
    simp
  | succ b ih =>
    calc
      Exp_int x (a + succ b) = Exp_int x ((a + b) + 1) := by rw [Nat.add_assoc]
      _ = x * Exp_int x (a + b) := by apply Exp_int_succ
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = Exp_int x a * (x * Exp_int x b) := by
        -- simple arithmetic reassociation
        simp_all
      _ = Exp_int x a * Exp_int x (succ b) := by
        -- apply succ lemma on the right factor
        congr
        apply Exp_int_succ

-- LLM HELPER
theorem Exp_int_two_mul (x e : Nat) : Exp_int x (2 * e) = Exp_int x e * Exp_int x e := by
  -- 2*e = e + e
  have : 2 * e = e + e := by simp [Nat.add_comm]
  rw [this]
  exact (Exp_int_add x e e)

-- LLM HELPER
def ModMul (a b m : String) : String := (DivMod (Mul a b) m).2

-- LLM HELPER
theorem ModMul_spec (a b m : String) (ha : ValidBitString a) (hb : ValidBitString b) (hm : ValidBitString m) (hpos : Str2Int m > 0) :
  ValidBitString (ModMul a b m) ∧ Str2Int (ModMul a b m) = (Str2Int a * Str2Int b) % Str2Int m := by
  let prod := Mul a b
  -- get Mul_spec: ValidBitString prod ∧ Str2Int prod = Str2Int a * Str2Int b
  have mult_spec := Mul_spec a b ha hb
  -- split the conjunction
  have hprod_valid : ValidBitString prod := mult_spec.left
  have hprod_eq : Str2Int prod = Str2Int a * Str2Int b := mult_spec.right
  -- apply DivMod_spec to prod and m
  let dm := DivMod prod m
  have dmspec := DivMod_spec prod m hprod_valid hm hpos
  -- dmspec is nested conjunction: ValidBitString dm.1 ∧ ValidBitString dm.2 ∧ Str2Int dm.1 = ... ∧ Str2Int dm.2 = ...
  -- destructure step by step
  cases dmspec with
  | intro qrest rrest =>
    -- qrest : ValidBitString dm.1
    -- rrest : ValidBitString dm.2 ∧ Str2Int dm.1 = ... ∧ Str2Int dm.2 = ...
    cases rrest with
    | intro r_valid rest2 =>
      cases rest2 with
      | intro q_eq r_eq =>
        -- now build the result: ModMul a b m = dm.2
        constructor
        · exact r_valid
        · calc
            Str2Int (ModMul a b m) = Str2Int dm.2 := rfl
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
  -- Str2Int sy equals folding expfold over sy.data starting from 0
  have sy_eq_fold : Str2Int sy = sy.data.foldl expfold 0 := by
    simp [Str2Int, expfold]
  -- General induction over list of chars
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
      -- acc2 = ModMul acc acc sz
      have acc2_spec := ModMul_spec acc acc sz Hvalid Hvalid hz hmpos
      obtain ⟨Hacc2_valid, Hacc2_eq⟩ := acc2_spec
      by_cases h1 : hd = '1'
      · -- case hd = '1'
        have acc'_spec := ModMul_spec (ModMul acc acc sz) sx sz Hacc2_valid hx hz hmpos
        obtain ⟨Hacc'_valid, Hacc'_eq⟩ := acc'_spec
        -- compute new accumulator value in numeric fold
        let new_acc_val := expfold acc_val hd
        -- show Str2Int (ModMul acc2 sx sz) = Exp_int (Str2Int sx) new_acc_val % m
        have Hnew : Str2Int (ModMul (ModMul acc acc sz) sx sz) = Exp_int (Str2Int sx) new_acc_val % m := by
          calc
            Str2Int (ModMul (ModMul acc acc sz) sx sz) = (Str2Int (ModMul acc acc sz) * Str2Int sx) % m := by rw [acc'_eq]
            _ = ((Str2Int acc * Str2Int acc) % m * Str2Int sx) % m := by rw [Hacc2_eq]
            _ = ((Exp_int (Str2Int sx) acc_val % m) * (Exp_int (Str2Int sx) acc_val % m) * Str2Int sx) % m := by
              rw [Heq]
            _ = (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val * Str2Int sx) % m := by
              -- combine modular multiplications using Nat.mul_mod twice
              rw [Nat.mul_mod (Exp_int (Str2Int sx) acc_val) (Exp_int (Str2Int sx) acc_val) m]
              rw [Nat.mul_mod (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val) (Str2Int sx) m]
            _ = Exp_int (Str2Int sx) (2 * acc_val + 1) % m := by
              -- exponent arithmetic: Exp_int x (2*acc_val + 1) = Exp_int x acc_val * Exp_int x acc_val * x
              have : Exp_int (Str2Int sx) (2 * acc_val + 1) = Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val * Str2Int sx := by
                calc
                  Exp_int (Str2Int sx) (2 * acc_val + 1) = Exp_int (Str2Int sx) ((acc_val + acc_val) + 1) := by
                    simp [Nat.add_comm]; rfl
                  _ = Exp_int (Str2Int sx) (acc_val + acc_val) * Exp_int (Str2Int sx) 1 := by
                    rw [Exp_int_add (Str2Int sx) acc_val acc_val]
                    rfl
                  _ = (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val) * (Str2Int sx) := by
                    simp [Exp_int]; rfl
                exact this
              rw [this]
        -- apply IH to tail
        have IHcall := ih tl (ModMul (ModMul acc acc sz) sx sz) new_acc_val Hacc'_valid Hnew
        -- simplify the folded step to match expected form
        simp [h1]
        exact IHcall
      · -- case hd ≠ '1'
        -- acc' = acc2
        have : tl.foldl step (if hd = '1' then ModMul (ModMul acc acc sz) sx sz else ModMul acc acc sz) =
                   tl.foldl step (ModMul acc acc sz) := by simp [h1]
        rw [this]
        let new_acc_val := expfold acc_val hd
        have Hnew : Str2Int (ModMul acc acc sz) = Exp_int (Str2Int sx) new_acc_val % m := by
          calc
            Str2Int (ModMul acc acc sz) = (Str2Int acc * Str2Int acc) % m := by rw [Hacc2_eq]
            _ = ((Exp_int (Str2Int sx) acc_val % m) * (Exp_int (Str2Int sx) acc_val % m)) % m := by rw [Heq]
            _ = (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val) % m := by
              rw [Nat.mul_mod (Exp_int (Str2Int sx) acc_val) (Exp_int (Str2Int sx) acc_val) m]
            _ = Exp_int (Str2Int sx) (2 * acc_val) % m := by
              rw [Exp_int_two_mul (Str2Int sx) acc_val]
        exact ih tl (ModMul acc acc sz) new_acc_val Hacc2_valid Hnew
  -- prepare base: start folding sy.data with accumulator "1" and acc_val 0
  have base_valid : ValidBitString "1" := by
    intro i c h
    cases i with
    | zero =>
      simp [String.get?] at h
      injection h with hc
      subst hc
      -- the only character is '1'
      right; rfl
    | succ _ =>
      simp [String.get?] at h
      contradiction
  have base_num : Str2Int "1" = Exp_int (Str2Int sx) 0 % m := by
    -- Str2Int "1" = 1 and Exp_int _ 0 = 1
    simp [Str2Int, Exp_int]
    rfl
  have final := IH_general sy.data "1" 0 base_valid base_num
  exact final
-- </vc-proof>

end BignumLean