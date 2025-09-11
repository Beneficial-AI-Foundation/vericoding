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
  -- Use the definition: Exp_int x (n+1) = if n+1 = 0 then 1 else x * Exp_int x ((n+1)-1)
  -- (n+1) is not zero, and (n+1)-1 = Nat.pred (n+1) = n.
  have hpred : Nat.pred (n + 1) = n := by
    simp [Nat.pred]
  calc
    Exp_int x (n + 1) = (if (n + 1) = 0 then 1 else x * Exp_int x (Nat.pred (n + 1))) := rfl
    _ = x * Exp_int x (Nat.pred (n + 1)) := by
      have : (n + 1) ≠ 0 := Nat.succ_ne_zero n
      simp [if_neg this]
    _ = x * Exp_int x n := by rw [hpred]

-- LLM HELPER
theorem Exp_int_add (x a : Nat) : ∀ b, Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  intro b
  induction b with
  | zero =>
    -- a + 0 = a, and Exp_int x 0 = 1
    simp only [Nat.add_zero]
    -- show Exp_int x a = Exp_int x a * 1
    have : Exp_int x 0 = 1 := by
      dsimp [Exp_int]; split <;> simp?
      -- the definition gives 1 when argument is 0
    -- avoid complex simp; compute directly
    calc
      Exp_int x (a + 0) = Exp_int x a := by simp [Nat.add_zero]
      _ = Exp_int x a * 1 := by simp [this]
      _ = Exp_int x a * Exp_int x 0 := by rw [this]
  | succ b ih =>
    -- Use that Exp_int x (n+1) = x * Exp_int x n
    calc
      Exp_int x (a + succ b) = Exp_int x ((a + b) + 1) := by rw [Nat.add_assoc]
      _ = x * Exp_int x (a + b) := by apply Exp_int_succ
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = Exp_int x a * (x * Exp_int x b) := by
        -- reassociate multiplication
        simp [Nat.mul_comm, Nat.mul_assoc]
      _ = Exp_int x a * Exp_int x (succ b) := by
        -- apply succ lemma on the right factor
        congr
        apply Exp_int_succ

-- LLM HELPER
theorem Exp_int_two_mul (x e : Nat) : Exp_int x (2 * e) = Exp_int x e * Exp_int x e := by
  -- 2*e = e + e, then apply Exp_int_add
  have : 2 * e = e + e := by
    -- straightforward arithmetic
    simp [Nat.mul_comm, Nat.mul_assoc]
  rw [this]
  exact Exp_int_add x e e

-- LLM HELPER
def ModMul (a b m : String) : String := (DivMod (Mul a b) m).2

-- LLM HELPER
theorem ModMul_spec (a b m : String) (ha : ValidBitString a) (hb : ValidBitString b) (hm : ValidBitString m) (hpos : Str2Int m > 0) :
  ValidBitString (ModMul a b m) ∧ Str2Int (ModMul a b m) = (Str2Int a * Str2Int b) % Str2Int m := by
  let prod := Mul a b
  have mult_spec := Mul_spec a b ha hb
  have hprod_valid : ValidBitString prod := mult_spec.left
  have hprod_eq : Str2Int prod = Str2Int a * Str2Int b := mult_spec.right
  let dm := DivMod prod m
  have dmspec := DivMod_spec prod m hprod_valid hm hpos
  -- destructure the nested conjunction coming from DivMod_spec
  cases dmspec with
  | intro q_valid rest =>
    cases rest with
    | intro r_valid rest2 =>
      cases rest2 with
      | intro q_eq r_eq =>
        -- ModMul a b m = dm.2
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
    rfl
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
        let new_acc_val := expfold acc_val hd
        -- compute Str2Int of the new accumulator
        have Hnew : Str2Int (ModMul (ModMul acc acc sz) sx sz) = Exp_int (Str2Int sx) new_acc_val % m := by
          calc
            Str2Int (ModMul (ModMul acc acc sz) sx sz) = (Str2Int (ModMul acc acc sz) * Str2Int sx) % m := by rw [Hacc'_eq]
            _ = ((Str2Int acc * Str2Int acc) % m * Str2Int sx) % m := by rw [Hacc2_eq]
            _ = ((Exp_int (Str2Int sx) acc_val % m) * (Exp_int (Str2Int sx) acc_val % m) * Str2Int sx) % m := by rw [Heq]
            _ = (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val * Str2Int sx) % m := by
              rw [Nat.mul_mod (Exp_int (Str2Int sx) acc_val) (Exp_int (Str2Int sx) acc_val) m]
              rw [Nat.mul_mod (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val) (Str2Int sx) m]
            _ = Exp_int (Str2Int sx) (2 * acc_val + 1) % m := by
              -- use properties of Exp_int to rearrange
              have : Exp_int (Str2Int sx) (2 * acc_val + 1) =
                      Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val * Str2Int sx := by
                calc
                  Exp_int (Str2Int sx) (2 * acc_val + 1) = Exp_int (Str2Int sx) ((acc_val + acc_val) + 1) := by
                    rw [Nat.add_comm]
                  _ = (Exp_int (Str2Int sx) (acc_val + acc_val)) * Exp_int (Str2Int sx) 1 := by
                    rw [Exp_int_add (Str2Int sx) acc_val acc_val]
                    rfl
                  _ = (Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val) * (Str2Int sx) := by
                    -- Exp_int ... 1 = Str2Int sx
                    have E1 : Exp_int (Str2Int sx) 1 = Str2Int sx := by
                      -- Exp_int x 1 = x * Exp_int x 0 = x * 1 = x
                      calc
                        Exp_int (Str2Int sx) 1 = (if 1 = 0 then 1 else (Str2Int sx) * Exp_int (Str2Int sx) 0) := rfl
                        _ = (Str2Int sx) * Exp_int (Str2Int sx) 0 := by
                          have : 1 ≠ 0 := by decide
                          simp [if_neg this]
                        _ = (Str2Int sx) * 1 := by
                          dsimp [Exp_int]; split <;> simp?
                        _ = Str2Int sx := by simp
                    rw [E1]
                rfl
              exact this
        -- apply IH to tail
        have IHcall := ih tl (ModMul (ModMul acc acc sz) sx sz) new_acc_val Hacc'_valid Hnew
        simp [h1]
        exact IHcall
      · -- case hd ≠ '1'
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
      dsimp [String.get?] at h
      injection h with hc
      subst hc
      right; rfl
    | succ _ =>
      dsimp [String.get?] at h
      contradiction
  have base_num : Str2Int "1" = Exp_int (Str2Int sx) 0 % m := by
    -- compute Str2Int "1" = 1
    dsimp [Str2Int]
    -- the fold over singleton ['1'] gives 1
    -- reduce the fold manually
    have : "1".data = ['1'] := by rfl
    rw [this]
    simp [List.foldl]
    -- now Exp_int ... 0 = 1, and 1 % m = 1 because m > 1
    have E0 : Exp_int (Str2Int sx) 0 = 1 := by
      dsimp [Exp_int]; simp
    have mod1 : 1 % m = 1 := by
      apply Nat.mod_eq_of_lt
      linarith [hsz_gt1]
    calc
      Str2Int "1" = 1 := by simp
      _ = Exp_int (Str2Int sx) 0 % m := by
        rw [E0, mod1]
  have final := IH_general sy.data "1" 0 base_valid base_num
  exact final
-- </vc-proof>

end BignumLean