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
theorem valid_one : ValidBitString "1" := by
  intro i c h
  cases i with
  | zero =>
    -- get? at position 0 yields '1'
    have : "1".get? 0 = some '1' := by simp
    rw [this] at h
    injection h with hc
    right; exact hc.symm
  | succ k =>
    -- out of bounds
    have : "1".get? (k + 1) = none := by simp
    rw [this] at h
    cases h

-- LLM HELPER
theorem str2int_one : Str2Int "1" = 1 := by
  -- "1".data = ['1'], foldl yields 1
  simp [Str2Int]; rfl

-- LLM HELPER
theorem Exp_int_add (x a b : Nat) : Exp_int x (a + b) = Exp_int x a * Exp_int x b := by
  induction b with
  | zero =>
    simp [Exp_int]
    -- Exp_int x (a + 0) = Exp_int x a, and Exp_int x 0 = 1 so RHS = Exp_int x a * 1 = Exp_int x a
    simp
  | succ b ih =>
    simp [Exp_int]
    -- Exp_int x (a + (b+1)) = x * Exp_int x (a + b)
    calc
      Exp_int x (a + (b + 1)) = x * Exp_int x (a + b) := by simp [Exp_int]
      _ = x * (Exp_int x a * Exp_int x b) := by rw [ih]
      _ = Exp_int x a * (x * Exp_int x b) := by ring
      _ = Exp_int x a * Exp_int x (b + 1) := by simp [Exp_int]

-- LLM HELPER
theorem Exp_int_two_mul (x e : Nat) : Exp_int x (2 * e) = Exp_int x e * Exp_int x e := by
  have : 2 * e = e + e := by simp [Nat.mul_comm]
  rw [this]
  exact Exp_int_add x e e

-- LLM HELPER
theorem ModMul_spec (a b m : String) (ha : ValidBitString a) (hb : ValidBitString b) (hm : ValidBitString m) (hpos : Str2Int m > 0) :
  ValidBitString (ModMul a b m) ∧ Str2Int (ModMul a b m) = (Str2Int a * Str2Int b) % Str2Int m := by
  let prod := Mul a b
  have mult_spec := Mul_spec a b ha hb
  have hprod_valid := mult_spec.left
  have hprod_eq := mult_spec.right
  let dm := DivMod prod m
  have dmspec := DivMod_spec prod m hprod_valid hm hpos
  constructor
  · exact dmspec.left.right
  · calc
      Str2Int (ModMul a b m) = Str2Int (dm.2) := rfl
      _ = Str2Int prod % Str2Int m := by rw [dmspec.right.right]
      _ = (Str2Int a * Str2Int b) % Str2Int m := by rw [hprod_eq]; rfl

-- LLM HELPER
theorem char_is_bit {s : String} (hs : ValidBitString s) (i : Nat) (c : Char) (h : s.get? i = some c) : c = '0' ∨ c = '1' := by
  exact hs (i:=i) (c:=c) h
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
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
  -- We'll prove by induction over sy.data fold
  let m := Str2Int sz
  have hmpos : m > 0 := by linarith
  let step := fun (acc : String) (ch : Char) =>
    let acc2 := ModMul acc acc sz
    if ch = '1' then ModMul acc2 sx sz else acc2
  let expfold := fun (acc : Nat) (ch : Char) => 2 * acc + (if ch = '1' then 1 else 0)
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
      -- consider whether hd = '1' or not
      by_cases h1 : hd = '1'
      · -- hd = '1'
        have acc' := ModMul acc2 sx sz
        have acc'_spec := ModMul_spec acc2 sx sz Hacc2_valid hx hz hmpos
        obtain ⟨Hacc'_valid, Hacc'_eq⟩ := acc'_spec
        -- compute new acc_val
        let new_val := expfold acc_val hd
        -- show Str2Int acc' = Exp_int ... new_val % m
        calc
          Str2Int acc' = (Str2Int acc2 * Str2Int sx) % m := by rw [acc'_eq]
          _ = ((Str2Int acc * Str2Int acc) % m * Str2Int sx) % m := by rw [Hacc2_eq]
          _ = ((Exp_int (Str2Int sx) acc_val % m * Exp_int (Str2Int sx) acc_val % m) * Str2Int sx) % m := by
            rw [Heq]
            congr
            · rfl
            · rfl
          _ = ((Exp_int (Str2Int sx) acc_val * Exp_int (Str2Int sx) acc_val) * Str2Int sx) % m := by
            -- use Nat.mul_mod to move mods out
            repeat
              rw [←Nat.mul_mod]
          _ = (Exp_int (Str2Int sx) (acc_val + acc_val) * Str2Int sx) % m := by
            rw [Exp_int_add (Str2Int sx) acc_val acc_val]
          _ = Exp_int (Str2Int sx) (acc_val + acc_val + 1) % m := by
            -- Exp_int x (n+1) = x * Exp_int x n
            simp [Exp_int]
        -- now acc_val + acc_val + 1 = expfold acc_val hd when hd = '1'
        have : expfold acc_val hd = acc_val + acc_val + 1 := by simp [expfold, h1]
        -- apply IH on tl
        have IH_call := ih (l := tl) (acc' : String) (new_val) Hacc'_valid (by rw [this]; exact (by rfl : Str2Int acc' = Exp_int (Str2Int sx) new_val % m))
        -- But the previous equality was already shown via calc; use that:
        have Heq_acc' : Str2Int acc' = Exp_int (Str2Int sx) new_val % m := by
          -- reuse the calc chain: everything simplifies to the desired equality
          -- we can re-evaluate using the chain above; for brevity, use the computed equalities:
          calc
            Str2Int acc' = (Str2Int acc2 * Str2Int sx) % m := by rw [acc'_eq]
            _ = ((Str2Int acc * Str2Int acc) % m * Str2Int sx) % m := by rw [Hacc2_eq]
            _ = ((Exp_int (Str2Int sx) acc_val % m * Exp_int (Str2Int sx) acc_val % m) * Str2Int sx) % m := by rw [Heq]
            _ = ((Exp_int (Str2Int sx) acc_val * Exp_int
-- </vc-theorem>
end BignumLean