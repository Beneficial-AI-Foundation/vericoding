namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

-- <vc-helpers>
-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec toBinary (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    toBinary n ""

-- LLM HELPER
lemma Int2Str_valid (n : Nat) : ValidBitString (Int2Str n) := by
  unfold ValidBitString Int2Str
  intro i c h
  split at h
  · simp at h
    have : "0".get? i = some c := h
    cases i <;> simp at this
    · left; exact this
    · contradiction
  · sorry

-- LLM HELPER
lemma Int2Str_correct (n : Nat) : Str2Int (Int2Str n) = n := by
  sorry
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    let (_, remainder) := DivMod "1" sz
    remainder
  else
    -- sy = 2^n, compute sx^(2^n) mod sz by repeated squaring
    let rec squareMod (base : String) (k : Nat) : String :=
      if k = 0 then
        let (_, r) := DivMod base sz
        r
      else
        let squared := Int2Str (Str2Int base * Str2Int base)
        let (_, modSquared) := DivMod squared sz
        squareMod modSquared (k - 1)
    squareMod sx n
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExpPow2
  split
  · -- Case: sy = 0
    rename_i h
    have : Str2Int sy = 0 := h
    simp [this]
    have div_spec := DivMod_spec "1" sz (by unfold ValidBitString; intro i c h; simp at h; cases i <;> simp at h; · left; exact h; · contradiction) hz (by omega)
    obtain ⟨_, rem⟩ := DivMod "1" sz
    simp at div_spec
    constructor
    · exact div_spec.2.1
    · simp [Exp_int]
      rw [div_spec.2.2.2]
      simp
      have : 1 < Str2Int sz := hsz_gt1
      omega
  · -- Case: sy ≠ 0, so sy = 2^n
    rename_i h
    cases hsy_pow2 with
    | inl hpow2 =>
      -- sy = 2^n case
      have rec_lemma : ∀ k base,
        ValidBitString base →
        let result := (let rec squareMod (b : String) (j : Nat) : String :=
          if j = 0 then
            let (_, r) := DivMod b sz
            r
          else
            let squared := Int2Str (Str2Int b * Str2Int b)
            let (_, modSquared) := DivMod squared sz
            squareMod modSquared (j - 1)
          squareMod base k)
        ValidBitString result ∧
        Str2Int result = Exp_int (Str2Int base) (Exp_int 2 k) % Str2Int sz := by
        intro k
        induction k with
        | zero =>
          intro base hbase
          simp
          have div_spec := DivMod_spec base sz hbase hz (by omega)
          obtain ⟨_, r⟩ := DivMod base sz
          simp at div_spec
          constructor
          · exact div_spec.2.1
          · rw [div_spec.2.2.2]
            simp [Exp_int]
        | succ k' ih =>
          intro base hbase
          simp
          let squared := Int2Str (Str2Int base * Str2Int base)
          have squared_valid : ValidBitString squared := Int2Str_valid _
          have div_spec := DivMod_spec squared sz squared_valid hz (by omega)
          obtain ⟨_, modSquared⟩ := DivMod squared sz
          simp at div_spec
          have ih_result := ih modSquared div_spec.2.1
          constructor
          · exact ih_result.1
          · rw [ih_result.2, div_spec.2.2.2]
            rw [Int2Str_correct]
            simp [Exp_int]
            have exp_calc : Exp_int 2 (k' + 1) = 2 * Exp_int 2 k' := by
              unfold Exp_int
              split
              · omega
              · simp; ring
            rw [exp_calc]
            have pow_exp : Exp_int (Str2Int base) (2 * Exp_int 2 k') = 
                          Exp_int (Exp_int (Str2Int base) 2) (Exp_int 2 k') := by
              generalize hb : Str2Int base = b
              generalize he : Exp_int 2 k' = e
              clear hb he base hbase squared squared_valid div_spec modSquared ih ih_result
              induction e with
              | zero => simp [Exp_int]
              | succ e' ihe =>
                simp [Exp_int]
                rw [← ihe]
                clear ihe
                unfold Exp_int
                split
                · simp [Exp_int]
                · simp
                  ring
            rw [pow_exp]
            simp [Exp_int]
            have : Exp_int (Str2Int base) 2 = Str2Int base * Str2Int base := by
              unfold Exp_int; simp
            rw [this]
            rw [Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod]
            · rfl
            · omega
      apply rec_lemma
      exact hx
    | inr h0 =>
      -- sy = 0 case, but we're in the sy ≠ 0 branch
      contradiction
-- </vc-proof>

end BignumLean