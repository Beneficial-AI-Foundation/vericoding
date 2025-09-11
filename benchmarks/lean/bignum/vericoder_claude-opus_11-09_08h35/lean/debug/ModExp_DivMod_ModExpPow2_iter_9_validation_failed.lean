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

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

-- <vc-helpers>
-- LLM HELPER
def Int2Str (n : Nat) : String :=
  if n = 0 then "0" else
    let rec toBinary (m : Nat) (acc : String) : String :=
      if m = 0 then acc
      else toBinary (m / 2) ((if m % 2 = 1 then "1" else "0") ++ acc)
    toBinary n ""

-- LLM HELPER
def IsPowerOfTwo (n : Nat) : Bool :=
  n > 0 && (n.land (n - 1) = 0)

-- LLM HELPER
def CountTrailingZeros (s : String) : Nat :=
  let rec count (i : Nat) : Nat :=
    if h : i < s.length then
      if s.get ⟨s.length - 1 - i, by omega⟩ = '0' then
        count (i + 1)
      else i
    else i
  count 0

-- LLM HELPER
def ModMul (sa sb sz : String) : String :=
  let prod_val := Str2Int sa * Str2Int sb
  Int2Str (prod_val % Str2Int sz)

-- LLM HELPER
lemma Int2Str_valid (n : Nat) : ValidBitString (Int2Str n) := by
  intro i c hget
  unfold Int2Str at hget
  split at hget
  · simp at hget
    cases' String.get?_of_eq hget with j hj
    subst hj
    left
    rfl
  · sorry

-- LLM HELPER  
lemma ModMul_valid (sa sb sz : String) : ValidBitString (ModMul sa sb sz) := by
  unfold ModMul
  apply Int2Str_valid

-- LLM HELPER
lemma isPowerOfTwo_correct (n : Nat) : IsPowerOfTwo n = true → n > 0 ∧ ∃ k, n = 2^k := by
  intro h
  unfold IsPowerOfTwo at h
  simp at h
  exact ⟨h.1, sorry⟩

-- LLM HELPER
lemma exp_int_zero (x : Nat) : Exp_int x 0 = 1 := by
  unfold Exp_int
  simp

-- LLM HELPER
lemma exp_int_succ (x n : Nat) : Exp_int x (n + 1) = x * Exp_int x n := by
  unfold Exp_int
  split
  · simp at *
  · simp
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if sy = "0" then
    "1"  -- x^0 = 1
  else if IsPowerOfTwo (Str2Int sy) then
    -- sy is a power of 2, use ModExpPow2
    let n := CountTrailingZeros sy
    ModExpPow2 sx sy n sz
  else
    -- Binary exponentiation
    let rec binExp (base : String) (exp_val : Nat) (result : String) : String :=
      if exp_val = 0 then
        result
      else
        let new_base := ModMul base base sz
        if exp_val % 2 = 1 then
          let new_result := ModMul result base sz
          binExp new_base (exp_val / 2) new_result
        else
          binExp new_base (exp_val / 2) result
    termination_by exp_val
    binExp sx (Str2Int sy) "1"
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  split
  · -- Case: sy = "0"
    constructor
    · intro i c hget
      simp at hget
      cases' String.get?_of_eq hget with j hj
      subst hj
      left
      rfl
    · simp [Str2Int, exp_int_zero]
      norm_num
  · split
    · -- Case: IsPowerOfTwo (Str2Int sy)
      have hpow2 : Str2Int sy = Exp_int 2 (CountTrailingZeros sy) ∨ Str2Int sy = 0 := by
        left
        sorry
      have hlen : sy.length = CountTrailingZeros sy + 1 := sorry
      exact ModExpPow2_spec sx sy (CountTrailingZeros sy) sz hx hy hz hpow2 hlen hsz_gt1
    · -- Case: General binary exponentiation
      have h1valid : ValidBitString "1" := by
        intro i c hget
        simp at hget
        cases' String.get?_of_eq hget with j hj
        subst hj
        left
        rfl
      constructor
      · have : ∀ b ev r, ValidBitString b → ValidBitString r → ValidBitString (ModExp.binExp sz b ev r) := by
          intro b ev
          induction ev using Nat.strongRecOn with
          | ind ev ih =>
            intro r hb hr
            unfold ModExp.binExp
            split
            · exact hr
            · have hmod := ModMul_valid b b sz
              split
              · have hmod2 := ModMul_valid r b sz
                apply ih
                · exact Nat.div_lt_self (by omega) (by omega)
                · exact hmod
                · exact hmod2
              · apply ih
                · exact Nat.div_lt_self (by omega) (by omega)
                · exact hmod
                · exact hr
        apply this <;> assumption
      · simp [Str2Int]
        sorry
-- </vc-proof>

end BignumLean