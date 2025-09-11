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
  · generalize hn : toBinary n "" = s at h
    have : ∀ m acc, (∀ j d, acc.get? j = some d → d = '0' ∨ d = '1') →
           ∀ k e, (toBinary m acc).get? k = some e → e = '0' ∨ e = '1' := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc hacc k e hget
        unfold toBinary at hget
        split at hget
        · exact hacc k e hget
        · rename_i hm
          apply ih (m / 2) (Nat.div_lt_self (Nat.zero_lt_of_ne_zero hm) (by norm_num))
          · intro j d hj
            simp at hj
            split at hj
            · left; simp [hj]
            · right; simp [hj]
            · exact hacc _ _ hj
          · exact hget
    apply this n ""
    · intro j d hj
      simp at hj
    · rw [← hn]; exact h

-- LLM HELPER
lemma Int2Str_correct (n : Nat) : Str2Int (Int2Str n) = n := by
  unfold Int2Str Str2Int
  split
  · simp
  · generalize hn : toBinary n "" = s
    have : ∀ m acc accVal,
           accVal = s.data.foldl (fun a ch => 2 * a + (if ch = '1' then 1 else 0)) 0 →
           (toBinary m acc).data.foldl (fun a ch => 2 * a + (if ch = '1' then 1 else 0)) 0 = 
           m * (2 ^ acc.length) + accVal := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro acc accVal haccVal
        unfold toBinary
        split
        · simp; omega
        · rename_i hm
          rw [ih (m / 2) (Nat.div_lt_self (Nat.zero_lt_of_ne_zero hm) (by norm_num))]
          · simp [List.foldl_append, List.foldl_cons, List.foldl_nil]
            split <;> simp
            · have : m = 2 * (m / 2) + 1 := by
                have := Nat.div_add_mod m 2
                simp at this
                split at this <;> omega
              rw [this]
              ring_nf
              simp [pow_succ]
              ring
            · have : m = 2 * (m / 2) := by
                have := Nat.div_add_mod m 2
                simp at this
                split at this <;> omega
              rw [this]
              ring_nf
              simp [pow_succ]
              ring
          · rfl
    convert this n "" 0 (by simp) using 1
    simp
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
  split_ifs with h
  · -- Case: sy = 0
    have : Str2Int sy = 0 := h
    simp [this]
    have div_spec := DivMod_spec "1" sz (by unfold ValidBitString; intro i c h; simp at h; cases i <;> simp at h; left; exact h; contradiction) hz (by omega)
    obtain ⟨_, rem⟩ := DivMod "1" sz
    simp at div_spec
    constructor
    · exact div_spec.2.1
    · simp [Exp_int]
      rw [div_spec.2.2.2]
      simp
      have : 1 < Str2Int sz := hsz_gt1
      omega
  · -- Case: sy = 2^n
    cases hsy_pow2 with
    | inl hpow2 =>
      have : Str2Int sy ≠ 0 := by rw [hpow2]; unfold Exp_int; split <;> omega
      contradiction
    | inr h0 =>
      contradiction
-- </vc-proof>

end BignumLean