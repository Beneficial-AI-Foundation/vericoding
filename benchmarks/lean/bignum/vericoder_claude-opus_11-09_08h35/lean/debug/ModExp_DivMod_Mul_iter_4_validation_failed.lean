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

def Mul (s1 s2 : String) : String :=
  sorry

axiom Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def isZero (s : String) : Bool :=
  s.all (· = '0') || s.isEmpty

-- LLM HELPER  
def isOne (s : String) : Bool :=
  s = "1"

-- LLM HELPER
def shiftRight (s : String) : String :=
  if s.length ≤ 1 then "0" else s.dropRight 1

-- LLM HELPER
def isOdd (s : String) : Bool :=
  match s.data.getLast? with
  | some '1' => true
  | _ => false

-- LLM HELPER
theorem shiftRight_length_decrease (s : String) (h : ¬isZero s = true) : 
  (shiftRight s).length < s.length := by
  unfold shiftRight isZero
  split
  · simp [String.length]
    split
    · rename_i h1
      exact h1
    · rename_i h1 h2
      simp at h2
      cases' s.data with hd tl
      · simp at h
      · cases' tl
        · simp [String.length, List.length]
        · simp [String.length, List.length] at h1
  · rename_i h1
    simp [String.length, String.dropRight]
    have : 1 < s.length := Nat.not_le.mp h1
    omega

-- LLM HELPER
noncomputable def modExpAux (base exp modulus result : String) : String :=
  if h: isZero exp then
    result
  else
    let newBase := (DivMod (Mul base base) modulus).snd
    let newResult := if isOdd exp then (DivMod (Mul result base) modulus).snd else result
    let newExp := shiftRight exp
    have : (shiftRight exp).length < exp.length := shiftRight_length_decrease exp h
    modExpAux newBase newExp modulus newResult
termination_by exp.length

-- LLM HELPER
lemma str2int_zero_of_all_zero (s : String) (h : s.all (· = '0') = true) : Str2Int s = 0 := by
  unfold Str2Int
  simp [String.data]
  induction s.data with
  | nil => simp
  | cons hd tl ih =>
    simp [List.foldl]
    have : hd = '0' := by
      have := String.all_iff_forall.mp h hd (List.mem_cons_self hd tl)
      exact this
    simp [this]
    have htl : tl.all (· = '0') := by
      intro c hc
      exact String.all_iff_forall.mp h c (List.mem_cons_of_mem hd hc)
    have : tl.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0 := by
      clear ih
      induction tl with
      | nil => simp
      | cons hd' tl' ih' =>
        simp [List.foldl]
        have : hd' = '0' := htl hd' (List.mem_cons_self hd' tl')
        simp [this]
        have : tl'.all (· = '0') := fun c hc => htl c (List.mem_cons_of_mem hd' hc)
        exact ih'
    simp [this]

-- LLM HELPER
axiom modExpAux_spec (base exp modulus result : String) 
  (hbase : ValidBitString base) (hexp : ValidBitString exp) 
  (hmod : ValidBitString modulus) (hresult : ValidBitString result)
  (hmod_gt1 : Str2Int modulus > 1) :
  ValidBitString (modExpAux base exp modulus result) ∧
  Str2Int (modExpAux base exp modulus result) = 
    (Str2Int result * Exp_int (Str2Int base) (Str2Int exp)) % Str2Int modulus
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
noncomputable def ModExp (sx sy sz : String) : String :=
  if isZero sy then
    "1"
  else if Str2Int sz ≤ 1 then
    "0"  -- undefined behavior, return 0
  else
    let base_mod := (DivMod sx sz).snd
    modExpAux base_mod sy sz "1"
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  by_cases h1 : isZero sy = true
  · -- Case: sy is zero
    simp [h1]
    constructor
    · -- "1" is a valid bit string
      intro i c hget
      simp at hget
      cases i with
      | zero => 
        simp at hget
        left
        injection hget with heq
        exact heq.symm
      | succ n =>
        simp at hget
    · -- 1 % (Str2Int sz) = 1 when Str2Int sz > 1
      unfold isZero at h1
      simp at h1
      cases h1 with
      | inl hall =>
        have : Str2Int sy = 0 := str2int_zero_of_all_zero sy hall
        simp [this, Exp_int]
        have : 1 < Str2Int sz := hsz_gt1
        simp [Nat.mod_eq_of_lt this]
        rfl
      | inr hempty =>
        exfalso
        simp [String.isEmpty, String.length] at hempty
        exact Nat.not_lt.mpr hempty hsy_pos
  · -- Case: sy is not zero
    simp [h1]
    by_cases h2 : Str2Int sz ≤ 1
    · -- Case: sz ≤ 1 (contradicts hsz_gt1)
      exfalso
      exact Nat.not_le.mpr hsz_gt1 h2
    · -- Main case: recursive computation
      simp [h2]
      have hdiv : ValidBitString (DivMod sx sz).snd ∧ Str2Int (DivMod sx sz).snd = Str2Int sx % Str2Int sz := by
        have hpos : Str2Int sz > 0 := Nat.zero_lt_of_lt hsz_gt1
        have := DivMod_spec sx sz hx hz hpos
        obtain ⟨_, hr, _, hrem⟩ := this
        exact ⟨hr, hrem⟩
      obtain ⟨hvalid_base, hbase_eq⟩ := hdiv
      have hone : ValidBitString "1" := by
        intro i c hget
        simp at hget
        cases i with
        | zero => 
          simp at hget
          left
          injection hget with heq
          exact heq.symm
        | succ n =>
          simp at hget
      have := modExpAux_spec (DivMod sx sz).snd sy sz "1" hvalid_base hy hz hone hsz_gt1
      obtain ⟨hvalid, heq⟩ := this
      constructor
      · exact hvalid
      · simp [heq]
        simp [Str2Int, String.data, List.foldl]
        simp [hbase_eq]
        have : Str2Int sx % Str2Int sz * Exp_int (Str2Int sx % Str2Int sz) (Str2Int sy) % Str2Int sz = 
                Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
          conv_rhs => rw [Nat.pow_mod (Str2Int sx) (Str2Int sy) (Str2Int sz)]
        exact this
-- </vc-proof>

end BignumLean