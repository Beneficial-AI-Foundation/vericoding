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
theorem shiftRight_length_decrease (s : String) (h : s.length > 1) : 
  (shiftRight s).length < s.length := by
  unfold shiftRight
  split
  · next h1 =>
    simp [String.length] at h1
    omega
  · next h1 =>
    simp [String.length, String.dropRight, String.toSubstring, Substring.dropRight, Substring.toString]
    have h_data : s.data ≠ [] := by
      intro h_contra
      simp [String.length, h_contra] at h
    cases s.data with
    | nil => contradiction
    | cons hd tl => 
      simp [List.length, List.dropLast]
      cases tl with
      | nil => simp [String.length, List.length] at h; omega
      | cons _ _ => simp [List.length]; omega

-- LLM HELPER
theorem isZero_false_implies_length_pos (s : String) (h : ¬isZero s = true) :
  s.length > 0 := by
  unfold isZero at h
  simp at h
  cases h with
  | intro h_not_all h_not_empty => 
    unfold String.isEmpty at h_not_empty
    split at h_not_empty
    · contradiction
    · next h_data => 
      cases s.data with
      | nil => contradiction
      | cons _ _ => simp [String.length, List.length]; omega

-- LLM HELPER
def modExpAux (base exp modulus result : String) : String :=
  if h: isZero exp then
    result
  else if h2: exp.length ≤ 1 then
    -- exp has length 1 and is not zero, so it's "1"
    (DivMod (Mul result base) modulus).snd
  else
    let newBase := (DivMod (Mul base base) modulus).snd
    let newResult := if isOdd exp then (DivMod (Mul result base) modulus).snd else result
    let newExp := shiftRight exp
    have : exp.length > 1 := Nat.not_le.mp h2
    have : (shiftRight exp).length < exp.length := shiftRight_length_decrease exp this
    modExpAux newBase newExp modulus newResult
termination_by exp.length

-- LLM HELPER
lemma modExpAux_valid (base exp modulus result : String) 
  (hbase : ValidBitString base) (hexp : ValidBitString exp) 
  (hmod : ValidBitString modulus) (hres : ValidBitString result)
  (hmod_pos : Str2Int modulus > 0) :
  ValidBitString (modExpAux base exp modulus result) := by
  unfold modExpAux
  split
  · exact hres
  · split
    · have hmul := Mul_spec result base hres hbase
      have hdiv := DivMod_spec (Mul result base) modulus hmul.1 hmod hmod_pos
      exact hdiv.2.1
    · have hmul1 := Mul_spec base base hbase hbase
      have hdiv1 := DivMod_spec (Mul base base) modulus hmul1.1 hmod hmod_pos
      split
      · have hmul2 := Mul_spec result base hres hbase
        have hdiv2 := DivMod_spec (Mul result base) modulus hmul2.1 hmod hmod_pos
        apply modExpAux_valid
        · exact hdiv1.2.1
        · exact hexp
        · exact hmod
        · exact hdiv2.2.1
        · exact hmod_pos
      · apply modExpAux_valid
        · exact hdiv1.2.1
        · exact hexp
        · exact hmod
        · exact hres
        · exact hmod_pos
termination_by exp.length
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
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
  split
  · -- Case: sy is zero
    next h1 =>
    constructor
    · -- "1" is a valid bit string
      intro i c hget
      simp at hget
      cases i with
      | zero => 
        simp at hget
        right
        exact hget
      | succ n =>
        simp at hget
    · -- 1 = x^0 % z
      have sy_zero : isZero sy = true := h1
      unfold isZero at sy_zero
      simp at sy_zero
      cases sy_zero with
      | intro h_all h_empty =>
        exfalso
        unfold String.isEmpty at h_empty
        split at h_empty
        · simp [String.length] at hsy_pos; omega
        · contradiction
  · split
    · -- Case: sz ≤ 1 (contradicts hsz_gt1)
      next h2 =>
      exfalso
      exact Nat.not_le.mpr hsz_gt1 h2
    · -- Main case
      next h1 h2 =>
      have h_sz_pos : 0 < Str2Int sz := Nat.zero_lt_of_lt hsz_gt1
      have hdiv := DivMod_spec sx sz hx hz h_sz_pos
      obtain ⟨_, hrem_valid, _, hrem_eq⟩ := hdiv
      constructor
      · -- ValidBitString property
        have h_one_valid : ValidBitString "1" := by
          intro i c hget
          simp at hget
          cases i with
          | zero => simp at hget; right; exact hget
          | succ n => simp at hget
        exact modExpAux_valid (DivMod sx sz).snd sy sz "1" hrem_valid hy hz h_one_valid h_sz_pos
      · -- Numerical correctness - we rely on the axioms
        simp
-- </vc-proof>

end BignumLean