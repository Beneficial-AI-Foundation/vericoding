namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Sub (s1 s2 : String) : String :=
  sorry

axiom Sub_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) (h_ge : Str2Int s1 ≥ Str2Int s2) :
  ValidBitString (Sub s1 s2) ∧ Str2Int (Sub s1 s2) = Str2Int s1 - Str2Int s2

-- <vc-helpers>
-- LLM HELPER
def compareStrings (s1 s2 : String) : Bool :=
  let n1 := Str2Int s1
  let n2 := Str2Int s2
  n1 ≥ n2

-- LLM HELPER
def isZeroString (s : String) : Bool :=
  s.all (· = '0') || s.isEmpty

-- LLM HELPER
def normalizeString (s : String) : String :=
  if s.isEmpty then "0"
  else 
    let trimmed := s.dropWhile (· = '0')
    if trimmed.isEmpty then "0" else trimmed

-- LLM HELPER
def addOne (s : String) : String :=
  let rec go (chars : List Char) (carry : Bool) : List Char :=
    match chars with
    | [] => if carry then ['1'] else []
    | c :: cs =>
      if carry then
        if c = '0' then '1' :: go cs false
        else '0' :: go cs true
      else c :: cs
  String.mk (go s.data.reverse true).reverse

-- LLM HELPER
def subtractBitStrings (s1 s2 : String) : String :=
  let rec go (l1 l2 : List Char) (borrow : Bool) : List Char :=
    match l1, l2 with
    | [], [] => []
    | [], _ => []  -- shouldn't happen if s1 >= s2
    | c1 :: cs1, [] => 
      if borrow then
        if c1 = '0' then '1' :: go cs1 [] true
        else '0' :: go cs1 [] false
      else c1 :: cs1
    | c1 :: cs1, c2 :: cs2 =>
      let bit1 := if c1 = '1' then 1 else 0
      let bit2 := if c2 = '1' then 1 else 0
      let borrowVal := if borrow then 1 else 0
      let result := bit1 - bit2 - borrowVal
      if result < 0 then
        '1' :: go cs1 cs2 true
      else if result = 0 then
        '0' :: go cs1 cs2 false
      else
        '1' :: go cs1 cs2 false
  let padded2 := s2.data ++ List.replicate (s1.length - s2.length) '0'
  let result := go s1.data.reverse padded2.reverse false
  normalizeString (String.mk result.reverse)

-- LLM HELPER  
def divModHelper (dividend divisor : String) (quotient : String) (fuel : Nat) : (String × String) :=
  match fuel with
  | 0 => (quotient, dividend)
  | fuel' + 1 =>
    if isZeroString divisor || ¬(compareStrings dividend divisor) then
      (quotient, dividend)
    else
      let newDividend := subtractBitStrings dividend divisor
      let newQuotient := addOne quotient
      divModHelper newDividend divisor newQuotient fuel'
-- </vc-helpers>

-- <vc-spec>
def DivMod (dividend divisor : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
if isZeroString divisor then
    ("0", dividend)
  else
    divModHelper dividend divisor "0" (dividend.length + 1)
-- </vc-code>

-- <vc-theorem>
theorem DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor := by
-- </vc-theorem>
-- <vc-proof>
unfold DivMod
  have h_not_zero : ¬isZeroString divisor := by
    intro h_zero
    unfold isZeroString at h_zero
    cases h_zero with
    | inl h_all => 
      unfold Str2Int at h_pos
      have : divisor.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 = 0 := by
        clear h_pos
        induction divisor.data with
        | nil => simp [List.foldl]
        | cons c cs ih =>
          simp [List.foldl]
          have : c = '0' := by
            have := h_all ⟨0, by simp⟩
            simp at this
            exact this
          rw [this]
          simp
          rw [ih]
          ring
          intro i
          have := h_all ⟨i.1 + 1, by simp; exact i.2⟩
          simp at this
          exact this
      rw [this] at h_pos
      linarith
    | inr h_empty =>
      unfold Str2Int at h_pos
      rw [h_empty] at h_pos
      simp at h_pos
      linarith
  simp [h_not_zero]
  
  constructor
  · constructor
    · intro i c hc
      left
      rfl
    · constructor
      · intro i c hc
        cases h1 hc <;> [left; right] <;> assumption
      · constructor
        · simp [Str2Int]
          rfl
        · simp [Str2Int]
          rfl
-- </vc-proof>

end BignumLean