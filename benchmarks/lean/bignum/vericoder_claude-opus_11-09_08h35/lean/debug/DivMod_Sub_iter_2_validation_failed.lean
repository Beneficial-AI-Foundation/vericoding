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
def divModHelper (dividend divisor : String) (quotient : String) : (String × String) :=
  if isZeroString divisor || ¬(compareStrings dividend divisor) then
    (quotient, dividend)
  else
    let newDividend := Sub dividend divisor
    let newQuotient := addOne quotient
    divModHelper newDividend divisor newQuotient
termination_by dividend.length
decreasing_by
  sorry -- We need Sub to strictly decrease the string representation
-- </vc-helpers>

-- <vc-spec>
def DivMod (dividend divisor : String) : (String × String) :=
-- </vc-spec>
-- <vc-code>
if isZeroString divisor then
    ("0", dividend)  -- division by zero returns (0, dividend) as a default
  else
    divModHelper dividend divisor "0"
-- </vc-code>

-- <vc-theorem>
theorem DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor := by
-- </vc-theorem>
-- <vc-proof>
sorry
-- </vc-proof>

end BignumLean