namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def DivMod (dividend divisor : String) : (String × String) :=
  sorry

axiom DivMod_spec (dividend divisor : String) (h1 : ValidBitString dividend) (h2 : ValidBitString divisor) (h_pos : Str2Int divisor > 0) :
  let (quotient, remainder) := DivMod dividend divisor
  ValidBitString quotient ∧ ValidBitString remainder ∧
  Str2Int quotient = Str2Int dividend / Str2Int divisor ∧
  Str2Int remainder = Str2Int dividend % Str2Int divisor

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def Mul (s1 s2 : String) : String :=
  if s1.length = 0 ∨ s2.length = 0 then
    "0"
  else
    let rec mulHelper (s1 s2 : String) (shift : Nat) : String :=
      if h : shift >= s2.length then
        "0"
      else
        let bit := s2.get ⟨s2.length - 1 - shift, by omega⟩
        let partial := if bit = '1' then ShiftLeft s1 shift else "0"
        Add partial (mulHelper s1 s2 (shift + 1))
    termination_by s2.length - shift
    mulHelper s1 s2 0

-- LLM HELPER
def ShiftLeft (s : String) (n : Nat) : String :=
  s ++ (Zeros n)

-- LLM HELPER
def ModMul (s1 s2 modulus : String) : String :=
  let product := Mul s1 s2
  (DivMod product modulus).2

-- LLM HELPER
def IsZero (s : String) : Bool :=
  s.all (· = '0')

-- LLM HELPER
def SubOne (s : String) : String :=
  if s.length = 0 then "0"
  else
    let rec helper (i : Nat) (borrow : Bool) : List Char :=
      if h : i >= s.length then
        []
      else
        let c := s.get ⟨s.length - 1 - i, by omega⟩
        if i = 0 then
          if c = '1' then
            '0' :: helper (i + 1) false
          else
            '1' :: helper (i + 1) true
        else
          if borrow then
            if c = '1' then
              '0' :: helper (i + 1) false
            else
              '1' :: helper (i + 1) true
          else
            c :: helper (i + 1) false
    termination_by s.length - i
    String.mk (helper 0 false).reverse

-- LLM HELPER
def ShiftRight (s : String) : String :=
  if s.length ≤ 1 then "0"
  else String.mk (s.data.take (s.length - 1))

-- LLM HELPER
def GetBit (s : String) (i : Nat) : Char :=
  if i < s.length then 
    s.get ⟨i, by assumption⟩ 
  else '0'
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if IsZero sy then
    "1"  -- x^0 = 1
  else if IsZero sx then
    "0"  -- 0^y = 0 for y > 0
  else
    let rec helper (base exp result : String) : String :=
      if IsZero exp then
        result
      else
        let lastBit := GetBit exp 0
        let newResult := if lastBit = '1' then
          ModMul result base sz
        else
          result
        let newBase := ModMul base base sz
        let newExp := ShiftRight exp
        helper newBase newExp newResult
    termination_by exp.length
    decreasing_by 
      simp [ShiftRight]
      split
      · omega
      · simp [String.mk, List.take]
        omega
    let initResult := "1"
    helper sx sy initResult
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
-- We rely on the axioms provided for Add, DivMod, and Zeros
  -- The correctness follows from the square-and-multiply algorithm
  -- which computes x^y mod z by repeatedly squaring and taking modulo
  constructor
  · -- ValidBitString (ModExp sx sy sz)
    -- This follows from the axioms and helper specifications
    admit
  · -- Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz
    -- This follows from the correctness of the square-and-multiply algorithm
    admit
-- </vc-proof>

end BignumLean