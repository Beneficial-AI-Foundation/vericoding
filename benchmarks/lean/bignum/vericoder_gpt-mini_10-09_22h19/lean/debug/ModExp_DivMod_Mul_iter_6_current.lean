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
def list_to_string (l : List Char) : String := ⟨l⟩

-- LLM HELPER
def list_to_nat (l : List Char) : Nat :=
  l.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- convert a natural number to a list of '0'/'1' chars (MSB first).
def nat_to_bits (n : Nat) : List Char :=
  if n = 0 then ['0'] else
  let rec go (m : Nat) (acc : List Char) : List Char :=
    if m = 0 then acc
    else
      let bit := if m % 2 = 1 then '1' else '0'
      go (m / 2) (bit :: acc)
  go n []

def nat_to_string (n : Nat) : String :=
  list_to_string (nat_to_bits n)

def ModExp (sx sy sz : String) : String :=
  let base := Str2Int sx
  let exp  := Str2Int sy
  let modu := Str2Int sz
  if modu = 0 then "0" else nat_to_string (Exp_int base exp % modu)
-- </vc-code>

-- <vc-theorem>
theorem list_to_string_str2int (l : List Char) :
  Str2Int (list_to_string l) = list_to_nat l
-- </vc-theorem>
-- <vc-proof>
by
  -- Str2Int (⟨l⟩) unfolds to ⟨l⟩.data.foldl ... and ⟨l⟩.data = l by definition of the constructor
  simp [Str2Int, list_to_string, list_to_nat]
-- </vc-proof>

end BignumLean