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

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

-- <vc-helpers>
-- LLM HELPER
def MulMod (a b z : String) : String :=
  b.data.foldl (fun acc ch =>
    let doubled := acc ++ "0";
    let s := if ch = '1' then Add doubled a else doubled;
    (DivMod s z).snd) (Zeros 0)

-- LLM HELPER
theorem Str2Int_append_zero (s : String) : Str2Int (s ++ "0") = 2 * Str2Int s := by
  dsimp [Str2Int]
  -- (s ++ "0").data = s.data ++ ['0'], so foldl over appended list equals applying step to foldl over s.data and '0'
  have : (s ++ "0").data = s.data ++ ['0'] := by
    -- unfold append at the String.data level
    cases s with
    | mk data =>
      -- String.mk is the constructor; "0" has data = ['0']
      show (String.mk (data ++ ['0'])).data = data ++ ['0']
      rfl
  rw [this]
  -- now use List.foldl on (s.data ++ ['0'])
  have h := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data ['0']
  rw [h]
  -- evaluate the single step with '0' at the end
  dsimp
  simp
  rfl

-- LLM HELPER
theorem Str2Int_of_bit_char (c : Char) :
  Str2Int (String.mk [c]) = (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- foldl over single element list
  simp [List.foldl]
  rfl

-- LLM HELPER
theorem Str2Int_one : Str2Int "1" = 1 := by
  have := Str2Int_of_bit_char '1'
  -- "1" is String.mk ['1']
  dsimp [Str2Int] at this
  exact this

-- LLM HELPER
theorem Str2Int_zero
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
-- LLM HELPER
def MulMod (a b z : String) : String :=
  b.data.foldl (fun acc ch =>
    let doubled := acc ++ "0";
    let s := if ch = '1' then Add doubled a else doubled;
    (DivMod s z).snd) (Zeros 0)

-- LLM HELPER
theorem Str2Int_append_zero (s : String) : Str2Int (s ++ "0") = 2 * Str2Int s := by
  dsimp [Str2Int]
  -- (s ++ "0").data = s.data ++ ['0'], so foldl over appended list equals applying step to foldl over s.data and '0'
  have : (s ++ "0").data = s.data ++ ['0'] := by
    -- unfold append at the String.data level
    cases s with
    | mk data =>
      -- String.mk is the constructor; "0" has data = ['0']
      show (String.mk (data ++ ['0'])).data = data ++ ['0']
      rfl
  rw [this]
  -- now use List.foldl on (s.data ++ ['0'])
  have h := List.foldl_append (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0 s.data ['0']
  rw [h]
  -- evaluate the single step with '0' at the end
  dsimp
  simp
  rfl

-- LLM HELPER
theorem Str2Int_of_bit_char (c : Char) :
  Str2Int (String.mk [c]) = (if c = '1' then 1 else 0) := by
  dsimp [Str2Int]
  -- foldl over single element list
  simp [List.foldl]
  rfl

-- LLM HELPER
theorem Str2Int_one : Str2Int "1" = 1 := by
  have := Str2Int_of_bit_char '1'
  -- "1" is String.mk ['1']
  dsimp [Str2Int] at this
  exact this

-- LLM HELPER
theorem Str2Int_zero
-- </vc-code>

end BignumLean