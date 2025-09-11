namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

def AllZero (s : String) : Prop :=
  ∀ i, s.get? i = some '0'

def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
  sorry

axiom ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def Zeros (n : Nat) : String :=
  sorry

axiom Zeros_spec (n : Nat) :
  let s := Zeros n
  s.length = n ∧ ValidBitString s ∧ Str2Int s = 0 ∧ AllZero s

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
def IsEven (s : String) : Bool :=
  match s.data.getLast? with
  | some '0' => true
  | _ => false

-- LLM HELPER
def ShiftRight (s : String) : String :=
  if s.data.length ≤ 1 then "0"
  else ⟨s.data.dropLast⟩

-- LLM HELPER
def ModExpAux (base exp modulus result : String) (fuel : Nat) : String :=
  match fuel with
  | 0 => result
  | fuel' + 1 =>
    if Str2Int exp = 0 then
      result
    else
      let newResult := if IsEven exp then result else (DivMod (Mul result base) modulus).2
      let newBase := (DivMod (Mul base base) modulus).2
      let newExp := ShiftRight exp
      ModExpAux newBase newExp modulus newResult fuel'

-- LLM HELPER
lemma str2int_one : Str2Int "1" = 1 := by
  unfold Str2Int
  simp

-- LLM HELPER  
lemma str2int_zero : Str2Int "0" = 0 := by
  unfold Str2Int
  simp

-- LLM HELPER
lemma validbitstring_one : ValidBitString "1" := by
  unfold ValidBitString
  intros i c h
  simp at h
  cases h with
  | inl h => simp [h]; right; rfl
  | inr h => contradiction

-- LLM HELPER
lemma validbitstring_zero : ValidBitString "0" := by
  unfold ValidBitString
  intros i c h
  simp at h
  cases h with
  | inl h => simp [h]; left; rfl
  | inr h => contradiction
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    "1"
  else if Str2Int sz = 1 then
    "0"
  else
    let fuel := sy.length
    ModExpAux (DivMod sx sz).2 sy sz "1" fuel
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
  · constructor
    · exact validbitstring_one
    · rw [str2int_one]
      unfold Exp_int
      simp
      have : 1 < Str2Int sz := hsz_gt1
      exact Nat.mod_eq_of_lt this
  · split
    · constructor
      · exact validbitstring_zero
      · rw [str2int_zero]
        simp [Nat.mod_one]
    · have hsz_pos : Str2Int sz > 0 := Nat.lt_trans Nat.zero_lt_one hsz_gt1
      have hmod := DivMod_spec sx sz hx hz hsz_pos
      constructor
      · have h1 := DivMod_spec (Mul "1" (DivMod sx sz).2) sz 
          (Mul_spec "1" (DivMod sx sz).2 validbitstring_one hmod.2.1).1 hz hsz_pos
        have h2 := DivMod_spec (Mul (DivMod sx sz).2 (DivMod sx sz).2) sz 
          (Mul_spec (DivMod sx sz).2 (DivMod sx sz).2 hmod.2.1 hmod.2.1).1 hz hsz_pos
        exact validbitstring_one
      · simp [ModExpAux]
        split
        · rw [str2int_one]
          unfold Exp_int
          simp
          have : 1 < Str2Int sz := hsz_gt1
          exact Nat.mod_eq_of_lt this
        · rw [str2int_one]
          have : Str2Int (DivMod sx sz).2 = Str2Int sx % Str2Int sz := hmod.2.2.2
          rw [this]
          rfl
-- </vc-proof>

end BignumLean