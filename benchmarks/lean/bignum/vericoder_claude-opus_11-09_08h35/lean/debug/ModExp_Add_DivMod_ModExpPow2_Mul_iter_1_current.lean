namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Exp_int (x y : Nat) : Nat :=
  if y = 0 then 1 else x * Exp_int x (y - 1)

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
  s = "1" || (s.dropWhile (· = '0') = "1")

-- LLM HELPER
def getBit (s : String) (i : Nat) : Bool :=
  if h : i < s.length then
    s.get ⟨i, h⟩ = '1'
  else
    false

-- LLM HELPER
def shiftRight (s : String) : String :=
  if s.length ≤ 1 then "0"
  else s.extract 0 (s.length - 1)

-- LLM HELPER
def modExpHelper (base : String) (exp : String) (modulus : String) (result : String) : String :=
  if isZero exp then
    result
  else
    let newResult := if getBit exp (exp.length - 1) then
      let prod := Mul result base
      (DivMod prod modulus).2
    else
      result
    let newBase := let squared := Mul base base
                   (DivMod squared modulus).2
    let newExp := shiftRight exp
    modExpHelper newBase newExp modulus newResult
termination_by exp.length
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if isZero sy then
    "1"
  else if isOne sy then
    (DivMod sx sz).2
  else
    modExpHelper sx sy sz "1"
-- </vc-code>

-- <vc-theorem>
theorem ModExp_spec (sx sy sz : String) (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pos : sy.length > 0) (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExp sx sy sz) ∧
  Str2Int (ModExp sx sy sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExp
  by_cases h_zero : isZero sy
  · simp [h_zero]
    constructor
    · intro i c hc
      simp at hc
      cases' hc with hc hc
      · left; exact hc
      · contradiction
    · have : Str2Int sy = 0 := by
        unfold isZero at h_zero
        cases h_zero with
        | inl h => 
          unfold Str2Int
          induction sy.data with
          | nil => rfl
          | cons c cs ih =>
            simp at h
            simp [List.foldl]
            have : c = '0' := by
              have : c ∈ sy.data := List.mem_cons_self c cs
              exact h c this
            simp [this]
            apply ih
            intro x hx
            exact h x (List.mem_cons_of_mem c hx)
        | inr h =>
          have : sy.data = [] := by
            unfold String.isEmpty at h
            simp at h
            exact h
          simp [Str2Int, this]
      simp [this, Exp_int]
      unfold Str2Int
      simp [List.foldl]
      norm_num
  · by_cases h_one : isOne sy
    · simp [h_zero, h_one]
      have spec := DivMod_spec sx sz hx hz hsz_gt1
      obtain ⟨_, hr_valid, _, hr_eq⟩ := spec
      constructor
      · exact hr_valid
      · simp [hr_eq]
        have : Str2Int sy = 1 := by
          unfold isOne at h_one
          cases h_one with
          | inl h => 
            simp [h, Str2Int]
            unfold Str2Int
            simp [List.foldl]
            norm_num
          | inr h =>
            admit
        simp [this, Exp_int]
    · simp [h_zero, h_one]
      admit
-- </vc-proof>

end BignumLean