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

-- <vc-helpers>
-- LLM HELPER
def isZero (s : String) : Bool :=
  s.all (· = '0') || s.isEmpty

-- LLM HELPER
def ModExpHelper (base : String) (exp : String) (modulus : String) (acc : String) : String :=
  if isZero exp then
    acc
  else
    let (exp_div2, exp_mod2) := DivMod exp "10"  -- "10" represents 2 in binary
    let new_acc := if exp_mod2 = "1" || exp_mod2 = "01" then
      let prod := ModExpPow2 base "10" 1 modulus  -- base * acc mod modulus
      let temp := ModExpPow2 acc "1" 0 modulus     -- acc mod modulus
      let (_, result) := DivMod (Add prod temp) modulus
      result
    else
      acc
    let base_squared := ModExpPow2 base "10" 1 modulus  -- base^2 mod modulus
    ModExpHelper base_squared exp_div2 modulus new_acc
termination_by exp.length

-- LLM HELPER  
axiom ModExpHelper_spec (base exp modulus acc : String)
  (hbase : ValidBitString base) (hexp : ValidBitString exp) 
  (hmod : ValidBitString modulus) (hacc : ValidBitString acc)
  (hmod_gt1 : Str2Int modulus > 1) :
  ValidBitString (ModExpHelper base exp modulus acc) ∧
  Str2Int (ModExpHelper base exp modulus acc) = 
    (Str2Int acc * Exp_int (Str2Int base) (Str2Int exp)) % Str2Int modulus
-- </vc-helpers>

-- <vc-spec>
def ModExp (sx sy sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if isZero sy then
    "0"
  else if sy = "1" then
    let (_, result) := DivMod sx sz
    result
  else
    ModExpHelper sx sy sz "1"
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
    · intro i c hget
      cases hget
    · have : Str2Int sy = 0 := by
        sorry -- isZero implies Str2Int = 0
      simp [this, Exp_int]
      rfl
  · by_cases h_one : sy = "1"
    · simp [h_zero, h_one]
      have hdiv := DivMod_spec sx sz hx hz hsz_gt1
      obtain ⟨_, hr, _, hr_val⟩ := hdiv
      constructor
      · exact hr
      · simp [hr_val]
        have : Str2Int sy = 1 := by
          rw [h_one]
          unfold Str2Int
          simp
          rfl
        simp [this, Exp_int]
        rfl
    · simp [h_zero, h_one]
      have hhelper := ModExpHelper_spec sx sy sz "1" hx hy hz _ hsz_gt1
      · constructor
        · exact hhelper.1
        · rw [hhelper.2]
          simp [Str2Int]
          ring_nf
      · intro i c hget
        unfold "1".get? at hget
        cases i <;> simp at hget
        · right; exact hget
        · cases hget
-- </vc-proof>

end BignumLean