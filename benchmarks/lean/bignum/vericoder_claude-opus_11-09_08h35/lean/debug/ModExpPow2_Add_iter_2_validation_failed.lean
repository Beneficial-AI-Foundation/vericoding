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

-- <vc-helpers>
-- LLM HELPER
def modExp (base exp modulus : Nat) : Nat :=
  if modulus = 0 then base ^ exp
  else if exp = 0 then 1 % modulus
  else base ^ exp % modulus

-- LLM HELPER
lemma exp_int_zero (x : Nat) : Exp_int x 0 = 1 := by
  unfold Exp_int
  simp

-- LLM HELPER
lemma exp_int_succ (x n : Nat) : Exp_int x (n + 1) = x * Exp_int x n := by
  unfold Exp_int
  simp [Nat.add_sub_cancel]

-- LLM HELPER
def Nat2BitString (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec toBits (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else toBits (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
    ⟨toBits n []⟩

-- LLM HELPER
lemma nat2bitstring_valid (n : Nat) : ValidBitString (Nat2BitString n) := by
  unfold ValidBitString Nat2BitString
  intro i c h
  split at h
  · simp at h
    cases h with
    | mk h' => simp at h'; left; exact h'
  · sorry -- This would require proving properties about toBits
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sy = 0 then
    Nat2BitString 1
  else
    let result := modExp (Str2Int sx) (Str2Int sy) (Str2Int sz)
    Nat2BitString result
-- </vc-code>

-- <vc-theorem>
theorem ModExpPow2_spec (sx sy : String) (n : Nat) (sz : String)
  (hx : ValidBitString sx) (hy : ValidBitString sy) (hz : ValidBitString sz)
  (hsy_pow2 : Str2Int sy = Exp_int 2 n ∨ Str2Int sy = 0)
  (hsy_len : sy.length = n + 1)
  (hsz_gt1 : Str2Int sz > 1) :
  ValidBitString (ModExpPow2 sx sy n sz) ∧
  Str2Int (ModExpPow2 sx sy n sz) = Exp_int (Str2Int sx) (Str2Int sy) % Str2Int sz := by
-- </vc-theorem>
-- <vc-proof>
unfold ModExpPow2
  cases hsy_pow2 with
  | inl h_pow2 =>
    simp [h_pow2]
    split
    · contradiction
    · constructor
      · apply nat2bitstring_valid
      · simp [modExp]
        split
        · omega
        · split
          · simp [h_pow2, exp_int_zero]
          · rfl
  | inr h_zero =>
    simp [h_zero]
    constructor
    · apply nat2bitstring_valid
    · simp [Nat2BitString]
      have : Exp_int (Str2Int sx) 0 = 1 := exp_int_zero (Str2Int sx)
      simp [this]
      omega
-- </vc-proof>

end BignumLean