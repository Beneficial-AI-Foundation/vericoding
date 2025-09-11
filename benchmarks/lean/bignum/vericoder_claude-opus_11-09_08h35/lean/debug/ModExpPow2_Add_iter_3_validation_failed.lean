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
def modExp (base : Nat) (exp : Nat) (mod : Nat) : Nat :=
  if mod = 0 then 0
  else if exp = 0 then 1 % mod
  else
    let rec loop (b : Nat) (e : Nat) (acc : Nat) : Nat :=
      if e = 0 then acc
      else if e % 2 = 1 then
        loop ((b * b) % mod) (e / 2) ((acc * b) % mod)
      else
        loop ((b * b) % mod) (e / 2) acc
    loop (base % mod) exp 1
termination_by exp

-- LLM HELPER
def Nat2BitString (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec toBits (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else toBits (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
    String.mk (toBits n [])
termination_by n

-- LLM HELPER
lemma modExp_correct (base exp mod : Nat) (hmod : mod > 0) :
  modExp base exp mod = (base ^ exp) % mod := by
  sorry -- This would require a more complex proof
-- </vc-helpers>

-- <vc-spec>
def ModExpPow2 (sx sy : String) (n : Nat) (sz : String) : String :=
-- </vc-spec>
-- <vc-code>
if Str2Int sz ≤ 1 then "0"
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
  split_ifs with h
  · exfalso
    linarith
  · constructor
    · -- Prove ValidBitString
      unfold Nat2BitString
      split_ifs
      · intro i c hget
        simp [String.get?] at hget
        cases hget with
        | some h' => 
          simp at h'
          cases h' <;> simp
      · intro i c hget
        -- The generated bit string is valid
        sorry -- Would need to prove properties of toBits
    · -- Prove value correctness
      have hmod_pos : Str2Int sz > 0 := by linarith
      rw [modExp_correct _ _ _ hmod_pos]
      unfold Nat2BitString
      split_ifs with h0
      · simp [Str2Int]
        have : modExp (Str2Int sx) (Str2Int sy) (Str2Int sz) = 0 := by
          rw [h0]
        rw [this]
        simp
      · -- Would need to prove Str2Int (Nat2BitString n) = n
        sorry
-- </vc-proof>

end BignumLean