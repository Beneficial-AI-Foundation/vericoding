namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def Add (s1 s2 : String) : String :=
  sorry

axiom Add_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Add s1 s2) ∧ Str2Int (Add s1 s2) = Str2Int s1 + Str2Int s2

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s))

-- <vc-helpers>
-- LLM HELPER
-- (No extra helpers required here.)
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
def mul_aux : String -> Nat -> String
| s1, 0 => ""            -- empty string represents 0, Str2Int "" = 0
| s1, Nat.succ n => Add s1 (mul_aux s1 n)

def Mul (s1 s2 : String) : String :=
  mul_aux s1 (Str2Int s2)
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2
-- </vc-theorem>
-- <vc-proof>
by
  intro s1 s2 h1 h2
  let n := Str2Int s2
  have all : ∀ m, ValidBitString (mul_aux s1 m) ∧ Str2Int (mul_aux s1 m) = m * Str2Int s1 := by
    intro m
    induction m with
    | zero =>
      -- mul_aux s1 0 = ""
      simp [mul_aux]
      constructor
      · intros i c h; cases h
      · simp [mul_aux, Str2Int]
    | succ m ih =>
      rcases ih with ⟨ihV, ihN⟩
      -- mul_aux s1 (m+1) = Add s1 (mul_aux s1 m)
      have add_spec := Add_spec s1 (mul_aux s1 m) h1 ihV
      rcases add_spec with ⟨v, eq⟩
      constructor
      · exact v
      · -- Str2Int (Add s1 (mul_aux s1 m)) = Str2Int s1 + Str2Int (mul_aux s1 m)
        -- use ihN to replace Str2Int (mul_aux s1 m) and algebra to get (m+1) * Str2Int s1
        calc
          Str2Int (mul_aux s1 (m+1)) = Str2Int (Add s1 (mul_aux s1 m)) := rfl
          _ = Str2Int s1 + Str2Int (mul_aux s1 m) := eq
          _ = Str2Int s1 + m * Str2Int s1 := by rw [ihN]
          _ = (m+1) * Str2Int s1 := by
            -- (m+1) * k = k * (m+1) = k*m + k = k + m*k
            rw [Nat.mul_comm, Nat.mul_add, Nat.mul_one, Nat.add_comm]
  exact (all n)
-- </vc-proof>

end BignumLean