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
def mul_aux : String → Nat → String
| s1, 0        => ""
| s1, Nat.succ n => Add s1 (mul_aux s1 n)
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
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
      simp [mul_aux, Str2Int]
      constructor
      · intro i c h; cases h
      · rfl
    | succ m ih =>
      rcases ih with ⟨ihV, ihN⟩
      have add_spec := Add_spec s1 (mul_aux s1 m) h1 ihV
      rcases add_spec with ⟨v_eq, sum_eq⟩
      constructor
      · exact v_eq
      · calc
          Str2Int (mul_aux s1 (m+1)) = Str2Int (Add s1 (mul_aux s1 m)) := rfl
          _ = Str2Int s1 + Str2Int (mul_aux s1 m) := sum_eq
          _ = Str2Int s1 + m * Str2Int s1 := by rw [ihN]
          _ = (m+1) * Str2Int s1 := by
            -- rearrange to the desired multiplication form
            rw [Nat.add_comm, Nat.mul_comm, ←Nat.mul_add, Nat.mul_comm]
  exact all n
-- </vc-proof>

end BignumLean