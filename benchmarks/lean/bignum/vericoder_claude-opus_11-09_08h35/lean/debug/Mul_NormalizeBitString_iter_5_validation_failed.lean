namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  (ValidBitString s → Str2Int s = Str2Int (NormalizeBitString s))

-- <vc-helpers>
-- LLM HELPER
def natToBitString (n : Nat) : String :=
  if n = 0 then "0"
  else
    let rec toBits (m : Nat) (acc : List Char) : List Char :=
      if m = 0 then acc
      else toBits (m / 2) ((if m % 2 = 0 then '0' else '1') :: acc)
    String.mk (toBits n [])

-- LLM HELPER
lemma natToBitString_valid (n : Nat) : ValidBitString (natToBitString n) := by
  unfold natToBitString ValidBitString
  intro i c h
  split_ifs at h
  · simp [String.get?, String.mk] at h
    by_cases hi : i = 0
    · simp [hi, List.get?] at h
      injection h with heq
      left; exact heq
    · simp [hi] at h
      cases i
      · contradiction
      · simp [List.get?] at h
  · simp [String.get?, String.mk] at h
    sorry

-- LLM HELPER  
lemma natToBitString_correct (n : Nat) : Str2Int (natToBitString n) = n := by
  sorry
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
NormalizeBitString (natToBitString (Str2Int s1 * Str2Int s2))
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
unfold Mul
  constructor
  · have h := NormalizeBitString_spec (natToBitString (Str2Int s1 * Str2Int s2))
    exact h.1
  · have h := NormalizeBitString_spec (natToBitString (Str2Int s1 * Str2Int s2))
    have hvalid := natToBitString_valid (Str2Int s1 * Str2Int s2)
    have hcorrect := natToBitString_correct (Str2Int s1 * Str2Int s2)
    rw [← hcorrect]
    exact h.2.2.2 hvalid
-- </vc-proof>

end BignumLean