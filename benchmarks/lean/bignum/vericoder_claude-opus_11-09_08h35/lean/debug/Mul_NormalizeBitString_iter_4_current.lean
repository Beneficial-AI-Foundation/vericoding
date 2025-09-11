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
  split_ifs
  · intros i c h
    simp [String.get?, String.mk] at h
    cases' List.get? ['0'] i with x
    · simp at h
    · simp at h
      cases h
      left; rfl
  · intro i c h
    simp only [String.get?, String.mk] at h
    generalize hbs : natToBitString.toBits n [] = bs
    rw [hbs] at h
    have : c ∈ bs := List.mem_of_get?
-- </vc-helpers>

-- <vc-spec>
def Mul (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
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
  split_ifs
  · intros i c h
    simp [String.get?, String.mk] at h
    cases' List.get? ['0'] i with x
    · simp at h
    · simp at h
      cases h
      left; rfl
  · intro i c h
    simp only [String.get?, String.mk] at h
    generalize hbs : natToBitString.toBits n [] = bs
    rw [hbs] at h
    have : c ∈ bs := List.mem_of_get?
-- </vc-code>

-- <vc-theorem>
theorem Mul_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  ValidBitString (Mul s1 s2) ∧ Str2Int (Mul s1 s2) = Str2Int s1 * Str2Int s2 := by
-- </vc-theorem>
end BignumLean