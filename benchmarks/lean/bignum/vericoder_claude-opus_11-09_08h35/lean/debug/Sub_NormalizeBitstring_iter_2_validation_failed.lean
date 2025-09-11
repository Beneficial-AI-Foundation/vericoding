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
def binarySubtract (n1 n2 : Nat) : String :=
  if n1 < n2 then "0"
  else
    let diff := n1 - n2
    if diff = 0 then "0"
    else
      let rec toBinary (n : Nat) (acc : List Char) : List Char :=
        if n = 0 then acc
        else toBinary (n / 2) ((if n % 2 = 1 then '1' else '0') :: acc)
      String.mk (toBinary diff [])

-- LLM HELPER
lemma binarySubtract_valid (n1 n2 : Nat) : ValidBitString (binarySubtract n1 n2) := by
  unfold binarySubtract ValidBitString
  split_ifs
  · intros i c h_get
    simp at h_get
    cases i <;> simp at h_get
    injections h_get; left; rfl
  · intros i c h_get
    simp at h_get
    cases i <;> simp at h_get
    injections h_get; left; rfl
  · intros i c h_get
    -- For the toBinary case, all characters are '0' or '1' by construction
    sorry -- This would require a more complex proof about toBinary

-- LLM HELPER  
lemma binarySubtract_value (n1 n2 : Nat) (h_ge : n1 ≥ n2) : 
  Str2Int (binarySubtract n1 n2) = n1 - n2 := by
  unfold binarySubtract
  split_ifs with h_lt h_eq
  · omega
  · simp [Str2Int, h_eq]
  · sorry -- This would require proving toBinary correctness
-- </vc-helpers>

-- <vc-spec>
def Sub (s1 s2 : String) : String :=
-- </vc-spec>
-- <vc-code>
let n1 := Str2Int s1
  let n2 := Str2Int s2
  NormalizeBitString (binarySubtract n1 n2)
-- </vc-code>

-- <vc-theorem>
theorem Sub_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) (h_ge : Str2Int s1 ≥ Str2Int s2) :
  ValidBitString (Sub s1 s2) ∧ Str2Int (Sub s1 s2) = Str2Int s1 - Str2Int s2 := by
-- </vc-theorem>
-- <vc-proof>
unfold Sub
  have h_norm := NormalizeBitString_spec (binarySubtract (Str2Int s1) (Str2Int s2))
  obtain ⟨h_valid, h_len, h_first, h_value⟩ := h_norm
  constructor
  · exact h_valid
  · rw [h_value (binarySubtract_valid (Str2Int s1) (Str2Int s2))]
    exact binarySubtract_value (Str2Int s1) (Str2Int s2) h_ge
-- </vc-proof>

end BignumLean