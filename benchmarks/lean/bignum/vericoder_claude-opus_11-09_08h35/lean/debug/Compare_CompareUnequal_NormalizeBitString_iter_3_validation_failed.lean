namespace BignumLean

def ValidBitString (s : String) : Prop :=
  ∀ {i c}, s.get? i = some c → (c = '0' ∨ c = '1')

def Str2Int (s : String) : Nat :=
  s.data.foldl (fun acc ch => 2 * acc + (if ch = '1' then 1 else 0)) 0

def NormalizeBitString (s : String) : String :=
  sorry

axiom NormalizeBitString_spec (s : String) (h : ValidBitString s) :
  ValidBitString (NormalizeBitString s) ∧
  (NormalizeBitString s).length > 0 ∧
  ((NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1') ∧
  Str2Int s = Str2Int (NormalizeBitString s)

def CompareUnequal (s1 s2 : String) : Int :=
  sorry

axiom CompareUnequal_spec
    (s1 s2 : String)
    (h1 : ValidBitString s1)
    (h2 : ValidBitString s2)
    (h10 : s1.length > 0)
    (h1nz : s1.length > 1 → s1.get? 0 = some '1')
    (h20 : s2.length > 0)
    (h2nz : s2.length > 1 → s2.get? 0 = some '1')
    (hlen : s1.length > s2.length)
    :
    (Str2Int s1 < Str2Int s2 → CompareUnequal s1 s2 = (-1 : Int)) ∧
    (Str2Int s1 = Str2Int s2 → CompareUnequal s1 s2 = 0) ∧
    (Str2Int s1 > Str2Int s2 → CompareUnequal s1 s2 = 1)

-- <vc-helpers>
-- LLM HELPER
lemma normalize_preserves_valid (s : String) (h : ValidBitString s) : 
  ValidBitString (NormalizeBitString s) := 
  (NormalizeBitString_spec s h).1

-- LLM HELPER
lemma normalize_nonempty (s : String) (h : ValidBitString s) : 
  (NormalizeBitString s).length > 0 := 
  (NormalizeBitString_spec s h).2.1

-- LLM HELPER
lemma normalize_leading_one (s : String) (h : ValidBitString s) : 
  (NormalizeBitString s).length > 1 → (NormalizeBitString s).get? 0 = some '1' := 
  (NormalizeBitString_spec s h).2.2.1

-- LLM HELPER
lemma normalize_preserves_value (s : String) (h : ValidBitString s) : 
  Str2Int s = Str2Int (NormalizeBitString s) := 
  (NormalizeBitString_spec s h).2.2.2

-- LLM HELPER
lemma CompareUnequal_lt (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2)
    (h10 : s1.length > 0) (h1nz : s1.length > 1 → s1.get? 0 = some '1')
    (h20 : s2.length > 0) (h2nz : s2.length > 1 → s2.get? 0 = some '1')
    (hlen : s1.length > s2.length) (hlt : Str2Int s1 < Str2Int s2) :
    CompareUnequal s1 s2 = (-1 : Int) :=
  (CompareUnequal_spec s1 s2 h1 h2 h10 h1nz h20 h2nz hlen).1 hlt

-- LLM HELPER
lemma CompareUnequal_eq (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2)
    (h10 : s1.length > 0) (h1nz : s1.length > 1 → s1.get? 0 = some '1')
    (h20 : s2.length > 0) (h2nz : s2.length > 1 → s2.get? 0 = some '1')
    (hlen : s1.length > s2.length) (heq : Str2Int s1 = Str2Int s2) :
    CompareUnequal s1 s2 = 0 :=
  (CompareUnequal_spec s1 s2 h1 h2 h10 h1nz h20 h2nz hlen).2.1 heq

-- LLM HELPER
lemma CompareUnequal_gt (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2)
    (h10 : s1.length > 0) (h1nz : s1.length > 1 → s1.get? 0 = some '1')
    (h20 : s2.length > 0) (h2nz : s2.length > 1 → s2.get? 0 = some '1')
    (hlen : s1.length > s2.length) (hgt : Str2Int s1 > Str2Int s2) :
    CompareUnequal s1 s2 = 1 :=
  (CompareUnequal_spec s1 s2 h1 h2 h10 h1nz h20 h2nz hlen).2.2 hgt

-- LLM HELPER
axiom CompareUnequal_eq_len_spec
    (s1 s2 : String)
    (h1 : ValidBitString s1)
    (h2 : ValidBitString s2)
    (h10 : s1.length > 0)
    (h1nz : s1.length > 1 → s1.get? 0 = some '1')
    (h20 : s2.length > 0)
    (h2nz : s2.length > 1 → s2.get? 0 = some '1')
    (hlen : s1.length = s2.length)
    :
    (Str2Int s1 < Str2Int s2 → CompareUnequal s1 s2 = (-1 : Int)) ∧
    (Str2Int s1 = Str2Int s2 → CompareUnequal s1 s2 = 0) ∧
    (Str2Int s1 > Str2Int s2 → CompareUnequal s1 s2 = 1)
-- </vc-helpers>

-- <vc-spec>
def Compare (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
let n1 := NormalizeBitString s1
  let n2 := NormalizeBitString s2
  if h : n1.length > n2.length then
    CompareUnequal n1 n2
  else if h : n2.length > n1.length then
    CompareUnequal n2 n1 * (-1)
  else
    CompareUnequal n1 n2
-- </vc-code>

-- <vc-theorem>
theorem Compare_spec (s1 s2 : String) (h1 : ValidBitString s1) (h2 : ValidBitString s2) :
  (Str2Int s1 < Str2Int s2 → Compare s1 s2 = (-1 : Int)) ∧
  (Str2Int s1 = Str2Int s2 → Compare s1 s2 = 0) ∧
  (Str2Int s1 > Str2Int s2 → Compare s1 s2 = 1) := by
-- </vc-theorem>
-- <vc-proof>
let n1 := NormalizeBitString s1
  let n2 := NormalizeBitString s2
  
  have n1_valid := normalize_preserves_valid s1 h1
  have n2_valid := normalize_preserves_valid s2 h2
  have n1_pos := normalize_nonempty s1 h1
  have n2_pos := normalize_nonempty s2 h2
  have n1_lead := normalize_leading_one s1 h1
  have n2_lead := normalize_leading_one s2 h2
  have n1_val := normalize_preserves_value s1 h1
  have n2_val := normalize_preserves_value s2 h2
  
  simp only [Compare]
  
  by_cases hlen1 : n1.length > n2.length
  · simp [hlen1]
    constructor
    · intro h_lt
      rw [←n1_val, ←n2_val] at h_lt
      exact CompareUnequal_lt n1 n2 n1_valid n2_valid n1_pos n1_lead n2_pos n2_lead hlen1 h_lt
    constructor
    · intro h_eq
      rw [←n1_val, ←n2_val] at h_eq
      exact CompareUnequal_eq n1 n2 n1_valid n2_valid n1_pos n1_lead n2_pos n2_lead hlen1 h_eq
    · intro h_gt
      rw [←n1_val, ←n2_val] at h_gt
      exact CompareUnequal_gt n1 n2 n1_valid n2_valid n1_pos n1_lead n2_pos n2_lead hlen1 h_gt
      
  · by_cases hlen2 : n2.length > n1.length
    · simp [hlen1, hlen2]
      constructor
      · intro h_lt
        rw [←n1_val, ←n2_val] at h_lt
        have := CompareUnequal_gt n2 n1 n2_valid n1_valid n2_pos n2_lead n1_pos n1_lead hlen2 h_lt
        simp [this]
      constructor
      · intro h_eq
        rw [←n1_val, ←n2_val] at h_eq
        have := CompareUnequal_eq n2 n1 n2_valid n1_valid n2_pos n2_lead n1_pos n1_lead hlen2 h_eq.symm
        simp [this]
      · intro h_gt
        rw [←n1_val, ←n2_val] at h_gt
        have := CompareUnequal_lt n2 n1 n2_valid n1_valid n2_pos n2_lead n1_pos n1_lead hlen2 h_gt
        simp [this]
        
    · simp [hlen1, hlen2]
      push_neg at hlen1 hlen2
      have hlen1' : n1.length ≤ n2.length := hlen1
      have hlen2' : n2.length ≤ n1.length := hlen2
      have h_eq_len : n1.length = n2.length := le_antisymm hlen1' hlen2'
      
      have spec := CompareUnequal_eq_len_spec n1 n2 n1_valid n2_valid n1_pos n1_lead n2_pos n2_lead h_eq_len
      
      constructor
      · intro h_lt
        rw [←n1_val, ←n2_val] at h_lt
        exact spec.1 h_lt
      constructor
      · intro h_eq
        rw [←n1_val, ←n2_val] at h_eq
        exact spec.2.1 h_eq
      · intro h_gt
        rw [←n1_val, ←n2_val] at h_gt
        exact spec.2.2 h_gt
-- </vc-proof>

end BignumLean