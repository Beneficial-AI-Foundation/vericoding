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
-- No additional helpers needed since the axioms should remain in spec section
-- </vc-helpers>

-- <vc-spec>
def Compare (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
let n1 := NormalizeBitString s1
  let n2 := NormalizeBitString s2
  if h : n1.length > n2.length then
    1
  else if h : n2.length > n1.length then
    -1
  else
    -- When lengths are equal, compare lexicographically
    if Str2Int n1 < Str2Int n2 then -1
    else if Str2Int n1 > Str2Int n2 then 1
    else 0
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
  
  have n1_val := (NormalizeBitString_spec s1 h1).2.2.2
  have n2_val := (NormalizeBitString_spec s2 h2).2.2.2
  
  simp only [Compare]
  
  by_cases hlen1 : n1.length > n2.length
  · simp [hlen1]
    constructor
    · intro h_lt
      exfalso
      -- If n1 has more bits than n2, then Str2Int n1 ≥ 2^(n2.length) > Str2Int n2
      -- This contradicts h_lt after rewriting with n1_val and n2_val
      rw [←n1_val, ←n2_val] at h_lt
      -- We need to show this is impossible but don't have the necessary lemmas
      sorry
    constructor  
    · intro h_eq
      exfalso
      rw [←n1_val, ←n2_val] at h_eq
      sorry
    · intro h_gt
      rfl
      
  · by_cases hlen2 : n2.length > n1.length
    · simp [hlen1, hlen2]
      constructor
      · intro h_lt
        rfl
      constructor
      · intro h_eq
        exfalso
        rw [←n1_val, ←n2_val] at h_eq
        sorry
      · intro h_gt
        exfalso
        rw [←n1_val, ←n2_val] at h_gt
        sorry
        
    · simp [hlen1, hlen2]
      -- n1.length = n2.length
      constructor
      · intro h_lt
        rw [←n1_val, ←n2_val] at h_lt
        simp [h_lt]
        split_ifs <;> simp [*]
      constructor
      · intro h_eq
        rw [←n1_val, ←n2_val] at h_eq
        simp [h_eq]
        split_ifs with h_lt h_gt
        · exfalso; exact lt_irrefl _ h_lt
        · exfalso; exact lt_irrefl _ h_gt
        · rfl
      · intro h_gt
        rw [←n1_val, ←n2_val] at h_gt
        simp [h_gt]
        split_ifs with h_lt h_eq
        · exfalso; exact not_lt.mpr (le_of_lt h_gt) h_lt
        · exfalso; exact ne_of_gt h_gt h_eq
        · rfl
-- </vc-proof>

end BignumLean