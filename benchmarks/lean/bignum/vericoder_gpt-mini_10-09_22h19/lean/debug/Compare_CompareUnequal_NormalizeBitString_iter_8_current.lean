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
-- helper to expose the definitional symmetry between `<` and `>`
theorem lt_iff_gt {a b : Nat} : (a < b) ↔ (b > a) := Iff.rfl
-- </vc-helpers>

-- <vc-spec>
def Compare (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
let n1 := NormalizeBitString s1
  let n2 := NormalizeBitString s2
  if n1.length > n2.length then
    CompareUnequal n1 n2
  else if n2.length > n1.length then
    - (CompareUnequal n2 n1)
  else
    if Str2Int n1 < Str2Int n2 then (-1 : Int)
    else if Str2Int n1 = Str2Int n2 then 0
    else 1
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

  rcases NormalizeBitString_spec s1 h1 with ⟨hn1_valid, hn1_lenpos, hn1_msb, eq1⟩
  rcases NormalizeBitString_spec s2 h2 with ⟨hn2_valid, hn2_lenpos, hn2_msb, eq2⟩

  by_cases hlen : n1.length > n2.length
  · -- n1 longer
    have : Compare s1 s2 = CompareUnequal n1 n2 := by
      simp [Compare, hlen]
    have spec := CompareUnequal_spec n1 n2 hn1_valid hn2_valid hn1_lenpos hn1_msb hn2_lenpos hn2_msb hlen
    rcases spec with ⟨spec_lt, spec_eq, spec_gt⟩
    constructor
    · intro H
      have Hn : Str2Int n1 < Str2Int n2 := by rwa [eq1, eq2] at H
      calc
        Compare s1 s2 = CompareUnequal n1 n2 := this
        _ = (-1 : Int) := spec_lt Hn
    · constructor
      · intro H
        have Hn : Str2Int n1 = Str2Int n2 := by rwa [eq1, eq2] at H
        calc
          Compare s1 s2 = CompareUnequal n1 n2 := this
          _ = 0 := spec_eq Hn
      · intro H
        have Hn : Str2Int n1 > Str2Int n2 := by rwa [eq1, eq2] at H
        calc
          Compare s1 s2 = CompareUnequal n1 n2 := this
          _ = 1 := spec_gt Hn

  · -- not (n1.length > n2.length)
    have hlen_neg : ¬ n1.length > n2.length := hlen
    by_cases hlen2 : n2.length > n1.length
    · -- n2 longer
      have : Compare s1 s2 = - (CompareUnequal n2 n1) := by
        simp [Compare, hlen_neg, hlen2]
      have spec := CompareUnequal_spec n2 n1 hn2_valid hn1_valid hn2_lenpos hn2_msb hn1_lenpos hn1_msb hlen2
      rcases spec with ⟨spec_lt, spec_eq, spec_gt⟩
      constructor
      · intro H
        have Hn : Str2Int n1 < Str2Int n2 := by rwa [eq1, eq2] at H
        -- Str2Int n2 > Str2Int n1 is definitionally the same as Str2Int n1 < Str2Int n2
        calc
          Compare s1 s2 = - (CompareUnequal n2 n1) := this
          _ = -1 := by rw [spec_gt Hn]
      · constructor
        · intro H
          have Hn : Str2Int n1 = Str2Int n2 := by rwa [eq1, eq2] at H
          calc
            Compare s1 s2 = - (CompareUnequal n2 n1) := this
            _ = 0 := by rw [spec_eq Hn]
        · intro H
          have Hn : Str2Int n1 > Str2Int n2 := by rwa [eq1, eq2] at H
          -- Str2Int n2 < Str2Int n1 is definitionally the same as Str2Int n1 > Str2Int n2
          calc
            Compare s1 s2 = - (CompareUnequal n2 n1) := this
            _ = 1 := by rw [spec_lt Hn]

    · -- lengths equal
      have hlen_eq : n1.length = n2.length := Nat.le_antisymm (Nat.le_of_not_gt hlen_neg) (Nat.le_of_not_gt hlen2)
      constructor
      · intro H
        have Hn : Str2Int n1 < Str2Int n2 := by rwa [eq1, eq2] at H
        have comp_eq : Compare s1 s2 = (if Str2Int n1 < Str2Int n2 then (-1 : Int) else if Str2Int n1 = Str2Int n2 then 0 else 1) := by
          simp [Compare, hlen_neg, hlen2]
        simp [comp_eq, Hn]
      · constructor
        · intro H
          have Hn : Str2Int n1 = Str2Int n2 := by rwa [eq1, eq2] at H
          have comp_eq : Compare s1 s2 = (if Str2Int n1 < Str2Int n2 then (-1 : Int) else if Str2Int n1 = Str2Int n2 then 0 else 1) := by
            simp [Compare, hlen_neg, hlen2]
          simp [comp_eq, Hn]
        · intro H
          have Hn : Str2Int n1 > Str2Int n2 := by rwa [eq1, eq2] at H
          have comp_eq : Compare s1 s2 = (if Str2Int n1 < Str2Int n2 then (-1 : Int) else if Str2Int n1 = Str2Int n2 then 0 else 1) := by
            simp [Compare, hlen_neg, hlen2]
          -- the first two conditions are false, so the else branch yields 1
          have nlt : ¬ (Str2Int n1 < Str2Int n2) := by
            intro C; exact Nat.lt_asymm C Hn
          have neq : ¬ (Str2Int n1 = Str2Int n2) := by
            intro C; exact (Nat.ne_of_gt Hn) C
          simp [comp_eq, nlt, neq]
-- </vc-proof>

end BignumLean