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
-- No additional helpers required for this proof.
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
rcases NormalizeBitString_spec s1 h1 with ⟨hn1_valid, hn1_lenpos, hn1_msb, eq1⟩
  rcases NormalizeBitString_spec s2 h2 with ⟨hn2_valid, hn2_lenpos, hn2_msb, eq2⟩

  -- We'll reason by cases on the lengths of the normalized strings.
  by_cases hlen : (NormalizeBitString s1).length > (NormalizeBitString s2).length
  · -- n1 longer: Compare s1 s2 = CompareUnequal n1 n2
    have : Compare s1 s2 = CompareUnequal (NormalizeBitString s1) (NormalizeBitString s2) := by
      simp [Compare, hlen]
    have spec := CompareUnequal_spec (NormalizeBitString s1) (NormalizeBitString s2)
      hn1_valid hn2_valid hn1_lenpos hn1_msb hn2_lenpos hn2_msb hlen
    rcases spec with ⟨spec_lt, spec_eq, spec_gt⟩
    constructor
    · intro H
      have Hn : Str2Int (NormalizeBitString s1) < Str2Int (NormalizeBitString s2) := by
        simpa [eq1, eq2] using H
      calc
        Compare s1 s2 = CompareUnequal (NormalizeBitString s1) (NormalizeBitString s2) := this
        _ = (-1 : Int) := spec_lt Hn
    · constructor
      · intro H
        have Hn : Str2Int (NormalizeBitString s1) = Str2Int (NormalizeBitString s2) := by
          simpa [eq1, eq2] using H
        calc
          Compare s1 s2 = CompareUnequal (NormalizeBitString s1) (NormalizeBitString s2) := this
          _ = 0 := spec_eq Hn
      · intro H
        have Hn : Str2Int (NormalizeBitString s1) > Str2Int (NormalizeBitString s2) := by
          simpa [eq1, eq2] using H
        calc
          Compare s1 s2 = CompareUnequal (NormalizeBitString s1) (NormalizeBitString s2) := this
          _ = 1 := spec_gt Hn

  · -- not (n1.length > n2.length)
    have hlen_neg : ¬ (NormalizeBitString s1).length > (NormalizeBitString s2).length := hlen
    by_cases hlen2 : (NormalizeBitString s2).length > (NormalizeBitString s1).length
    · -- n2 longer: Compare s1 s2 = - (CompareUnequal n2 n1)
      have : Compare s1 s2 = - CompareUnequal (NormalizeBitString s2) (NormalizeBitString s1) := by
        simp [Compare, hlen_neg, hlen2]
      have spec := CompareUnequal_spec (NormalizeBitString s2) (NormalizeBitString s1)
        hn2_valid hn1_valid hn2_lenpos hn2_msb hn1_lenpos hn1_msb hlen2
      rcases spec with ⟨spec_lt, spec_eq, spec_gt⟩
      constructor
      · intro H
        have Hn : Str2Int (NormalizeBitString s1) < Str2Int (NormalizeBitString s2) := by
          simpa [eq1, eq2] using H
        -- From Hn derive Str2Int n2 > Str2Int n1 and use spec_gt
        have Hgt : Str2Int (NormalizeBitString s2) > Str2Int (NormalizeBitString s1) := by
          exact Nat.lt_iff_gt.2 Hn
        calc
          Compare s1 s2 = - CompareUnequal (NormalizeBitString s2) (NormalizeBitString s1) := this
          _ = -1 := by rw [spec_gt Hgt]
      · constructor
        · intro H
          have Hn : Str2Int (NormalizeBitString s1) = Str2Int (NormalizeBitString s2) := by
            simpa [eq1, eq2] using H
          calc
            Compare s1 s2 = - CompareUnequal (NormalizeBitString s2) (NormalizeBitString s1) := this
            _ = 0 := by rw [spec_eq Hn]
        · intro H
          have Hn : Str2Int (NormalizeBitString s1) > Str2Int (NormalizeBitString s2) := by
            simpa [eq1, eq2] using H
          have Hlt : Str2Int (NormalizeBitString s2) < Str2Int (NormalizeBitString s1) := by
            exact Nat.gt_iff_lt.2 Hn
          calc
            Compare s1 s2 = - CompareUnequal (NormalizeBitString s2) (NormalizeBitString s1) := this
            _ = 1 := by rw [spec_lt Hlt]

    · -- lengths equal
      have hlen_eq : (NormalizeBitString s1).length = (NormalizeBitString s2).length := by
        apply Nat.le_antisymm
        · by_contra H; have : (NormalizeBitString s2).length > (NormalizeBitString s1).length := by
            apply Nat.lt_of_not_ge (by simpa using H); contradiction
          exact Nat.le_of_not_gt hlen_neg
        · exact Nat.le_of_not_gt hlen2
      -- With equal lengths Compare reduces to direct integer comparison of n1 and n2.
      constructor
      · intro H
        have Hn : Str2Int (NormalizeBitString s1) < Str2Int (NormalizeBitString s2) := by
          simpa [eq1, eq2] using H
        have : Compare s1 s2 = (if Str2Int (NormalizeBitString s1) < Str2Int (NormalizeBitString s2) then (-1 : Int) else
          if Str2Int (NormalizeBitString s1) = Str2Int (NormalizeBitString s2) then 0 else 1) := by
          simp [Compare, hlen_neg, hlen2]
        simp [this, Hn]
      · constructor
        · intro H
          have Hn : Str2Int (NormalizeBitString s1) = Str2Int (NormalizeBitString s2) := by
            simpa [eq1, eq2] using H
          have : Compare s1 s2 = (if Str2Int (NormalizeBitString s1) < Str2Int (NormalizeBitString s2) then (-1 : Int) else
            if Str2Int (NormalizeBitString s1) = Str2Int (NormalizeBitString s2) then 0 else 1) := by
            simp [Compare, hlen_neg, hlen2]
          simp [this, Hn]
        · intro H
          have Hn : Str2Int (NormalizeBitString s1) > Str2Int (NormalizeBitString s2) := by
            simpa [eq1, eq2] using H
          have : Compare s1 s2 = (if Str2Int (NormalizeBitString s1) < Str2Int (NormalizeBitString s2) then (-1 : Int) else
            if Str2Int (NormalizeBitString s1) = Str2Int (NormalizeBitString s2) then 0 else 1) := by
            simp [Compare, hlen_neg, hlen2]
          -- first two conditions are false, so result is 1
          have nlt : ¬ (Str2Int (NormalizeBitString s1) < Str2Int (NormalizeBitString s2)) := by
            intro C; exact (Nat.lt_asymm (Str2Int (NormalizeBitString s1)) (Str2Int (NormalizeBitString s1)) (Nat.lt_trans C Hn))
          have neq : ¬ (Str2Int (NormalizeBitString s1) = Str2Int (NormalizeBitString s2)) := by
            intro C; have := Nat.ne_of_gt Hn; apply this; exact C
          simp [this, nlt, neq]
-- </vc-proof>

end BignumLean