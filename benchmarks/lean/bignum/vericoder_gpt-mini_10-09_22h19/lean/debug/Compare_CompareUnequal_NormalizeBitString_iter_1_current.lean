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
-- (no helpers needed)
-- </vc-helpers>

-- <vc-spec>
def Compare (s1 s2 : String) : Int :=
-- </vc-spec>
-- <vc-code>
def Compare (s1 s2 : String) : Int :=
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
  have ⟨hn1_valid, hn1_lenpos, hn1_msb, hn1_eq⟩ := NormalizeBitString_spec s1 h1
  have ⟨hn2_valid, hn2_lenpos, hn2_msb, hn2_eq⟩ := NormalizeBitString_spec s2 h2
  -- rewrite Str2Int s1 and s2 in terms of normalized strings
  have eq1 : Str2Int s1 = Str2Int n1 := hn1_eq
  have eq2 : Str2Int s2 = Str2Int n2 := hn2_eq

  by_cases hlen : n1.length > n2.length
  · -- case: n1 longer
    dsimp [Compare]
    rw if_pos hlen
    have spec := CompareUnequal_spec n1 n2 hn1_valid hn2_valid hn1_lenpos hn1_msb hn2_lenpos hn2_msb hlen
    have ⟨spec_lt, spec_eq, spec_gt⟩ := spec
    constructor
    · intro H
      apply spec_lt
      rwa [eq1, eq2] at H
    · constructor
      · intro H
        apply spec_eq
        rwa [eq1, eq2] at H
      · intro H
        apply spec_gt
        rwa [eq1, eq2] at H

  · -- case: not (n1.length > n2.length)
    dsimp [Compare]
    rw if_neg hlen
    by_cases hlen2 : n2.length > n1.length
    · -- case: n2 longer
      rw if_pos hlen2
      have spec := CompareUnequal_spec n2 n1 hn2_valid hn1_valid hn2_lenpos hn2_msb hn1_lenpos hn1_msb hlen2
      have ⟨spec_lt, spec_eq, spec_gt⟩ := spec
      constructor
      · intro H
        -- Str2Int s1 < Str2Int s2  -> compare = -1
        -- we have Compare = - (CompareUnequal n2 n1)
        -- use spec to determine CompareUnequal n2 n1, then negate
        have H' : Str2Int n1 < Str2Int n2 := by rwa [eq1, eq2] at H
        -- From H' we get CompareUnequal n2 n1 = 1 (because n2 > n1)
        have c := spec_gt H'
        dsimp at c
        change - (CompareUnequal n2 n1) = (-1 : Int)
        rw [c]
        rfl
      · constructor
        · intro H
          have H' : Str2Int n1 = Str2Int n2 := by rwa [eq1, eq2] at H
          -- From equality, spec gives CompareUnequal n2 n1 = 0
          have c := spec_eq H'
          dsimp at c
          change - (CompareUnequal n2 n1) = 0
          rw [c]
          rfl
        · intro H
          have H' : Str2Int n1 > Str2Int n2 := by rwa [eq1, eq2] at H
          -- From H' we get CompareUnequal n2 n1 = -1, so negation gives 1
          have c := spec_lt H'
          dsimp at c
          change - (CompareUnequal n2 n1) = 1
          rw [c]
          rfl
    · -- case: lengths equal
      rw if_neg hlen2
      -- Now Compare reduces to direct Str2Int comparison on normalized strings
      constructor
      · intro H
        dsimp [Compare]
        -- With equal lengths we are in final branch; rewrite Str2Int facts
        have H' : Str2Int n1 < Str2Int n2 := by rwa [eq1, eq2] at H
        rw [if_neg hlen, if_neg hlen2] at *
        -- Evaluate the nested ifs: use the same condition to choose the first branch
        dsimp [Compare]
        -- Directly check the conditional on Str2Int n1 < Str2Int n2
        have : (if Str2Int n1 < Str2Int n2 then (-1 : Int) else if Str2Int n1 = Str2Int n2 then 0 else 1) =
                   (-1 : Int) := by
          by_cases h : Str2Int n1 < Str2Int n2
          · simp [h]
          · have ne := Classical.byContradiction (fun contra => h)
            -- unreachable since we are in branch h; but we already have H'
          terminate_by_reflexivity
        -- The above is cumbersome; instead directly simplify using H'
        simp [H']
        rfl
      · constructor
        · intro H
          dsimp [Compare]
          have H' : Str2Int n1 = Str2Int n2 := by rwa [eq1, eq2] at H
          simp [H']
          rfl
        · intro H
          dsimp [Compare]
          have H' : Str2Int n1 > Str2Int n2 := by rwa [eq1, eq2] at H
          -- show the final else returns 1
          by_cases hlt : Str2Int n1 < Str2Int n2
          · exfalso; apply lt_irrefl _ (lt_trans hlt H')
          · by_cases heq : Str2Int n1 = Str2Int n2
            · exfalso; apply (lt_irrefl _ H')
            · -- neither less nor equal, so the final else branch yields 1
              simp [hlt, heq]
              rfl

-- Note: Some minor uses of classical reasoning are employed to deal with decidable if-branches.
-- </vc-proof>

end BignumLean