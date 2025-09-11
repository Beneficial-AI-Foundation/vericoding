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
set n1 := NormalizeBitString s1
  set n2 := NormalizeBitString s2
  have ⟨hn1_valid, hn1_lenpos, hn1_msb, eq1⟩ := NormalizeBitString_spec s1 h1
  have ⟨hn2_valid, hn2_lenpos, hn2_msb, eq2⟩ := NormalizeBitString_spec s2 h2

  dsimp [Compare]
  by_cases hlen : n1.length > n2.length
  · -- n1 longer: Compare s1 s2 = CompareUnequal n1 n2
    rw [if_pos hlen]
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

  · -- not (n1.length > n2.length)
    rw [if_neg hlen]
    by_cases hlen2 : n2.length > n1.length
    · -- n2 longer: Compare s1 s2 = - (CompareUnequal n2 n1)
      rw [if_pos hlen2]
      have spec := CompareUnequal_spec n2 n1 hn2_valid hn1_valid hn2_lenpos hn2_msb hn1_lenpos hn1_msb hlen2
      have ⟨spec_lt, spec_eq, spec_gt⟩ := spec
      constructor
      · intro H
        -- Str2Int s1 < Str2Int s2 -> Str2Int n1 < Str2Int n2
        have H' : Str2Int n1 < Str2Int n2 := by rwa [eq1, eq2] at H
        -- From H' we get Str2Int n2 > Str2Int n1, so use spec_gt
        have Hgt : Str2Int n2 > Str2Int n1 := (Nat.lt_iff_gt.2 H')
        have c := spec_gt Hgt
        -- hence - (CompareUnequal n2 n1) = -1
        rw [c]
        rfl
      · constructor
        · intro H
          have H' : Str2Int n1 = Str2Int n2 := by rwa [eq1, eq2] at H
          have c := spec_eq H'
          rw [c]
          rfl
        · intro H
          have H' : Str2Int n1 > Str2Int n2 := by rwa [eq1, eq2] at H
          -- From H' we get Str2Int n2 < Str2Int n1, so apply spec_lt to that
          have Hlt : Str2Int n2 < Str2Int n1 := (Nat.gt_iff_lt.2 H')
          have c := spec_lt Hlt
          rw [c]
          rfl

    · -- lengths equal
      rw [if_neg hlen2]
      -- In this case Compare reduces to direct comparison on Str2Int n1 and n2
      constructor
      · intro H
        have H' : Str2Int n1 < Str2Int n2 := by rwa [eq1, eq2] at H
        -- reduce the nested ifs to the first branch
        dsimp
        rw [if_pos H']
        rfl
      · constructor
        · intro H
          have H' : Str2Int n1 = Str2Int n2 := by rwa [eq1, eq2] at H
          dsimp
          rw [if_neg (by
            intro C
            have : Str2Int n1 < Str2Int n2 := by simpa [C] using (Nat.lt_of_lt H')
            contradiction
          )]
          rw [if_pos H']
          rfl
        · intro H
          have H' : Str2Int n1 > Str2Int n2 := by rwa [eq1, eq2] at H
          dsimp
          -- first condition false:
          have nlt : ¬ (Str2Int n1 < Str2Int n2) := by
            intro C
            have Hbn := Nat.lt_of_gt H'
            have := Nat.lt_trans C Hbn
            exact lt_irrefl _ this
          -- second condition false:
          have neq : ¬ (Str2Int n1 = Str2Int n2) := by
            intro C; have := Nat.ne_of_gt H'; dsimp at this; exact (this C)
          rw [if_neg nlt, if_neg neq]
          rfl
-- </vc-proof>

end BignumLean