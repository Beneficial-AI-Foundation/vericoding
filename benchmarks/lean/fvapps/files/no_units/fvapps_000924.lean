-- <vc-preamble>
def isVowel (c : Char) : Bool := 
  c = 'a' ∨ c = 'e' ∨ c = 'i' ∨ c = 'o' ∨ c = 'u'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minCostVowelTransform (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cost_non_negative (s : String) :
  minCostVowelTransform s ≥ 0 :=
sorry

theorem vowels_zero_cost (s : String) :
  (∀ c ∈ s.data, isVowel c) → minCostVowelTransform s = 0 :=
sorry

theorem cost_is_sum_of_min_distances (s : String) :
  minCostVowelTransform s = 
    s.data.foldl (fun acc c =>
      if isVowel c then 
        acc
      else
        acc + ['a', 'e', 'i', 'o', 'u'].foldl (fun min_dist v =>
          min min_dist (if c.toNat ≥ v.toNat then c.toNat - v.toNat else v.toNat - c.toNat)
        ) 1000000
    ) 0 :=
sorry

theorem non_vowels_positive_cost (s : String) :
  s ≠ "" →
  (∀ c ∈ s.data, ¬isVowel c) →
  minCostVowelTransform s > 0 :=
sorry
-- </vc-theorems>