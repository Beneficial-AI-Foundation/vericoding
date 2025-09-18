-- <vc-preamble>
def sumGroups (arr : List Int) : Int := sorry

def getNextArr (arr : List Int) : List Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countAlternatingParity (arr : List Int) : Nat := sorry

theorem sum_groups_returns_positive : 
  ∀ (arr : List Int), arr ≠ [] → 0 < sumGroups arr := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_groups_alternating_parity_bound :
  ∀ (arr : List Int), arr ≠ [] → 
  sumGroups arr ≤ countAlternatingParity arr := sorry

theorem sum_groups_monotonic_reduction :
  ∀ (arr : List Int), arr ≠ [] →
  ∀ (next : List Int), next = getNextArr arr →
  next ≠ arr →
  List.length next ≤ List.length arr := sorry
-- </vc-theorems>