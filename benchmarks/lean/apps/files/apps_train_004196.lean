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

/-
info: 6
-/
-- #guard_msgs in
-- #eval sum_groups [2, 1, 2, 2, 6, 5, 0, 2, 0, 5, 5, 7, 7, 4, 3, 3, 9]

/-
info: 5
-/
-- #guard_msgs in
-- #eval sum_groups [2, 1, 2, 2, 6, 5, 0, 2, 0, 3, 3, 3, 9, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval sum_groups [1, 1, 2, 2]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded