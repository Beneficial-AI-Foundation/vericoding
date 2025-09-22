-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def twos_difference (lst : List Int) : List (Int × Int) := sorry

theorem twos_difference_ordered (lst : List Int) :
  let result := twos_difference lst
  ∀ i j, i < j → i < (result.length) → j < (result.length) → 
    (result[i]!.1 < result[j]!.1 ∨ (result[i]!.1 = result[j]!.1 ∧ result[i]!.2 ≤ result[j]!.2)) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem twos_difference_pairs (lst : List Int) :
  let result := twos_difference lst
  ∀ p ∈ result, p.2 - p.1 = 2 := sorry

theorem twos_difference_valid_elements (lst : List Int) :
  let result := twos_difference lst
  ∀ p ∈ result, p.1 ∈ lst ∧ p.2 ∈ lst := sorry

theorem twos_difference_complete (lst : List Int) :
  let result := twos_difference lst
  ∀ x y, x ∈ lst → y ∈ lst → y - x = 2 →
  ∃ p ∈ result, p.1 = x ∧ p.2 = y := sorry

theorem twos_difference_empty (lst : List Int) :
  lst = [] → twos_difference lst = [] := sorry
-- </vc-theorems>