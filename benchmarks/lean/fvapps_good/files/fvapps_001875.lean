-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def groupThePeople (groupSizes : List Nat) : List (List Nat) := sorry

theorem group_sizes_match_values (groupSizes : List Nat) 
  (h : ∀ x ∈ groupSizes, 1 ≤ x ∧ x ≤ 10) :
  let result := groupThePeople groupSizes
  ∀ group ∈ result,
    let size := group.length 
    ∀ i ∈ group, groupSizes.get! i = size := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_overlapping_groups (groupSizes : List Nat)
  (h : ∀ x ∈ groupSizes, 1 ≤ x ∧ x ≤ 10) :
  let result := groupThePeople groupSizes
  ∀ g1 ∈ result,
    ∀ g2 ∈ result,
      g1 ≠ g2 →
      ∀ i ∈ g1, i ∉ g2 := sorry
-- </vc-theorems>