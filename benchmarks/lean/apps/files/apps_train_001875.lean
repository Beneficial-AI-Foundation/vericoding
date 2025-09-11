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

/-
info: sorted([sorted(g) for g in expected1])
-/
-- #guard_msgs in
-- #eval sorted [sorted(g) for g in result1]

/-
info: sorted([sorted(g) for g in expected2])
-/
-- #guard_msgs in
-- #eval sorted [sorted(g) for g in result2]

/-
info: sorted([sorted(g) for g in expected3])
-/
-- #guard_msgs in
-- #eval sorted [sorted(g) for g in result3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded