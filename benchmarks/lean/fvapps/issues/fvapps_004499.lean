-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def groupInts (lst : List Int) (key : Int) : List (List Int) := sorry

theorem empty_list_any_key (k : Int) : 
  groupInts [] k = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem group_ints_result_structure {lst : List Int} {k : Int} :
  let result := groupInts lst k
  -- Result is a list of non-empty lists
  ∀ sublist ∈ result, sublist ≠ [] := sorry

theorem group_ints_preserves_elements {lst : List Int} {k : Int} :
  let result := groupInts lst k
  List.join result = lst := sorry

theorem group_ints_homogeneous_groups {lst : List Int} {k : Int} :
  let result := groupInts lst k
  ∀ group ∈ result, 
    let first_less := group.head! < k
    ∀ x ∈ group, (x < k) = first_less := sorry

theorem group_ints_adjacent_groups_differ {lst : List Int} {k : Int} :
  let result := groupInts lst k
  ∀ i < result.length - 1,
    let group1_head := (result.get! i).head!
    let group2_head := (result.get! (i+1)).head!
    (group1_head < k) ≠ (group2_head < k) := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval group_ints [] 0

/-
info: [[1]]
-/
-- #guard_msgs in
-- #eval group_ints [1] 1
-- </vc-theorems>