def threeAmigos (nums : List Int) : List Int := sorry

theorem threeAmigos_valid_size {nums : List Int} :
  let result := threeAmigos nums
  List.length result = 0 ∨ List.length result = 3 := sorry

-- <vc-helpers>
-- </vc-helpers>

def list_max (l : List Int) : Int := sorry
def list_min (l : List Int) : Int := sorry

theorem threeAmigos_consecutive {nums : List Int} (h : 3 ≤ List.length nums) :
  let result := threeAmigos nums
  result = [] ∨ ∃ i, i + 2 < List.length nums ∧ 
    result = [nums[i]!, nums[i+1]!, nums[i+2]!] := sorry

theorem threeAmigos_same_parity {nums : List Int} (h : 3 ≤ List.length nums) :
  let result := threeAmigos nums
  result = [] ∨ (∀ x ∈ result, x % 2 = result[0]! % 2) := sorry

theorem threeAmigos_minimal_range {nums : List Int} (h : 3 ≤ List.length nums) :
  let result := threeAmigos nums
  result = [] ∨
  (∀ i, i + 2 < List.length nums →
    (∀ j, j ∈ [nums[i]!, nums[i+1]!, nums[i+2]!] → j % 2 = nums[i]! % 2) →
    (list_max result - list_min result) ≤ (nums[i+2]! - nums[i]!)) := sorry

/-
info: [5, 3, 5]
-/
-- #guard_msgs in
-- #eval three_amigos [1, 2, 34, 2, 1, 5, 3, 5, 7, 234, 2, 1]

/-
info: [2, 2, 2]
-/
-- #guard_msgs in
-- #eval three_amigos [2, 4, 6, 8, 10, 2, 2, 2, 1, 1, 1, 5, 3]

/-
info: []
-/
-- #guard_msgs in
-- #eval three_amigos [2, 4, 5, 3, 6, 3, 1, 56, 7, 6, 3, 12]

-- Apps difficulty: introductory
-- Assurance level: guarded