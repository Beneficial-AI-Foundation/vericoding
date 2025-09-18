-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def threeAmigos (nums : List Int) : List Int :=
sorry

def list_max (l : List Int) : Int :=
sorry

def list_min (l : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem threeAmigos_valid_size {nums : List Int} :
  let result := threeAmigos nums
  List.length result = 0 ∨ List.length result = 3 :=
sorry

theorem threeAmigos_consecutive {nums : List Int} (h : 3 ≤ List.length nums) :
  let result := threeAmigos nums
  result = [] ∨ ∃ i, i + 2 < List.length nums ∧
    result = [nums[i]!, nums[i+1]!, nums[i+2]!] :=
sorry

theorem threeAmigos_same_parity {nums : List Int} (h : 3 ≤ List.length nums) :
  let result := threeAmigos nums
  result = [] ∨ (∀ x ∈ result, x % 2 = result[0]! % 2) :=
sorry

theorem threeAmigos_minimal_range {nums : List Int} (h : 3 ≤ List.length nums) :
  let result := threeAmigos nums
  result = [] ∨
  (∀ i, i + 2 < List.length nums →
    (∀ j, j ∈ [nums[i]!, nums[i+1]!, nums[i+2]!] → j % 2 = nums[i]! % 2) →
    (list_max result - list_min result) ≤ (nums[i+2]! - nums[i]!)) :=
sorry
-- </vc-theorems>