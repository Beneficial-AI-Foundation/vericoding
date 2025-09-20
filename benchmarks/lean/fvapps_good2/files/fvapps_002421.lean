-- <vc-preamble>
def list_sum : List Nat → Nat
| [] => 0
| x::xs => x + list_sum xs

def list_get (l: List Nat) (i: Nat) : Nat :=
match l with
| [] => 0
| x::xs => if i = 0 then x else list_get xs (i-1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest_triangle_perimeter (xs: List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem perimeter_bounds {nums : List Nat} (h : nums.length ≥ 3) :
  let result := largest_triangle_perimeter nums
  (result = 0 ∨ (result > 0 ∧ result ≤ list_sum nums)) :=
sorry

theorem triangle_inequality {nums : List Nat} (h : nums.length ≥ 3) :
  let result := largest_triangle_perimeter nums
  result > 0 →
  ∃ i j k, i < nums.length ∧ j < nums.length ∧ k < nums.length ∧
          i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
          list_get nums i < list_get nums j + list_get nums k ∧
          result ≥ list_get nums i + list_get nums j + list_get nums k :=
sorry

theorem order_independent {nums nums' : List Nat} (h : nums.length ≥ 3)
  (h2 : nums.length = nums'.length)
  (h3 : ∀ x, x ∈ nums ↔ x ∈ nums') :
  largest_triangle_perimeter nums = largest_triangle_perimeter nums' :=
sorry

theorem non_positive_result {nums : List Nat} (h : nums.length ≥ 3)
  (h₂ : ∀ x ∈ nums, x = 0) :
  largest_triangle_perimeter nums = 0 :=
sorry

theorem minimal_cases_unit :
  largest_triangle_perimeter [1,1,1] = 3 :=
sorry

theorem minimal_cases_invalid :
  largest_triangle_perimeter [1,1,2] = 0 :=
sorry
-- </vc-theorems>