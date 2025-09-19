-- <vc-preamble>
def isSorted (as : List Nat) : Prop :=
  ∀ i j, i < j → j < as.length → as[i]! ≤ as[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_patches (nums : List Nat) (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_patches_basic_properties {nums : List Nat} {n : Nat}
  (h : isSorted nums) :
  let result := min_patches nums n
  Nat.zero ≤ result ∧ isSorted nums := by
  sorry

theorem min_patches_empty_list {n : Nat} :
  let result := min_patches [] n
  0 < result := by
  sorry

theorem min_patches_small_n {nums : List Nat} (n : Nat)
  (h₁ : isSorted nums)
  (h₂ : nums ≠ [])
  (h₃ : ∀ x ∈ nums, n < x) :
  0 ≤ min_patches nums n := by
  sorry

theorem min_patches_minimal_cases_1 :
  min_patches [1] 1 = 0 := by
  sorry

theorem min_patches_minimal_cases_2 :
  min_patches [2] 1 = 1 := by
  sorry

theorem min_patches_minimal_cases_3 :
  min_patches [1,2] 2 = 0 := by
  sorry
-- </vc-theorems>