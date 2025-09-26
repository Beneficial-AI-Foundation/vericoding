-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def containsThree (n : Int) : Bool :=
  sorry

def magicSum (nums : List Int) : Int :=
  sorry

def sumList (nums : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem magic_sum_filtering_contributing (nums : List Int) :
  let contributing := nums.filter (fun x => x % 2 = 1 ∧ containsThree x)
  contributing ≠ [] → magicSum nums = magicSum contributing := by
  sorry

theorem magic_sum_filtering_non_contributing (nums : List Int) :
  let non_contributing := nums.filter (fun x => x % 2 = 0 ∨ ¬containsThree x)
  magicSum non_contributing = 0 := by
  sorry

theorem magic_sum_order_invariant (nums : List Int) :
  magicSum nums = magicSum nums.reverse := by
  sorry

theorem magic_sum_duplicates (nums : List Int) :
  magicSum (nums ++ nums) = 2 * magicSum nums := by
  sorry

theorem magic_sum_empty :
  magicSum [] = 0 := by
  sorry

theorem magic_sum_valid_sum (nums : List Int) :
  let valid := nums.filter (fun x => x % 2 = 1 ∧ containsThree x)
  valid ≠ [] → magicSum nums = sumList valid := by
  sorry

theorem magic_sum_all_invalid (nums : List Int) :
  (∀ x ∈ nums, x % 2 = 0 ∨ ¬containsThree x) → magicSum nums = 0 := by
  sorry
-- </vc-theorems>