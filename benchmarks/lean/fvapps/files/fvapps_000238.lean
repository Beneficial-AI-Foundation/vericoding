-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_equal_freq (nums: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_equal_freq_returns_valid_length (nums: List Nat) : 
  nums ≠ [] → 0 ≤ max_equal_freq nums ∧ max_equal_freq nums ≤ nums.length :=
  sorry

theorem max_equal_freq_handles_unique_values (nums: List Nat) :
  nums ≠ [] → (∀ (i j : Fin nums.length), i ≠ j → nums.get i ≠ nums.get j) →
  max_equal_freq nums = nums.length :=
  sorry

theorem max_equal_freq_handles_two_frequencies (nums: List Nat) (i: Fin nums.length) :
  nums.length ≥ 2 →
  let nums' := nums.eraseDups ++ [nums.get i]
  max_equal_freq nums' = nums'.length :=
  sorry

theorem max_equal_freq_handles_single_value {n: Nat} (k: Nat) :
  k > 0 →
  let nums := List.replicate k n
  max_equal_freq nums = nums.length :=
  sorry
-- </vc-theorems>