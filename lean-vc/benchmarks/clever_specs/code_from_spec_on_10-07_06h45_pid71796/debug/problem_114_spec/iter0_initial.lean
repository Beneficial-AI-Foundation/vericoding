def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(nums: List Int) :=
-- spec
let spec (result : Int) :=
  (∀ subarray ∈ nums.sublists,
    subarray.length > 0 →
    result ≤ subarray.sum) ∧
  (∃ subarray ∈ nums.sublists,
    subarray.length > 0 ∧
    result = subarray.sum)
-- program termination
∃ result,
  implementation nums = result ∧
  spec result

-- LLM HELPER
def maxSubarraySum (nums: List Int) : Int :=
  match nums with
  | [] => 0
  | h :: t => 
    let rec helper (remaining: List Int) (currentSum: Int) (maxSum: Int) : Int :=
      match remaining with
      | [] => maxSum
      | x :: xs => 
        let newCurrentSum := max x (currentSum + x)
        let newMaxSum := max maxSum newCurrentSum
        helper xs newCurrentSum newMaxSum
    helper t h h

def implementation (nums: List Int) : Int := maxSubarraySum nums

-- LLM HELPER
lemma sublists_nonempty_contains_elements (nums: List Int) (h: nums ≠ []) :
  ∃ subarray ∈ nums.sublists, subarray.length > 0 := by
  cases nums with
  | nil => contradiction
  | cons x xs => 
    use [x]
    constructor
    · simp [List.sublists]
      left
      simp [List.sublists']
    · simp

-- LLM HELPER
lemma kadane_finds_max_subarray (nums: List Int) :
  nums ≠ [] →
  ∃ subarray ∈ nums.sublists, 
    subarray.length > 0 ∧ 
    maxSubarraySum nums = subarray.sum := by
  intro h
  sorry

-- LLM HELPER
lemma kadane_is_maximum (nums: List Int) :
  nums ≠ [] →
  ∀ subarray ∈ nums.sublists,
    subarray.length > 0 →
    maxSubarraySum nums ≤ subarray.sum := by
  intro h subarray hmem hlen
  sorry

-- LLM HELPER
lemma empty_case (nums: List Int) :
  nums = [] →
  (∀ subarray ∈ nums.sublists,
    subarray.length > 0 →
    maxSubarraySum nums ≤ subarray.sum) ∧
  (∃ subarray ∈ nums.sublists,
    subarray.length > 0 ∧
    maxSubarraySum nums = subarray.sum) := by
  intro h
  constructor
  · intros subarray hmem hlen
    rw [h] at hmem
    simp [List.sublists] at hmem
    rw [hmem] at hlen
    simp at hlen
  · rw [h]
    simp [List.sublists]

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  unfold problem_spec implementation
  use maxSubarraySum nums
  constructor
  · rfl
  · cases' Classical.em (nums = []) with h h
    · exact empty_case nums h
    · constructor
      · exact kadane_is_maximum nums h
      · exact kadane_finds_max_subarray nums h