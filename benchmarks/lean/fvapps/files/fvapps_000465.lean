-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def range_sum (nums : List Nat) (n : Nat) (left right : Nat) : Nat :=
  sorry

def partialSums (nums : List Nat) (n : Nat) : List Nat :=
  sorry

def listMin (l : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem range_sum_output_properties {nums : List Nat} {n left right : Nat}
  (h1 : nums.length = n)
  (h2 : !nums.isEmpty)
  (h3 : ∀ x ∈ nums, x ≥ 1 ∧ x ≤ 1000)
  (h4 : left ≥ 1 ∧ right ≥ 1)
  (h5 : left ≤ 20 ∧ right ≤ 20) :
  let result := range_sum nums n left right
  result ≥ 0 ∧ result < 10^9 + 7 :=
sorry

theorem range_sum_monotonic {nums : List Nat} {n left right : Nat}
  (h1 : nums.length = n)
  (h2 : !nums.isEmpty)
  (h3 : left < right)
  (h4 : right ≤ n) :
  range_sum nums n left (right-1) ≤ range_sum nums n left right :=
sorry

theorem range_sum_single_element {nums : List Nat} {n k : Nat}
  (h1 : nums.length = n)
  (h2 : !nums.isEmpty)
  (h3 : k ≤ n)
  (h4 : k > 0) :
  let pSums := partialSums nums n
  ∀ h : k - 1 < pSums.length,
  range_sum nums n k k = pSums.get ⟨k-1, h⟩ :=
sorry

theorem range_sum_full_range {nums : List Nat} {n : Nat}
  (h1 : nums.length = n)
  (h2 : !nums.isEmpty)
  (h3 : ∀ x ∈ nums, x ≥ 1 ∧ x ≤ 100) :
  range_sum nums n 1 (n * (n+1) / 2) > 0 :=
sorry

theorem range_sum_first_element {nums : List Nat} {n : Nat}
  (h1 : nums.length = n)
  (h2 : !nums.isEmpty) :
  range_sum nums n 1 1 = listMin nums :=
sorry
-- </vc-theorems>