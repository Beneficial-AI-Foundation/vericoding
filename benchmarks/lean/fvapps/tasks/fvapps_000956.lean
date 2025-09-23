-- <vc-preamble>
def powers_of_two : List Nat :=
  let rec mk_powers : Nat → List Nat
    | 0 => []
    | n+1 => if (2^n ≤ 1000) then (2^n)::(mk_powers n) else mk_powers n
  mk_powers 10
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_longest_dividing_subsequence (nums: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_bounds {nums: List Nat}
  (h1: ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 1000)
  (h2: nums.length > 0) :
  1 ≤ find_longest_dividing_subsequence nums ∧
  find_longest_dividing_subsequence nums ≤ nums.length :=
sorry

theorem powers_of_two_sequence :
  find_longest_dividing_subsequence powers_of_two = powers_of_two.length :=
sorry

theorem sorted_divisible_sequence {nums: List Nat}
  (h1: ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 1000)
  (h2: nums.length ≥ 2)
  (h3: ∀ (i: Fin nums.length) (j: Fin nums.length),
    i.val < j.val → (nums.get j) % (nums.get i) = 0)
  (h4: ∀ (i: Fin nums.length) (j: Fin nums.length),
    i.val < j.val → nums.get i ≤ nums.get j) :
  find_longest_dividing_subsequence nums = nums.length :=
sorry

theorem edge_case_singleton :
  find_longest_dividing_subsequence [1] = 1 :=
sorry
-- </vc-theorems>