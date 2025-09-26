-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | x :: xs => x + xs.sum

def gcd_multiple (nums : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_gcd_partition_sum (n k : Nat) (arr : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gcd_multiple_divides (nums : List Nat) (h : nums ≠ []) :
  let result := gcd_multiple nums
  (∀ n ∈ nums, n % result = 0) ∧ result > 0 := by
  sorry

theorem max_gcd_sum_basic_properties 
  (n k : Nat) (arr : List Nat)
  (h1 : arr.length ≥ n)
  (h2 : k ≤ n) :
  let result := max_gcd_partition_sum n k arr 
  result ≥ 0 ∧ 
  result ≤ (arr.take n).sum := by
  sorry

theorem max_gcd_sum_k_one
  (n : Nat) (arr : List Nat)
  (h : arr.length ≥ n) :
  max_gcd_partition_sum n 1 arr = gcd_multiple (arr.take n) := by
  sorry

theorem max_gcd_sum_k_eq_n
  (n : Nat) (arr : List Nat)
  (h : arr.length ≥ n) :
  max_gcd_partition_sum n n arr = (arr.take n).sum := by
  sorry

theorem max_gcd_sum_identical_elements
  (n k : Nat) 
  (h1 : n ≥ 2)
  (h2 : k = n/2) :
  let arr := List.replicate n 10
  max_gcd_partition_sum n k arr = 10 * k := by
  sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval max_gcd_partition_sum 4 2 [5, 6, 3, 2]
-- </vc-theorems>