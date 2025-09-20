-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def canDistributePizza (n k : Nat) : String := sorry

theorem can_distribute_basic_props {n k : Nat} (h1 : n > 0) (h2 : k > 0) :
  canDistributePizza n k = "YES" ∨ canDistributePizza n k = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem insufficient_slices {n k : Nat} (h1 : n > 0) (h2 : k > 0) (h3 : k < n) :
  canDistributePizza n k = "NO" := sorry

theorem yes_case_props {n k : Nat} (h1 : n > 0) (h2 : k > 0)
  (h3 : canDistributePizza n k = "YES") :
  k % n = 0 ∧ k ≥ n := sorry

theorem no_case_props {n k : Nat} (h1 : n > 0) (h2 : k > 0)
  (h3 : canDistributePizza n k = "NO") :
  k < n ∨ k % n ≠ 0 := sorry

theorem exact_multiple_works {n m : Nat} (h1 : n > 0) (h2 : m > 1) :
  canDistributePizza n (n * m) = "YES" := sorry

theorem non_divisible_fails {n k offset : Nat} 
  (h1 : n > 1) (h2 : offset > 0) (h3 : offset < n) :
  canDistributePizza n (n * k + offset) = "NO" := sorry
-- </vc-theorems>