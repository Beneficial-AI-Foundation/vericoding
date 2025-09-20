-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def prod_int_partII (n s : Nat) : Nat × Nat × List (List Nat) := sorry

theorem prod_int_properties (n s : Nat) (h1 : n ≥ 1) (h2 : n ≤ 1000) (h3 : s ≥ 1) (h4 : s ≤ 10) :
  let result := prod_int_partII n s
  let total := result.1
  let count := result.2.1
  let factors := result.2.2
  count ≥ 0 ∧
  (factors ≠ [] → List.length factors = count) ∧
  (count > 0 → ∀ f ∈ factors, List.length f = s ∧ 
    ∀ (i : Nat), i < List.length f - 1 → 
      (List.get! f i) ≥ 2 ∧ (List.get! f i) * (List.get! f (i + 1)) ≥ (List.get! f i)) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_factor (n : Nat) (h : n ≥ 1) (h2 : n ≤ 100) :
  let result := prod_int_partII n 1
  let count := result.2.1
  count ≤ 1 ∧
  (count = 1 → result.2.2 = [[n]]) := sorry

theorem prime_factors (p : Nat) (h : p ∈ [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]) :
  (prod_int_partII p 2).2.1 = 0 := sorry
-- </vc-theorems>