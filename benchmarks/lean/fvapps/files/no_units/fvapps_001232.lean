-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_soldier_memory (n : Nat) (m : Nat) (positions : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_length {n m : Nat} {positions : List Nat} 
  (h1 : n ≥ 2) (h2 : positions.length = m) (h3 : ∀ p ∈ positions, p < n) :
  (solve_soldier_memory n m positions).length = n :=
  sorry

theorem solution_non_negative {n m : Nat} {positions : List Nat}
  (h1 : n ≥ 2) (h2 : positions.length = m) (h3 : ∀ p ∈ positions, p < n) :
  ∀ x ∈ solve_soldier_memory n m positions, x ≥ 0 :=
  sorry

theorem solution_monotonic {n m : Nat} {positions : List Nat}
  (h1 : n ≥ 2) (h2 : positions.length = m) (h3 : ∀ p ∈ positions, p < n) :
  ∀ i : Nat, i < n → i ∉ positions → i > 0 →
    let result := solve_soldier_memory n m positions
    ∀ v1 v2, result[i]? = some v1 → result[i-1]? = some v2 →
    v1 ≤ v2 + 1 ∧ v2 ≤ v1 + 1 :=
  sorry

theorem single_soldier_linear {n pos : Nat}
  (h1 : n ≥ 2) (h2 : pos < n) :
  ∀ i : Nat, i < n →
    let result := solve_soldier_memory n 1 [pos]
    ∀ v, result[i]? = some v →
    v = if i ≥ pos then i - pos else pos - i :=
  sorry
-- </vc-theorems>