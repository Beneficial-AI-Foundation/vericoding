-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fenwick_operations (n : Nat) (m : Nat) (c : Int) (ops : List String) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fenwick_results_length (n : Nat) (m : Nat) (c : Int) (ops : List String) :
  let results := fenwick_operations n m c ops
  let num_queries := (ops.filter (fun op => op.startsWith "Q")).length
  results.length = num_queries := sorry

theorem fenwick_results_are_ints (n : Nat) (m : Nat) (c : Int) (ops : List String) :
  let results := fenwick_operations n m c ops
  ∀ x ∈ results, x = x := sorry

theorem fenwick_empty_ops (n : Nat) :
  fenwick_operations n 0 0 [] = [] := sorry

theorem fenwick_input_bounds (n m : Nat) (c : Int) (ops : List String) : 
  (2 ≤ n ∧ n ≤ 100) →
  (1 ≤ m ∧ m ≤ 20) →
  (-1000 ≤ c ∧ c ≤ 1000) →
  fenwick_operations n m c ops ≠ [] := sorry

theorem fenwick_valid_query_bounds (pos : Nat) (n : Nat) :
  1 ≤ pos → pos ≤ n → 
  ∀ (m : Nat) (c : Int) (ops : List String),
  let results := fenwick_operations n m c ops
  results ≠ [] := sorry

theorem fenwick_valid_update_bounds (u v : Nat) (k : Int) (n : Nat) :
  1 ≤ u → u ≤ v → v ≤ n →
  -100 ≤ k → k ≤ 100 →
  ∀ (m : Nat) (c : Int) (ops : List String),
  let results := fenwick_operations n m c ops
  results ≠ [] := sorry

/-
info: [0, 1, 2]
-/
-- #guard_msgs in
-- #eval fenwick_operations 7 5 0 ["Q 7", "S 1 7 1", "Q 3", "S 1 3 1", "Q 3"]

/-
info: [1, 3]
-/
-- #guard_msgs in
-- #eval fenwick_operations 3 3 1 ["Q 1", "S 1 2 2", "Q 2"]

/-
info: [2, 3]
-/
-- #guard_msgs in
-- #eval fenwick_operations 5 4 0 ["S 1 3 2", "Q 2", "S 2 4 1", "Q 3"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded