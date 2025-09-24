-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_longest_increasing_paths (n : Nat) (values : List Nat) (edges : List (Nat × Nat)) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_correct {n : Nat} {values : List Nat} {edges : List (Nat × Nat)}
  (h1 : values.length = n)
  (h2 : ∀ e ∈ edges, e.1 < n ∧ e.2 ≤ n) :
  (find_longest_increasing_paths n values edges).length = n :=
sorry

theorem all_paths_at_least_one {n : Nat} {values : List Nat} {edges : List (Nat × Nat)}
  (h1 : values.length = n)
  (h2 : ∀ e ∈ edges, e.1 < n ∧ e.2 ≤ n) :
  ∀ x ∈ find_longest_increasing_paths n values edges, x ≥ 1 :=
sorry

theorem single_value_paths {n : Nat} :
  let values := List.replicate n 1
  let edges := List.map (fun i => (1, i+2)) (List.range (n-1))
  ∀ x ∈ find_longest_increasing_paths n values edges, x = 1 :=
sorry
-- </vc-theorems>