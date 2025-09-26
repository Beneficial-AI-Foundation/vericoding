-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortestAlternatingPaths (n : Nat) (redEdges blueEdges : List Edge) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_path_valid (n : Nat) (edges : List Edge) 
  (h1 : n > 0) (h2 : ∀ e ∈ edges, e.from_ < n ∧ e.to_ < n) :
  let result := shortestAlternatingPaths n edges []
  -- Result length matches n
  List.length result = n
  -- First element is 0
  ∧ List.get! result 0 = 0 
  -- All elements are -1 or valid length < 2n
  ∧ ∀ x ∈ result, x ≥ -1 ∧ (x = -1 ∨ x < 2 * n) :=
sorry

theorem alternating_path_valid (n : Nat) (redEdges blueEdges : List Edge)
  (h1 : n > 0)
  (h2 : ∀ e ∈ redEdges, e.from_ < n ∧ e.to_ < n)
  (h3 : ∀ e ∈ blueEdges, e.from_ < n ∧ e.to_ < n) :
  let result := shortestAlternatingPaths n redEdges blueEdges
  -- Result length matches n
  List.length result = n
  -- First element is 0
  ∧ List.get! result 0 = 0
  -- All elements are -1 or valid length < 2n 
  ∧ ∀ x ∈ result, x ≥ -1 ∧ (x = -1 ∨ x < 2 * n) :=
sorry

theorem no_edges (n : Nat) (h : n > 0) :
  let result := shortestAlternatingPaths n ([] : List Edge) ([] : List Edge)
  List.get! result 0 = 0
  ∧ ∀ i, i > 0 → i < n → List.get! result i = -1 := 
sorry

theorem self_loops :
  let n := 3
  let result := shortestAlternatingPaths n 
    [⟨0, 0⟩] [⟨0, 0⟩]
  List.get! result 0 = 0 :=
sorry

/-
info: [0, 1, -1]
-/
-- #guard_msgs in
-- #eval shortest_alternating_paths 3 [[0, 1], [1, 2]] []

/-
info: [0, 1, 2]
-/
-- #guard_msgs in
-- #eval shortest_alternating_paths 3 [[0, 1]] [[1, 2]]

/-
info: [0, 1, 1]
-/
-- #guard_msgs in
-- #eval shortest_alternating_paths 3 [[0, 1], [0, 2]] [[1, 0]]
-- </vc-theorems>