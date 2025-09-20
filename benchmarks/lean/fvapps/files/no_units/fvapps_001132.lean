-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_crashes (N : Nat) (K : Nat) (directions : List Nat) 
  (positions : List Nat) (queries : List Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiple_queries_result_length {N K : Nat} {directions positions : List Nat} {queries : List Nat}
  (h1 : N ≥ 2) (h2 : K ≥ 5)
  (h3 : directions = [1, 2])
  (h4 : positions = [0, K/2])
  (h5 : queries.length ≥ 1)
  : List.length (count_crashes N K directions positions queries) = List.length queries := sorry

theorem multiple_queries_result_natural {N K : Nat} {directions positions : List Nat} {queries : List Nat}
  (h1 : N ≥ 2) (h2 : K ≥ 5)
  (h3 : directions = [1, 2])
  (h4 : positions = [0, K/2]) :
  ∀ x ∈ count_crashes N K directions positions queries, x ≥ 0 := sorry

theorem crashes_monotonic_with_time {N K t : Nat} {directions positions : List Nat}
  (h1 : N ≥ 2) (h2 : K ≥ 5) (h3 : t > 0)
  (h4 : directions = [1, 2])
  (h5 : positions = [0, K/2]) :
  (count_crashes N K directions positions [t]).head! ≥ 
  (count_crashes N K directions positions [t-1]).head! := sorry
-- </vc-theorems>