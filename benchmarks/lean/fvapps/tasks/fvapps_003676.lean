-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binary_simulation (s : String) (ops : List (List Nat)) : List Char := sorry

def simple_simulate (s : String) (ops : List (List Nat)) : List Char := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binary_simulation_matches_reference (s : String) (ops : List (List Nat)) :
  binary_simulation s ops = simple_simulate s ops := sorry

theorem queries_only_match_original (s : String) (queries : List (List Nat)) 
  (h : ∀ q ∈ queries, q.head! = 2 → q.length = 2) :
  binary_simulation s queries = simple_simulate s queries := sorry

theorem double_inversion_cancels (s : String) :
  let i := 1
  let j := s.length 
  let ops := [[0, i, j], [0, i, j], [1, 1]]
  binary_simulation s ops = [s.get 0] := sorry
-- </vc-theorems>