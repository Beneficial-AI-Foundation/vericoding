-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Edge := List Int
def max_removable_edges (n : Int) (edges : List Edge) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_edges_result {n : Int} (hn : n ≥ 0) :
  max_removable_edges n [] = if n = 0 then 0 else -1 :=
  sorry
-- </vc-theorems>