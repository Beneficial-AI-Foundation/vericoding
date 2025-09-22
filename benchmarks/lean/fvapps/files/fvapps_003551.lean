-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (x : Float) : Float := if x < 0 then -x else x

def vector_affinity (xs ys : List Int) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem self_affinity (xs : List Int) :
  vector_affinity xs xs = 1.0 := sorry

theorem affinity_bounds (xs ys : List Int) : 
  0 ≤ vector_affinity xs ys ∧ vector_affinity xs ys ≤ 1.0 := sorry

theorem affinity_symmetric (xs ys : List Int) :
  abs (vector_affinity xs ys - vector_affinity ys xs) < 1e-10 := sorry

theorem empty_lists :
  vector_affinity [] [] = 1.0 := sorry

theorem empty_with_nonempty (xs : List Int) :
  (xs = [] → vector_affinity xs xs = 1.0) ∧
  (xs ≠ [] → vector_affinity xs [] = 0.0 ∧ vector_affinity [] xs = 0.0) := sorry
-- </vc-theorems>