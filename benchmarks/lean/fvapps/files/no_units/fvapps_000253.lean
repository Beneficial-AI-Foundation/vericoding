-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxProbability (n : Nat) (edges : List (List Nat)) (probs : List Float) 
  (s : Nat) (t : Nat) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxProbability_bounded (n : Nat) (edges : List (List Nat)) (probs : List Float)
  (s t : Nat) :
  0 ≤ maxProbability n edges probs s t ∧ maxProbability n edges probs s t ≤ 1 := sorry

theorem maxProbability_same_node (n : Nat) (edges : List (List Nat)) (probs : List Float)
  (s : Nat) :
  maxProbability n edges probs s s = 1 := sorry

theorem maxProbability_symmetry (n : Nat) (edges : List (List Nat)) (probs : List Float)
  (s t : Nat) :
  (maxProbability n edges probs s t - maxProbability n edges probs t s).abs < 1e-10 := sorry
-- </vc-theorems>