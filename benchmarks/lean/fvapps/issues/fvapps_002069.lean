-- <vc-preamble>
def abs (x : Float) : Float :=
sorry

def List.sum (xs : List Float) : Float :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tree_shrinking_probabilities (n : Nat) (edges : List (Nat × Nat)) : List Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tree_shrinking_probabilities_length_matches_input (n : Nat) (edges : List (Nat × Nat)) :
  List.length (tree_shrinking_probabilities n edges) = n :=
sorry

theorem tree_shrinking_probabilities_in_probability_range (n : Nat) (edges : List (Nat × Nat)) :
  ∀ p ∈ tree_shrinking_probabilities n edges, 0 ≤ p ∧ p ≤ 1 :=
sorry

theorem tree_shrinking_probabilities_sum_to_one (n : Nat) (edges : List (Nat × Nat)) :
  let probs := tree_shrinking_probabilities n edges 
  Float.abs (List.sum probs - 1) < 1e-6 :=
sorry
-- </vc-theorems>