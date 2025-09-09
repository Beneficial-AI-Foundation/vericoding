-- <vc-helpers>
-- </vc-helpers>

def n_closestPairs_tonum (upperLim : Nat) (k : Nat) : List (Nat × Nat) :=
sorry

theorem n_closest_pairs_length (upperLim : Nat) (k : Nat) 
  (h1 : upperLim ≥ 3) (h2 : k ≥ 1) :
  let result := n_closestPairs_tonum upperLim k 
  List.length result ≤ k :=
sorry

theorem n_closest_pairs_bounds (upperLim : Nat) (k : Nat)
  (h1 : upperLim ≥ 3) (h2 : k ≥ 1) :
  let result := n_closestPairs_tonum upperLim k
  ∀ pair ∈ result, 
    (let (m, n) := pair
     m ≤ upperLim ∧ n > 0 ∧ m > n) :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible