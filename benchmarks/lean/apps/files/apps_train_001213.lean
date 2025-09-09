-- <vc-helpers>
-- </vc-helpers>

def count_pairs (arr : List Nat) : Nat :=
  sorry

theorem all_ones (arr : List Nat) (h : ∀ x ∈ arr, x = 1) : 
  count_pairs arr = 0 :=
sorry

theorem count_pairs_commutative (arr : List Nat) :
  count_pairs arr = count_pairs arr.reverse :=
sorry

theorem count_pairs_bounds (arr : List Nat) :
  0 ≤ count_pairs arr ∧ count_pairs arr ≤ (arr.length * (arr.length - 1)) / 2 :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded