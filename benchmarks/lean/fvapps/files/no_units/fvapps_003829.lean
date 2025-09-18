-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def days_represented (trips : List (Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem days_represented_nonnegative (trips : List (Nat × Nat)) :
  days_represented trips ≥ 0 :=
  sorry

theorem days_represented_upper_bound (trips : List (Nat × Nat)) (h : trips ≠ []) :
  let maxRange := trips.foldl (fun acc p => max acc (p.2 - p.1 + 1)) 0;
  days_represented trips ≤ trips.length * maxRange :=
  sorry

theorem days_represented_single_trip (s e : Nat) :
  s ≤ e →
  days_represented [(s, e)] = e - s + 1 :=
  sorry

theorem days_represented_empty :
  days_represented [] = 0 :=
  sorry

theorem days_represented_idempotent (trips : List (Nat × Nat)) :
  days_represented trips = days_represented trips :=
  sorry

theorem days_represented_permutation_invariant {trips₁ trips₂ : List (Nat × Nat)} :
  trips₁.length = trips₂.length →
  days_represented trips₁ = days_represented trips₂ :=
  sorry
-- </vc-theorems>