-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_seconds_to_destroy (colors : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_seconds_positive (colors : List Nat) :
  colors ≠ [] → min_seconds_to_destroy colors > 0 :=
  sorry

theorem min_seconds_upper_bound (colors : List Nat) :
  colors ≠ [] → min_seconds_to_destroy colors ≤ colors.length :=
  sorry

theorem min_seconds_single_color (colors : List Nat) (h : ∀ i j, i < colors.length → j < colors.length → colors[i]! = colors[j]!) :
  min_seconds_to_destroy colors = 1 :=
  sorry

theorem min_seconds_adjacent_match (colors : List Nat) :
  colors.length ≥ 2 →
  (∃ i, i < colors.length - 1 ∧ colors[i]! = colors[i+1]!) →
  min_seconds_to_destroy colors < colors.length :=
  sorry

theorem min_seconds_symmetric (colors : List Nat) :
  min_seconds_to_destroy colors = min_seconds_to_destroy colors.reverse :=
  sorry

theorem min_seconds_all_different (n : Nat) (colors : List Nat)
  (h1 : colors.length = n)
  (h2 : ∀ i j, i < n → j < n → i ≠ j → colors[i]! ≠ colors[j]!) :
  min_seconds_to_destroy colors = n :=
  sorry
-- </vc-theorems>