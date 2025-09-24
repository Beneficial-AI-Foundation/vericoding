-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_possible (a b : String) : Bool :=
  sorry

def count_ones (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ones_diff_bounds (a b : String) :
  is_possible a b →
  count_ones b ≤ ((count_ones a + 1) / 2) * 2
  ∧
  ¬is_possible a b →
  count_ones b > ((count_ones a + 1) / 2) * 2 :=
sorry

theorem same_string_always_possible (s : String) :
  is_possible s s :=
sorry

theorem all_zeros_possible (s zeros : String) :
  (∀ c ∈ zeros.data, c = '0') →
  s.length = zeros.length →
  is_possible s zeros :=
sorry

theorem length_invariant (s ones : String) :
  (∀ c ∈ ones.data, c = '1') →
  is_possible s ones ↔
  ones.length ≤ ((count_ones s + 1) / 2) * 2 :=
sorry
-- </vc-theorems>