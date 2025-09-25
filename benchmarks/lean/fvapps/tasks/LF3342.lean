-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maximum (xs : List Int) : Int :=
sorry

def minimum (xs : List Int) : Int :=
sorry

def sorted (xs : List Int) : List Int :=
sorry

def max_gap (xs : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_gap_positive (xs : List Int) (h : xs.length ≥ 2) :
  max_gap xs ≥ 0 :=
sorry

theorem max_gap_bounded_by_range (xs : List Int) (h : xs.length ≥ 2) :
  max_gap xs ≤ maximum xs - minimum xs :=
sorry

theorem max_gap_in_consecutive_diffs (xs : List Int) (h : xs.length ≥ 2) :
  ∃ i : Nat, i < xs.length - 1 ∧
    max_gap xs = (sorted xs).get ⟨i+1, sorry⟩ - (sorted xs).get ⟨i, sorry⟩ :=
sorry

theorem max_gap_reversal_invariant (xs : List Int) (h : xs.length ≥ 2) :
  max_gap xs = max_gap xs.reverse :=
sorry

theorem max_gap_nonnegative_bounded (xs : List Int) (h : xs.length ≥ 2)
  (h2 : ∀ x ∈ xs, x ≥ 0) :
  max_gap xs ≤ maximum xs :=
sorry

theorem max_gap_translation_invariant (xs : List Int) (c : Int) (h : xs.length ≥ 2) :
  max_gap xs = max_gap (xs.map (· + c)) :=
sorry
-- </vc-theorems>