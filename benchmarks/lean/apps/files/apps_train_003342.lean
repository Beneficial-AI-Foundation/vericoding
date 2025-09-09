def maximum (xs : List Int) : Int := sorry
def minimum (xs : List Int) : Int := sorry

-- <vc-helpers>
-- </vc-helpers>

def sorted (xs : List Int) : List Int := sorry
def max_gap (xs : List Int) : Int := sorry

theorem max_gap_positive (xs : List Int) (h : xs.length ≥ 2) : 
  max_gap xs ≥ 0 := sorry

theorem max_gap_bounded_by_range (xs : List Int) (h : xs.length ≥ 2) :
  max_gap xs ≤ maximum xs - minimum xs := sorry

theorem max_gap_in_consecutive_diffs (xs : List Int) (h : xs.length ≥ 2) :
  ∃ i : Nat, i < xs.length - 1 ∧ 
    max_gap xs = (sorted xs).get ⟨i+1, sorry⟩ - (sorted xs).get ⟨i, sorry⟩ := sorry

theorem max_gap_reversal_invariant (xs : List Int) (h : xs.length ≥ 2) :
  max_gap xs = max_gap xs.reverse := sorry

theorem max_gap_nonnegative_bounded (xs : List Int) (h : xs.length ≥ 2) 
  (h2 : ∀ x ∈ xs, x ≥ 0) :
  max_gap xs ≤ maximum xs := sorry

theorem max_gap_translation_invariant (xs : List Int) (c : Int) (h : xs.length ≥ 2) :
  max_gap xs = max_gap (xs.map (· + c)) := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval max_gap [13, 10, 2, 9, 5]

/-
info: 23
-/
-- #guard_msgs in
-- #eval max_gap [-3, -27, -4, -2]

/-
info: 576
-/
-- #guard_msgs in
-- #eval max_gap [-54, 37, 0, 64, -15, 640, 0]

-- Apps difficulty: introductory
-- Assurance level: unguarded