-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def segments (m: Nat) (segs: List (Nat × Nat)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_segments {m : Nat} (h : m ≤ 100) :
  segments m [] = List.range (m + 1) :=
sorry

theorem result_in_bounds {m : Nat} {segs : List (Nat × Nat)} (h : m ≤ 100) :
  ∀ x ∈ segments m segs, 0 ≤ x ∧ x ≤ m :=
sorry

theorem result_ordered {m : Nat} {segs : List (Nat × Nat)} (h : m ≤ 100) :
  List.Pairwise (· ≤ ·) (segments m segs) :=
sorry

theorem not_covered_by_segments {m : Nat} {segs : List (Nat × Nat)} (h : m ≤ 100) :
  ∀ x ∈ segments m segs,
    ∀ seg ∈ segs, ¬(seg.1 ≤ x ∧ x ≤ seg.2) :=
sorry

theorem missing_covered_by_segments {m : Nat} {segs : List (Nat × Nat)} (h : m ≤ 100) :
  ∀ x ≤ m, x ∉ segments m segs →
    ∃ seg ∈ segs, seg.1 ≤ x ∧ x ≤ seg.2 :=
sorry

theorem full_coverage {m : Nat} (h : m ≤ 100) :
  segments m [(0,m)] = [] :=
sorry
-- </vc-theorems>