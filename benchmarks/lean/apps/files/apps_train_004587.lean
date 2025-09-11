-- <vc-preamble>
def sort_ranks (ranks: List String) : List String := sorry

def is_valid_version (s: String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def loose_version_le (v1 v2: String) : Bool := sorry

theorem sort_ranks_maintains_elements (ranks: List String) 
  (h: ∀ x ∈ ranks, is_valid_version x) :
  let sorted := sort_ranks ranks
  ∀ x, (x ∈ ranks ↔ x ∈ sorted) ∧
  sorted.length = ranks.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_ranks_ordering (ranks: List String)
  (h1: ranks.length ≥ 2)
  (h2: ∀ x ∈ ranks, is_valid_version x) :
  let sorted := sort_ranks ranks
  ∀ (i: Nat) (h: i + 1 < sorted.length),
    loose_version_le (sorted[i]'(Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_of_lt h)))
                    (sorted[i+1]'h) := sorry

theorem sort_ranks_idempotent (ranks: List String)
  (h: ∀ x ∈ ranks, is_valid_version x) :
  sort_ranks (sort_ranks ranks) = sort_ranks ranks := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval sort_ranks ["2", "1", "1.1"]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval sort_ranks ["3.1", "1", "1.1", "2", "3", "1.2", "3.2", "1.2.1", "3.1.1"]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval sort_ranks ["3", "2", "1"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded