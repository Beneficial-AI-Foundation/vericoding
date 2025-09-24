-- <vc-preamble>
def exchange_sort (sequence : List Int) : Nat :=
  sorry

def isSorted (l : List Int) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: rest => x ≤ y && isSorted (y :: rest)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count (x : Int) (l : List Int) : Nat :=
  match l with
  | [] => 0
  | h :: t => (if h = x then 1 else 0) + count x t
-- </vc-definitions>

-- <vc-theorems>
theorem exchange_sort_nonnegative {sequence : List Int}
  (h : ∀ x ∈ sequence, x ≥ 7 ∧ x ≤ 9) :
  exchange_sort sequence ≥ 0 := sorry

theorem exchange_sort_zero_when_sorted {sequence : List Int}
  (h₁ : ∀ x ∈ sequence, x ≥ 7 ∧ x ≤ 9)
  (h₂ : isSorted sequence = true) :
  exchange_sort sequence = 0 := sorry

theorem exchange_sort_bounded_by_length {sequence : List Int}
  (h : ∀ x ∈ sequence, x ≥ 7 ∧ x ≤ 9) :
  exchange_sort sequence ≤ sequence.length := sorry

theorem exchange_sort_preserves_frequency {sequence : List Int}
  (h : ∀ x ∈ sequence, x ≥ 7 ∧ x ≤ 9) :
  ∀ x, count x sequence = count x (List.mergeSort (· ≤ ·) sequence) := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval exchange_sort [7, 7, 8, 8, 9, 9]

/-
info: 1
-/
-- #guard_msgs in
-- #eval exchange_sort [9, 7, 8, 8, 9, 7]

/-
info: 4
-/
-- #guard_msgs in
-- #eval exchange_sort [8, 8, 7, 9, 9, 9, 8, 9, 7]
-- </vc-theorems>