-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_interesting_sequence (n : Nat) (l : Nat) (arr : List Nat) : Nat := sorry

theorem sequence_properties {n : Nat} {l : Nat} {arr : List Nat} 
  (hn : n > 0) (hl : l > 0) (harr : arr.length = n) (hbound : ∀ x ∈ arr, x > 0 ∧ x ≤ 100) :
  let result := solve_interesting_sequence n l arr;
  -- Result is non-negative
  result ≥ 0  
  -- Result is bounded by array length
  ∧ result ≤ n
  -- Result is at least the max distance between duplicates
  ∧ ∀ (x : Nat) (pos₁ pos₂ : Nat),
    let indices : List (Nat × Nat) := List.enumFrom 1 arr;
    let positions := List.filterMap (fun p => if p.2 = x then some p.1 else none) indices;
    pos₁ ∈ positions →
    pos₂ ∈ positions →
    pos₁ ≠ pos₂ →
    result ≥ (max pos₁ pos₂ - min pos₁ pos₂) := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem base_case : solve_interesting_sequence 1 1 [5] = 0 := by sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_interesting_sequence 6 3 [2, 4, 1, 12, 3, 5]

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_interesting_sequence 4 2 [5, 5, 5, 5]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_interesting_sequence 5 3 [1, 2, 3, 4, 5]
-- </vc-theorems>