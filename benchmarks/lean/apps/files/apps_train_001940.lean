-- <vc-preamble>
def find_min_questions (n : Nat) : List Nat :=
  sorry

def isPrime (n : Nat) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrimePower (n : Nat) : Bool := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_questions_output_type (n : Nat) :
  ∀ x ∈ find_min_questions n, x ≤ n := by
  sorry

theorem find_min_questions_ordering (n : Nat) :
  ∀ (l : List Nat), l = find_min_questions n →
    ∀ i, i + 1 < l.length → 
      l.get! i > l.get! (i + 1) →
      isPrime (l.get! (i + 1)) := by
  sorry

theorem find_min_questions_empty_for_one :
  find_min_questions 1 = [] := by
  sorry

theorem find_min_questions_nonempty_for_gt_one (n : Nat) :
  n > 1 →
  (find_min_questions n).length > 0 ∧
  ∀ x ∈ find_min_questions n, x ≥ 2 := by
  sorry

theorem find_min_questions_prime_powers (n : Nat) :
  ∀ x ∈ find_min_questions n, isPrimePower x := by
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval len find_min_questions(4)

/-
info: 4
-/
-- #guard_msgs in
-- #eval len find_min_questions(6)

/-
info: 0
-/
-- #guard_msgs in
-- #eval len find_min_questions(1)
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded