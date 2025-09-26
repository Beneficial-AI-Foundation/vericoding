-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pattern (k : Nat) : Array (Array Char) := sorry

theorem pattern_size_correct (k : Nat) (h : k > 0) :
  let pattern := generate_pattern k
  (pattern.size = k) ∧ 
  (∀ i : Fin k, pattern[i.val]!.size = k) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_chars_valid (k : Nat) (h : k > 0) :
  let pattern := generate_pattern k
  ∀ i : Fin k, ∀ j : Fin k,
  pattern[i.val]![j.val]! = '0' ∨ pattern[i.val]![j.val]! = '1' := sorry

theorem pattern_alternates_correctly (k : Nat) (h : k > 0) :
  let pattern := generate_pattern k
  ∀ i : Fin k, ∀ j : Fin k,
  pattern[i.val]![j.val]! = (if (i.val + j.val) % 2 = 0 then '0' else '1') := sorry

theorem adjacent_elements_differ (k : Nat) (h : k > 0) :
  let pattern := generate_pattern k
  (∀ i : Fin k, ∀ j : Fin (k-1), pattern[i.val]![j.val]! ≠ pattern[i.val]![(j.val+1)]!) ∧
  (∀ i : Fin (k-1), ∀ j : Fin k, pattern[i.val]![j.val]! ≠ pattern[i.val+1]![j.val]!) := sorry
-- </vc-theorems>