def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
-- spec
let spec (result: Nat) :=
-- every character in the string is counted once
result = 0 ↔ string.isEmpty ∧
(0 < result → result - 1 = implementation (string.drop 1))
-- program termination
∃ result, implementation string = result ∧
spec result

def implementation (string: String): Nat := string.length

-- LLM HELPER
lemma string_length_zero_iff_empty (s: String) : s.length = 0 ↔ s.isEmpty := by
  simp [String.isEmpty]

-- LLM HELPER
lemma string_length_drop_one (s: String) : s.length > 0 → s.length - 1 = (s.drop 1).length := by
  intro h
  simp [String.drop]
  sorry

theorem correctness
(string: String)
: problem_spec implementation string := by
  unfold problem_spec
  simp [implementation]
  constructor
  · simp [string_length_zero_iff_empty]
  · intro h
    exact string_length_drop_one string h