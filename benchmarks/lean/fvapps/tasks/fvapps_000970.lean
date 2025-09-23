-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pattern (k : Nat) : List String := sorry 

def format_multiple_patterns (cases : List Nat) : List String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem generate_pattern_length (k : Nat) (h : 0 < k ∧ k ≤ 26) :
  (generate_pattern k).length = k := sorry

theorem generate_pattern_alternating (k : Nat) (h : 0 < k ∧ k ≤ 26) (i : Nat) (hi : i < k) :
  let line := (generate_pattern k)[i]'(by 
    rw [generate_pattern_length k h]
    exact hi)
  if i % 2 = 0 
  then ∀ c ∈ line.data, c.isUpper ∧ (c.toNat - 'A'.toNat < i + 1)
  else ∀ c ∈ line.data, c.isDigit := sorry

theorem format_multiple_patterns_length {cases : List Nat} (h : cases ≠ []) 
  (h2 : ∀ k ∈ cases, 0 < k ∧ k ≤ 26) :
  (format_multiple_patterns cases).length = cases.foldl (· + ·) 0 := sorry

theorem format_multiple_patterns_matches {cases : List Nat} (h : cases ≠ [])
  (h2 : ∀ k ∈ cases, 0 < k ∧ k ≤ 26) (pos k : Nat):
  k ∈ cases →
  (format_multiple_patterns cases).take k = generate_pattern k := sorry
-- </vc-theorems>