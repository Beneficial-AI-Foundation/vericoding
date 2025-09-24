-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern (n : Nat) (y : Nat := 1) : String := sorry

def stringToNat (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_empty (n : Nat) :
  (n = 0 ∨ n < 0) → pattern n = "" := sorry

theorem pattern_basic_properties (n : Nat) (h : 0 < n ∧ n ≤ 9) :
  let result := pattern n
  let lines := result.splitOn "\n"
  (∀ d ∈ (String.join lines).data.filter Char.isDigit, 
    0 ≤ (stringToNat d.toString) ∧ (stringToNat d.toString) ≤ 9) ∧
  lines.get! 0 = lines.get! (lines.length - 1) ∧
  (lines.get! 0).contains '1' ∧
  (lines.get! (n-1)).contains ((toString n).data.get! 0) := sorry

theorem pattern_repetition (n y : Nat) (h1 : 0 < n ∧ n ≤ 5) (h2 : 0 < y ∧ y ≤ 3) :
  let result := pattern n y
  let lines := result.splitOn "\n"
  let matchingLines := (List.range lines.length).filter (λ i => lines.get! i = lines.get! 0)
  lines.get! 0 = lines.get! (lines.length - 1) ∧
  (lines.get! 0).contains '1' ∧
  matchingLines.length ≥ y := sorry
-- </vc-theorems>