-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern (n : Int) : String := sorry

def String.replicate (n : Nat) (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_positive (n : Int) (h : 1 ≤ n ∧ n ≤ 100) : 
  let lines := (pattern n).split (· == '\n')
  (lines.length = n) ∧ 
  ∀ i : Nat, i < n → 
    lines[i]! = String.replicate (i+1) (toString (i+1)) := sorry

theorem pattern_non_positive (n : Int) (h : n ≤ 0) :
  pattern n = "" := sorry

theorem pattern_output_structure : 
  let lines := (pattern 5).split (· == '\n')
  (∀ line ∈ lines, line.all Char.isDigit) ∧ 
  (∀ line ∈ lines, line.length > 0 → 
    ∀ c ∈ line.data, c = line.get! 0) ∧
  (∀ i : Nat, i < lines.length → 
    let line := lines[i]!
    String.toNat! (toString (line.get! 0)) = line.length) := sorry
-- </vc-theorems>