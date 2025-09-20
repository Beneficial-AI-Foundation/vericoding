-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern_generator (n : Nat) : List String := sorry

def containsSubstr (s : String) (sub : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_generator_result_nonempty (k : Nat) (h : k > 0) : 
  pattern_generator k ≠ [] := sorry

theorem pattern_generator_length (k : Nat) (h : k > 0) :
  (pattern_generator k).length = k := sorry

theorem pattern_generator_valid_chars (k : Nat) (h : k > 0) :
  ∀ line ∈ pattern_generator k, ∀ c ∈ line.data, c.isDigit ∨ c = ' ' := sorry

theorem pattern_generator_contains_numbers (k : Nat) (h : k > 0) :
  ∀ i : Nat, 1 ≤ i → i ≤ 3 * (k-1) → 
    ∃ line ∈ pattern_generator k, containsSubstr line (toString i) := sorry

theorem pattern_generator_first_line (k : Nat) (h : k > 0) :
  (pattern_generator k).head! = "1" ∨ 
  (pattern_generator k).head!.startsWith "1" := sorry

theorem pattern_generator_last_line (k : Nat) (h : k > 0) :
  ¬(pattern_generator k).getLast!.contains ' ' := sorry

theorem pattern_generator_single (k : Nat) (h : k = 1) :
  pattern_generator k = ["1"] := sorry

theorem pattern_generator_two (k : Nat) (h : k = 2) :
  (pattern_generator k).length = 2 ∧
  (pattern_generator k).head! = "1" := sorry
-- </vc-theorems>