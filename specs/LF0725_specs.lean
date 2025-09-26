-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pattern (k : Nat) : List String := sorry

theorem pattern_length_is_k {k : Nat} (h : k % 2 = 1) :
  let pattern := generate_pattern k
  List.length pattern = k := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_is_symmetric {k : Nat} (h : k % 2 = 1) :
  let pattern := generate_pattern k
  pattern = List.reverse pattern := sorry

theorem pattern_content_valid {k : Nat} (h : k % 2 = 1) :
  let pattern := generate_pattern k
  (∀ line ∈ pattern, ∀ c ∈ line.data, c = '*' ∨ c = ' ') ∧ 
  pattern.head? = some "*" ∧
  pattern.getLast? = some "*" ∧
  (k > 1 → pattern.get? 1 = some "**") := sorry

theorem middle_lines_format {k : Nat} (h : k % 2 = 1) :
  let pattern := generate_pattern k
  let mid := k / 2
  ∀ i, 2 ≤ i → i < mid →
    let line := pattern.get! i
    line.data.head? = some '*' ∧ 
    line.data.getLast? = some '*' ∧
    (∀ c ∈ (line.data.drop 1).dropLast, c = ' ') := sorry
-- </vc-theorems>