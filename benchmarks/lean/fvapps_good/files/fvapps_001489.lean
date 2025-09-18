-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pattern (k : Nat) : List String := sorry

theorem pattern_length {k : Nat} (h : k > 0) :
  List.length (generate_pattern k) = k := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_last_line {k : Nat} (h : k > 0) :
  List.get! (generate_pattern k) (k - 1) = "*".append (String.join (List.replicate (k-1) "*")) := sorry

theorem pattern_first_line {k : Nat} (h : k > 0) :
  List.head! (generate_pattern k) = "*" := sorry

theorem pattern_middle_lines {k : Nat} (h : k > 2) (i : Nat) (hi : i > 0 ∧ i < k - 1) :
  let line := List.get! (generate_pattern k) i
  line.length = i + 1 ∧
  (∀ c ∈ line.data, c = '*' ∨ c = ' ') := sorry
-- </vc-theorems>