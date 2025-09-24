-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_shortest_non_subsequence (s : String) : String :=
  sorry

def is_subsequence (needle haystack : String) : Bool :=
  sorry

def generate_strings (length : Nat) : List String :=
  sorry

def all_chars_in_range (s : String) : Bool :=
  sorry

def all_lower (s : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_valid_string (s : String) :
  let result := find_shortest_non_subsequence s
  (result.length > 0) ∧ (all_lower result) := by
  sorry

theorem result_is_minimal (s : String) :
  let result := find_shortest_non_subsequence s
  ∀ n : Nat, n < result.length →
  ∀ possible : String, possible.length = n →
  is_subsequence possible s := by
  sorry

theorem result_for_all_letters {s : String} :
  s.length = 26 →
  (∀ c : Char, c.isLower → s.contains c) →
  find_shortest_non_subsequence s = "aa" := by
  sorry
-- </vc-theorems>