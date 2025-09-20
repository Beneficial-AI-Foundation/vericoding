-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.count (s : String) (c : Char) : Nat :=
sorry

def String.toCharArray (s : String) : Array Char :=
sorry

def String.fromCharArray (arr : Array Char) : String :=
sorry

def has_subpattern (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_substring (s : String) (h : s.length > 0) :
  let result := has_subpattern s

  result.length ≤ s.length ∧

  (∀ i j, i < j → i < result.length → j < result.length →
    result.toCharArray[i]! ≤ result.toCharArray[j]!) ∧

  (∀ c, c ∈ result.toCharArray.toList → c ∈ s.toCharArray.toList) :=
sorry

theorem output_pattern_reconstruction (s : String) (h : s.length > 0) :
  let pattern := has_subpattern s
  let counts_s := s.toCharArray.toList.map (fun c => (c, s.count c))
  let counts_p := pattern.toCharArray.toList.map (fun c => (c, pattern.count c))
  pattern.length > 0 →
  ∃ ratio : Nat, ∀ (s_c p_c : Char) (s_count p_count : Nat),
    (s_c, s_count) ∈ counts_s →
    (p_c, p_count) ∈ counts_p →
    s_count = p_count * ratio :=
sorry

theorem idempotent (s : String) (h : s.length > 0) :
  has_subpattern s = has_subpattern (has_subpattern s) :=
sorry
-- </vc-theorems>