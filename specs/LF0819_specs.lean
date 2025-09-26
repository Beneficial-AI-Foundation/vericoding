-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern_generator (k : Nat) : List String := sorry

theorem pattern_length {k : Nat} (h : k > 0) :
  (pattern_generator k).length = k := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_star_count {k : Nat} (h : k > 0) :
  ∀ line ∈ pattern_generator k, (line.data.filter (· = '*')).length = 1 := sorry

theorem pattern_valid_chars {k : Nat} (h : k > 0) :
  ∀ line ∈ pattern_generator k, ∀ c ∈ line.data, c = ' ' ∨ c = '*' := sorry

theorem pattern_ends_with_star {k : Nat} (h : k > 0) :
  ∀ line ∈ pattern_generator k, line.endsWith "*" := sorry

theorem pattern_symmetry {k : Nat} (h : k > 0) :
  ∀ i, i < k/2 → 
    let lines := pattern_generator k
    ((lines.get! i).data.filter (· = ' ')).length = i ∧
    ((lines.get! (k - 1 - i)).data.filter (· = ' ')).length = i := sorry
-- </vc-theorems>