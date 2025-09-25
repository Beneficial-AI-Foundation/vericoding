-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replace (s : String) : String := sorry

def countGroups (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem replace_preserves_length {s : String} 
  (h : ∀ c ∈ s.data, c = '!' ∨ c = '?') :
  (replace s).length = s.length := sorry

theorem replace_uses_valid_chars {s : String}
  (h : ∀ c ∈ s.data, c = '!' ∨ c = '?') :
  ∀ c ∈ (replace s).data, c = '!' ∨ c = '?' ∨ c = ' ' := sorry 

theorem replace_groups_monotonic {s : String}
  (h : ∀ c ∈ s.data, c = '!' ∨ c = '?') :
  countGroups (replace s) ≤ countGroups s := sorry
-- </vc-theorems>