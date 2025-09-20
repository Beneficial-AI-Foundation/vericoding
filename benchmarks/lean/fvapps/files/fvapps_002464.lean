-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_string_indices (s : String) (k : String) : List (Int × Int) := sorry

-- Any result is a list of integer tuples
-- </vc-definitions>

-- <vc-theorems>
theorem find_string_indices_returns_valid_pairs (s k : String) 
  (h₁ : s.length > 0) (h₂ : k.length > 0) :
  ∀ p ∈ (find_string_indices s k), ∃ i j : Int, p = (i, j) := sorry

-- For non-failure results, indices are valid and contain substring

theorem find_string_indices_valid_matches (s k : String)
  (h₁ : s.length > 0) (h₂ : k.length > 0)
  (h₃ : find_string_indices s k ≠ [(-1, -1)]) :
  ∀ p ∈ (find_string_indices s k),
    let i := p.1
    let j := p.2
    0 ≤ i ∧ i ≤ j ∧ j < s.length := sorry

-- Results are ordered and non-overlapping

theorem find_string_indices_ordered (s k : String)
  (h₁ : s.length > 0) (h₂ : k.length > 0)
  (h₃ : find_string_indices s k ≠ [(-1, -1)])
  (i : Nat) (h₄ : i + 1 < (find_string_indices s k).length) :
  let result := find_string_indices s k
  result[i]!.2 < result[i+1]!.1 := sorry

-- First character match starts at beginning

theorem find_string_indices_first_char (s : String)
  (h : s.length > 0) :
  let result := find_string_indices s (String.mk [s.get 0])
  result ≠ [] → result[0]!.1 = 0 := sorry
-- </vc-theorems>