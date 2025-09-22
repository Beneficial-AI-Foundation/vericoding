-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_awkwardness (s : String) : Nat := sorry

-- Result should be non-negative
-- </vc-definitions>

-- <vc-theorems>
theorem min_awkwardness_nonneg (s : String) : 
  min_awkwardness s ≥ 0 := sorry

-- Single character strings should return 0 

theorem min_awkwardness_single_char (c : Char) : 
  min_awkwardness (String.mk [c]) = 0 := sorry

-- All same character strings return 0

theorem min_awkwardness_same_chars {s : String} 
  (h : ∀ (i j : String.Pos), s.get i = s.get j) :
  min_awkwardness s = 0 := sorry

-- Result is symmetric when swapping b and g

theorem min_awkwardness_symmetric (s : String) : 
  min_awkwardness (String.map (fun c => if c = 'b' then 'g' else if c = 'g' then 'b' else c) s) = min_awkwardness s := sorry

-- Length 2 different chars give result 1

theorem min_awkwardness_two_diff (s : String) 
  (h1 : s.length = 2)
  (h2 : ∃ (i j : String.Pos), s.get i = 'b' ∧ s.get j = 'g') :
  min_awkwardness s = 1 := sorry

-- Only works with strings containing b and g

theorem min_awkwardness_valid_chars (s : String) :
  (∀ (i : String.Pos), s.get i = 'b' ∨ s.get i = 'g') → 
  min_awkwardness s ≥ 0 := sorry
-- </vc-theorems>