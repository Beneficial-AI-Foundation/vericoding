-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ranks (scores : List Int) : List Nat := sorry

theorem ranks_length_preserved (scores : List Int) :
  (ranks scores).length = scores.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ranks_are_valid (scores : List Int) (h : scores ≠ []) :
  ∀ r ∈ ranks scores, 1 ≤ r ∧ r ≤ scores.length := sorry

theorem ranks_order (scores : List Int) (i j : Nat) 
  (h1 : i < scores.length) (h2 : j < scores.length) :
  scores[i]! > scores[j]! → (ranks scores)[i]! < (ranks scores)[j]! := sorry

theorem ranks_equal (scores : List Int) (i j : Nat)
  (h1 : i < scores.length) (h2 : j < scores.length) :
  scores[i]! = scores[j]! → (ranks scores)[i]! = (ranks scores)[j]! := sorry

theorem ranks_empty :
  ranks [] = [] := sorry
-- </vc-theorems>