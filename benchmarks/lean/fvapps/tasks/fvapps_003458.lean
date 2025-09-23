-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.diff : List α → List α → List α 
  | xs, ys => sorry

-- Elements in result must come from input lists
-- </vc-definitions>

-- <vc-theorems>
theorem diff_elements_from_inputs {α} (a b : List α) (x : α) :
  x ∈ List.diff a b → x ∈ a ∨ x ∈ b
  := sorry

-- Elements in result must be unique 

theorem diff_unique {α} (a b : List α) :
  List.Nodup (List.diff a b)
  := sorry

-- If inputs are same (up to permutation), result is empty

theorem diff_same {α} (a b : List α) :
  a = b → List.diff a b = []
  := sorry

-- Symmetric property

theorem diff_symmetric {α} (a b : List α) :
  List.diff a b = List.diff b a
  := sorry

-- Identity property

theorem diff_identity {α} (xs : List α) :
  List.diff xs xs = []
  := sorry
-- </vc-theorems>