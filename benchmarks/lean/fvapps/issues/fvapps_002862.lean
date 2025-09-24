-- <vc-preamble>
def Dict := List (String × (String ⊕ Int))

def solution (d : Dict) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted (xs : List String) : Prop :=
  ∀ i j, i < j → j < xs.length → xs[i]! ≤ xs[j]!
-- </vc-definitions>

-- <vc-theorems>
theorem solution_output_sorted (d : Dict) (h : d.length > 0) : 
  let result := solution d
  let pairs := result.splitOn ","
  isSorted pairs := by
  sorry

theorem solution_contains_all_pairs (d : Dict) (h : d.length > 0) : 
  let result := solution d
  let pairs := result.splitOn ","  
  ∀ p ∈ d, ∃ pair ∈ pairs, 
    match p.2 with
    | Sum.inl s => pair = s!"{p.1} = {s}"
    | Sum.inr n => pair = s!"{p.1} = {n}" := by
  sorry 

theorem solution_empty (d : Dict) (h : d = []) :
  solution d = "" := by
  sorry

/-
info: 'a = 1,b = 2'
-/
-- #guard_msgs in
-- #eval solution {"a": 1, "b": 2}

/-
info: 'a = b,b = a'
-/
-- #guard_msgs in
-- #eval solution {"a": "b", "b": "a"}

/-
info: ''
-/
-- #guard_msgs in
-- #eval solution {}
-- </vc-theorems>