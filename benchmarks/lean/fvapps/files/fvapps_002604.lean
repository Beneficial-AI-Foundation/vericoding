-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def near_flatten (arr: List (List (List Int))) : List (List Int) := sorry

def list_min (l: List Int) : Int :=
  match l with
  | [] => 0
  | x::xs => xs.foldl min x
-- </vc-definitions>

-- <vc-theorems>
theorem near_flatten_keeps_list_structure (arr: List (List (List Int))) : 
  let result := near_flatten arr
  -- Result is a list of lists of integers
  ∀ x ∈ result, x.all (fun i => true)
  := sorry

theorem near_flatten_sorted (arr: List (List (List Int))) :
  let result := near_flatten arr
  ∀ i, i + 1 < result.length →
    list_min (result.get ⟨i, by sorry⟩) ≤ list_min (result.get ⟨i+1, by sorry⟩)
  := sorry
-- </vc-theorems>