-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_longest (numbers : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_longest_in_list (numbers : List Int) 
  (h : numbers ≠ []) : 
  find_longest numbers ∈ numbers :=
  sorry

theorem find_longest_has_max_len (numbers : List Int) 
  (h : numbers ≠ []) :
  ∀ x ∈ numbers, 
    (toString (find_longest numbers)).length ≥ (toString x).length :=
  sorry

theorem ties_return_first (numbers : List Int)
  (h : numbers.length ≥ 2) :
  let result := find_longest numbers
  let maxLen := (toString result).length 
  numbers.find? (fun x => (toString x).length = maxLen) = some result :=
  sorry
-- </vc-theorems>