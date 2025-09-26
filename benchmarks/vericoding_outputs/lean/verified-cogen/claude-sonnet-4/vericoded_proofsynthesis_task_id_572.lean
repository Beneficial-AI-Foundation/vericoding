import Mathlib
-- <vc-preamble>
/- Recursive helper function to count frequency -/
def countFrequencyRcr (seq : List Int) (key : Int) : Nat :=
  match seq with
  | [] => 0
  | head :: tail => 
      countFrequencyRcr tail key + (if head = key then 1 else 0)

/- Precondition for removeDuplicates -/
@[reducible, simp]
def removeDuplicates_precond (arr : Array Int) := True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def countOccurrences (lst : List Int) (x : Int) : Nat :=
  lst.filter (· = x) |>.length

-- LLM HELPER
def removeDuplicatesAux (lst : List Int) (seen : List Int) : List Int :=
  match lst with
  | [] => []
  | head :: tail =>
      if seen.contains head then
        removeDuplicatesAux tail seen
      else
        let newSeen := head :: seen
        if countOccurrences (head :: tail) head = 1 then
          head :: removeDuplicatesAux tail newSeen
        else
          removeDuplicatesAux tail newSeen

-- LLM HELPER
lemma countFrequencyRcr_eq_filter_length (lst : List Int) (x : Int) :
    countFrequencyRcr lst x = (lst.filter (· = x)).length := by
  induction lst with
  | nil => simp [countFrequencyRcr]
  | cons head tail ih =>
    simp [countFrequencyRcr]
    rw [ih]
    by_cases h : head = x
    · simp [h]
    · simp [h]
-- </vc-helpers>

-- <vc-definitions>
def removeDuplicates (arr : Array Int) (h_precond : removeDuplicates_precond (arr)) : Array Int :=
  Array.mk (arr.toList.filter (fun x => countFrequencyRcr arr.toList x = 1))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeDuplicates_postcond (arr : Array Int) (unique_arr : Array Int) (h_precond : removeDuplicates_precond (arr)) :=
  unique_arr.toList = arr.toList.filter (fun x => countFrequencyRcr arr.toList x = 1)

theorem removeDuplicates_spec_satisfied (arr : Array Int) (h_precond : removeDuplicates_precond (arr)) :
    removeDuplicates_postcond (arr) (removeDuplicates (arr) h_precond) h_precond := by
  simp [removeDuplicates_postcond, removeDuplicates]
-- </vc-theorems>

#check removeDuplicates