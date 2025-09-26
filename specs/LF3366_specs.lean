-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseMiddle {α : Type} (xs : List α) : List α := sorry

theorem length_reverseMiddle {α : Type} (xs : List α) 
  (h : xs.length ≥ 4) :
  (reverseMiddle xs).length = xs.length - 2 * ((xs.length)/2 - 1) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem elements_from_middle {α : Type} (xs : List α) 
  (h : xs.length ≥ 4) :
  ∃ start : Nat,
    start = xs.length/2 - 1 ∧ 
    reverseMiddle xs = (xs.drop start).take (xs.length - 2*start) :=  
sorry

theorem is_reversed_middle {α : Type} (xs : List α)
  (h : xs.length ≥ 4) :
  let start := xs.length/2 - 1
  let middle := (xs.drop start).take (xs.length - 2*start)
  reverseMiddle xs = middle.reverse :=
sorry
-- </vc-theorems>