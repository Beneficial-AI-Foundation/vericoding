-- <vc-preamble>
def abs (x : Int) : Int :=
  if x < 0 then -x else x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def firstNonConsecutive (arr : List Int) : Option Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_or_single_returns_none (arr : List Int) :
  arr.length ≤ 1 → firstNonConsecutive arr = none :=
sorry

theorem consecutive_returns_none (arr : List Int) (h : arr.length ≥ 2) :
  (∀ i j, i + 1 = j → arr[i]? = some x → arr[j]? = some y → y = x + 1) →
  firstNonConsecutive arr = none :=
sorry

theorem non_consecutive_returns_first_break (arr : List Int) (gap : Int)
    (h1 : arr.length ≥ 3) (h2 : (abs gap) > 1) :
  let pos := arr.length / 2
  let val := arr[pos]?
  match val with
  | none => True
  | some x =>
    let next := arr[pos+1]?
    match next with
    | none => True
    | some y => x + gap = y → firstNonConsecutive arr = some y
  :=
sorry

theorem result_in_input (arr : List Int) :
  match firstNonConsecutive arr with
  | none => True
  | some x => x ∈ arr :=
sorry
-- </vc-theorems>