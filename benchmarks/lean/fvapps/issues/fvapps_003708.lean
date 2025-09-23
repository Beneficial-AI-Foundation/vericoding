-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def total (arr: List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem total_sequence_property {arr: List Int} (h: arr.length ≥ 2) :
  let first_iter := (arr.zip (arr.tail!)).map (fun p => p.1 + p.2)
  first_iter.length = arr.length - 1 :=
sorry
-- </vc-theorems>