-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_start_value (nums : List Int) : Int := sorry

def running_sums (start : Int) (nums : List Int) : List Int :=
  match nums with
  | [] => [start]
  | x::xs => let rest := running_sums (start + x) xs
             start :: rest
-- </vc-definitions>

-- <vc-theorems>
theorem min_start_single_element (x : Int) :
  let start := min_start_value [x]
  start ≥ 1 ∧ start + x ≥ 1 := sorry
-- </vc-theorems>