-- <vc-preamble>
def min_of_list (arr : List Int) : Int :=
  match arr with
  | [] => 0
  | x::xs => xs.foldl min x

def max_of_list (arr : List Int) : Int :=
  match arr with
  | [] => 0
  | x::xs => xs.foldl max x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def keep_order (arr : List Int) (val : Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem keep_order_bounds {arr : List Int} {val : Int} :
  let idx := keep_order arr val
  0 ≤ idx ∧ idx ≤ arr.length :=
sorry

theorem keep_order_before {arr : List Int} {val : Int} :
  let idx := keep_order arr val
  ∀ i, i < idx → arr[i]! < val :=
sorry
-- </vc-theorems>