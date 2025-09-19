-- <vc-preamble>
def keep_order (arr : List Int) (val : Int) : Nat := sorry

theorem keep_order_bounds {arr : List Int} {val : Int} :
  let idx := keep_order arr val
  0 ≤ idx ∧ idx ≤ arr.length := sorry

def min_of_list (arr : List Int) : Int :=
  match arr with
  | [] => 0
  | x::xs => xs.foldl min x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_of_list (arr : List Int) : Int :=
  match arr with
  | [] => 0
  | x::xs => xs.foldl max x
-- </vc-definitions>

-- <vc-theorems>
theorem keep_order_before {arr : List Int} {val : Int} :
  let idx := keep_order arr val
  ∀ i, i < idx → arr[i]! < val := sorry
-- </vc-theorems>