-- <vc-preamble>
def isSorted (l : List Int) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x::y::xs => x ≤ y ∧ isSorted (y::xs)

def count (x : Int) (l : List Int) : Nat :=
  match l with
  | [] => 0
  | h::t => (if h = x then 1 else 0) + count x t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_unique_balls (arr1 arr2 : List Int) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unique_balls_elements_from_inputs {arr1 arr2 : List Int} :
  let result := find_unique_balls arr1 arr2
  ∀ x ∈ result, x ∈ arr1 ++ arr2 :=
sorry

theorem identical_arrays_empty {arr : List Int} :
  find_unique_balls arr arr = [] :=
sorry
-- </vc-theorems>