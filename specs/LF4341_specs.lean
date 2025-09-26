-- <vc-preamble>
def group (arr : List Int) : List (List Int) := sorry

def listSum (xs : List Nat) : Nat := 
  match xs with
  | [] => 0
  | h :: t => h + listSum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listSort (xs : List Int) : List Int := sorry

def listIndexOf (xs : List Int) (x : Int) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem group_idempotent {arr : List Int} (h : arr ≠ []) :
  let result1 := group arr;
  let flattened := result1.join;
  let result2 := group flattened;
  result1 = result2 :=
sorry
-- </vc-theorems>