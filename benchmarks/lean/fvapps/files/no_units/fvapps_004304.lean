-- <vc-preamble>
def List.maximum' (l : List Int) (h : l ≠ []) : Int :=
  match l with
  | [] => by contradiction
  | x :: xs => xs.foldl max x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array_operations (arr : List Int) (k : Nat) : List Int := sorry

theorem array_operations_length_preserved (arr : List Int) (k : Nat) (h : arr ≠ []) :
  (array_operations arr k).length = arr.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_operations_zero_identity (arr : List Int) (h : arr ≠ []) :
  array_operations arr 0 = arr := sorry

theorem array_operations_input_preservation (arr : List Int) (k : Nat) :
  let original := arr
  array_operations arr k = array_operations original k := sorry
-- </vc-theorems>