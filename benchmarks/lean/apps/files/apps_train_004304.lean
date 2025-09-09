def List.maximum' (l : List Int) (h : l ≠ []) : Int :=
  match l with
  | [] => by contradiction
  | x :: xs => xs.foldl max x

-- <vc-helpers>
-- </vc-helpers>

def array_operations (arr : List Int) (k : Nat) : List Int := sorry

theorem array_operations_length_preserved (arr : List Int) (k : Nat) (h : arr ≠ []) :
  (array_operations arr k).length = arr.length := sorry

theorem array_operations_zero_identity (arr : List Int) (h : arr ≠ []) :
  array_operations arr 0 = arr := sorry

theorem array_operations_input_preservation (arr : List Int) (k : Nat) :
  let original := arr
  array_operations arr k = array_operations original k := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible