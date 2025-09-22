-- <vc-preamble>
def list_maximum (l : List Int) : Option Int :=
  l.foldl (fun acc x => match acc with
    | none => some x
    | some m => some (max m x)) none
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def small_enough (numbers : List Int) (limit : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem small_enough_characterization (numbers : List Int) (limit : Int)
    (h : numbers ≠ []) :
  small_enough numbers limit = ((list_maximum numbers).getD 0 ≤ limit) :=
sorry

theorem small_enough_at_maximum (numbers : List Int) (h : numbers ≠ []) :
  let max_val := (list_maximum numbers).getD 0
  small_enough numbers max_val = true ∧
  small_enough numbers (max_val - 1) = false :=
sorry

theorem small_enough_scaling (numbers : List Int) (factor : Int)
    (h : numbers ≠ []) (h_pos : factor > 0) :
  let max_val := (list_maximum numbers).getD 0
  let scaled_numbers := numbers.map (· * factor)
  small_enough scaled_numbers (max_val * factor) = small_enough numbers max_val :=
sorry
-- </vc-theorems>