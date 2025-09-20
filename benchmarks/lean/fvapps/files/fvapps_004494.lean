-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def base_finder (nums : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem base_detection {base : Nat} (h1 : 2 ≤ base) (h2 : base ≤ 10) :
  let numbers := List.map toString (List.range base)
  base_finder numbers = base :=
sorry

theorem base_repeating_digits {base : Nat} (h1 : 2 ≤ base) (h2 : base ≤ 10) :
  let numbers := List.map (fun x => toString x ++ toString x) (List.range base)
  base_finder numbers = base :=
sorry

theorem base_varying_lengths {base : Nat} (h1 : 2 ≤ base) (h2 : base ≤ 10) :
  let numbers := List.map (fun i => String.mk (List.replicate (i+1) '0')) (List.range base)
  base_finder numbers = 1 := 
sorry

theorem base_empty_sequence :
  base_finder [] = 0 :=
sorry
-- </vc-theorems>