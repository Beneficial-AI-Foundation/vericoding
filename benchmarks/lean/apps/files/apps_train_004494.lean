-- <vc-helpers>
-- </vc-helpers>

def base_finder (nums : List String) : Nat :=
  sorry

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

/-
info: 10
-/
-- #guard_msgs in
-- #eval base_finder ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]

/-
info: 7
-/
-- #guard_msgs in
-- #eval base_finder ["1", "2", "3", "4", "5", "6", "10", "11", "12", "13"]

/-
info: 6
-/
-- #guard_msgs in
-- #eval base_finder ["301", "302", "303", "304", "305", "310", "311", "312", "313", "314"]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible