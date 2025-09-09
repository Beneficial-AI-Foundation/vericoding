-- <vc-helpers>
-- </vc-helpers>

def kooka_counter (s: String) : Nat :=
  sorry

theorem kooka_counter_nonnegative (s: String) : 
  kooka_counter s ≥ 0 := 
sorry

theorem kooka_counter_empty : 
  kooka_counter "" = 0 := 
sorry

theorem kooka_counter_consecutive_laughs (n: Nat) (h: n > 0) :
  kooka_counter (String.join (List.replicate n "ha")) = 1 ∧ 
  kooka_counter (String.join (List.replicate n "Ha")) = 1 :=
sorry

theorem kooka_counter_alternating_laughs (n: Nat) (h: n > 0) :
  let lowerLaugh := String.join (List.replicate n "ha")
  let upperLaugh := String.join (List.replicate n "Ha")
  kooka_counter (lowerLaugh ++ upperLaugh) = 2 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval kooka_counter ""

/-
info: 1
-/
-- #guard_msgs in
-- #eval kooka_counter "hahahahaha"

/-
info: 2
-/
-- #guard_msgs in
-- #eval kooka_counter "hahahahahaHaHaHa"

-- Apps difficulty: introductory
-- Assurance level: unguarded