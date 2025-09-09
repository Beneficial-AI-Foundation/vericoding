-- <vc-helpers>
-- </vc-helpers>

def mutuallyExclusive (dice : List (Nat × Float)) (call1 : Nat) (call2 : Nat) : Option String := sorry

def sum_float_list (l : List Float) : Float := sorry

theorem invalid_probabilities_returns_none :
  ∀ (dice : List (Nat × Float)) (call1 call2 : Nat),
  sum_float_list (dice.map (fun p => p.2)) < 0.9 →
  mutuallyExclusive dice call1 call2 = none :=
sorry

theorem valid_probabilities_sum_correctly :
  mutuallyExclusive [(1, 0.2), (2, 0.2), (3, 0.2), (4, 0.2), (5, 0.2)] 1 2 = some "0.40" ∧
  mutuallyExclusive [(1, 0.3), (2, 0.3), (3, 0.4)] 1 2 = some "0.60" :=
sorry

/-
info: None
-/
-- #guard_msgs in
-- #eval mutually_exclusive *test1

/-
info: '0.30'
-/
-- #guard_msgs in
-- #eval mutually_exclusive *test2

/-
info: '0.20'
-/
-- #guard_msgs in
-- #eval mutually_exclusive *test3

-- Apps difficulty: introductory
-- Assurance level: unguarded