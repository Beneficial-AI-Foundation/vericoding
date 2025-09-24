-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mutuallyExclusive (dice : List (Nat × Float)) (call1 : Nat) (call2 : Nat) : Option String := sorry

def sum_float_list (l : List Float) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_probabilities_returns_none :
  ∀ (dice : List (Nat × Float)) (call1 call2 : Nat),
  sum_float_list (dice.map (fun p => p.2)) < 0.9 →
  mutuallyExclusive dice call1 call2 = none :=
sorry

theorem valid_probabilities_sum_correctly :
  mutuallyExclusive [(1, 0.2), (2, 0.2), (3, 0.2), (4, 0.2), (5, 0.2)] 1 2 = some "0.40" ∧
  mutuallyExclusive [(1, 0.3), (2, 0.3), (3, 0.4)] 1 2 = some "0.60" :=
sorry
-- </vc-theorems>