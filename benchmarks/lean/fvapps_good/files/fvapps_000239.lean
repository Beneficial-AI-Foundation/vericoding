-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def flipgame (fronts : List Nat) (backs : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flipgame_result_in_input_lists (fronts backs : List Nat) :
  fronts.length = backs.length →
  let result := flipgame fronts backs
  result ≠ 0 →
  result ∈ fronts ∨ result ∈ backs :=
sorry

theorem flipgame_result_not_same_card (fronts backs : List Nat) :
  fronts.length = backs.length →
  let result := flipgame fronts backs
  result ≠ 0 →
  ¬∃ i, i < fronts.length ∧ fronts[i]! = backs[i]! ∧ fronts[i]! = result :=
sorry

theorem flipgame_result_is_minimal (fronts backs : List Nat) :
  fronts.length = backs.length →
  let result := flipgame fronts backs
  result ≠ 0 →
  ∀ n, (n ∈ fronts ∨ n ∈ backs) →
    (¬∃ i, i < fronts.length ∧ fronts[i]! = backs[i]! ∧ fronts[i]! = n) →
    result ≤ n :=
sorry

theorem flipgame_identical_numbers (n length : Nat) :
  length > 0 →
  flipgame (List.replicate length n) (List.replicate length n) = 0 :=
sorry

theorem flipgame_two_different_numbers (n1 n2 : Nat) :
  n1 ≠ n2 →
  n1 > 0 →
  n2 > 0 →
  flipgame [n1] [n2] = min n1 n2 :=
sorry
-- </vc-theorems>