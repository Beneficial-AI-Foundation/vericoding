-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveEugeneHomework (a n m : Nat) : Nat :=
  sorry

def repeatedNum (a n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_eugene_homework_range (a n m : Nat)
  (ha : 1 ≤ a ∧ a ≤ 10^9)
  (hn : 1 ≤ n ∧ n ≤ 100)
  (hm : 2 ≤ m ∧ m ≤ 10^9) :
  let result := solveEugeneHomework a n m
  0 ≤ result ∧ result < m :=
sorry

theorem solve_eugene_homework_correct (a n m : Nat)
  (ha : 1 ≤ a ∧ a ≤ 10^9)
  (hn : 1 ≤ n ∧ n ≤ 100)
  (hm : 2 ≤ m ∧ m ≤ 10^9) :
  solveEugeneHomework a n m = repeatedNum a n % m :=
sorry

theorem modulo_one_is_zero (a n : Nat)
  (ha : 1 ≤ a ∧ a ≤ 10^6)
  (hn : 1 ≤ n ∧ n ≤ 100) :
  solveEugeneHomework a n 1 = 0 :=
sorry

theorem single_repeat (a m : Nat)
  (ha : 1 ≤ a ∧ a ≤ 10^6)
  (hm : 2 ≤ m ∧ m ≤ 10^6) :
  solveEugeneHomework a 1 m = a % m :=
sorry
-- </vc-theorems>