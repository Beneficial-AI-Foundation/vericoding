-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def only_one (bs : List Bool) : Bool := sorry

def count_true : List Bool → Nat
  | [] => 0
  | true :: rest => 1 + count_true rest 
  | false :: rest => count_true rest
-- </vc-definitions>

-- <vc-theorems>
theorem only_one_empty : 
  only_one [] = false :=
sorry

theorem only_one_exactly_one_true (bs : List Bool) : 
  (count_true bs = 1) → only_one bs = true :=
sorry

theorem only_one_wrong_count (bs : List Bool) :
  (count_true bs ≠ 1) → only_one bs = false := 
sorry

theorem only_one_main (bs : List Bool) :
  only_one bs = (count_true bs = 1) :=
sorry
-- </vc-theorems>