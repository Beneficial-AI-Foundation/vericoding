-- <vc-preamble>
def sum (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | x :: rest => x + sum rest
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split_and_add (numbers : List Int) (n : Nat) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_and_add_empty (n : Nat) :
  split_and_add [] n = [] := sorry

theorem split_and_add_single (x : Int) (n : Nat) :
  split_and_add [x] n = [x] := sorry

theorem split_and_add_sum_preserved (numbers : List Int) (n : Nat) :
  sum numbers = sum (split_and_add numbers n) := sorry

theorem split_and_add_idempotent (numbers : List Int) (n : Nat) :
  let result1 := split_and_add numbers n
  let result2 := split_and_add numbers (n + 1)
  result1.length = 1 → result1 = result2 := sorry

theorem split_and_add_length_decreases {numbers : List Int} (n : Nat) :
  numbers.length ≥ 2 →
  (split_and_add numbers 1).length ≤ numbers.length := sorry
-- </vc-theorems>