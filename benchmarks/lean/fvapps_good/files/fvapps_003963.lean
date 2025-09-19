-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def game (n: Nat) : List Nat := sorry

theorem game_result_list_length {n: Nat} :
  let result := game n
  List.length result = 1 ∨ List.length result = 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem game_zero_case :
  game 0 = [0] := sorry

theorem game_even_case {n: Nat} :
  n % 2 = 0 →
  game n = [n * n / 2] := sorry 

theorem game_odd_case {n: Nat} :
  n % 2 = 1 →
  game n = [n * n, 2] := sorry

theorem game_fraction_in_range {n: Nat} :
  let result := game n
  let fraction := if List.length result = 2 
                  then result[0]! / result[1]!
                  else result[0]!
  0 ≤ fraction ∧ fraction ≤ n * n := sorry
-- </vc-theorems>