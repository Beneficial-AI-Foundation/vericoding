-- <vc-preamble>
def abs (n : Int) : Int := 
  if n < 0 then -n else n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_sequence (n : Nat) (arr : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_sequence_output_sign_flips {n : Nat} {arr : List Int} :
  let result := solve_sequence n arr
  ∀ i, i < result.length → abs (result.get ⟨i, sorry⟩) = abs (arr.get ⟨i, sorry⟩) :=
sorry

theorem solve_sequence_maintains_length {n : Nat} {arr : List Int} :
  (solve_sequence n arr).length = arr.length :=
sorry

theorem solve_sequence_input_preserved {n : Nat} {arr : List Int} :
  solve_sequence n arr = solve_sequence n arr ∧ arr = arr :=
sorry

theorem solve_sequence_case1 :
  solve_sequence 4 [4, 3, 1, 2] = [4, 3, -1, 2] :=
sorry

theorem solve_sequence_case2 :
  solve_sequence 6 [1, 2, 2, 1, 3, 1] = [-1, 2, 2, -1, 3, -1] :=
sorry

theorem solve_sequence_case3 :
  solve_sequence 4 [1, 2, 1, 2] = [1, 2, -1, 2] :=
sorry
-- </vc-theorems>