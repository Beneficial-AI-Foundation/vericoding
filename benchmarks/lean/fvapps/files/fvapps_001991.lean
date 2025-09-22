-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (k : Nat) (arr : List Int) : List Int := sorry

def fft (arr : List Int) (n : Nat) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_empty_array_length {n : Nat} (h : n > 0) (h2 : n ≤ 10) :
  let arr := List.replicate n 0
  List.length (solve n 0 arr) = n + 1 := sorry

theorem solve_empty_array_nonneg {n : Nat} (h : n > 0) (h2 : n ≤ 10) :
  let arr := List.replicate n 0
  ∀ x ∈ (solve n 0 arr), x ≥ 0 := sorry

theorem fft_simple :
  fft [1, 0, 0, 0] 2 = [1, 1, 1, 1] := sorry

theorem solve_example_1 :
  solve 5 3 [1, 2, 3, 4, 5] = [6, 5, 4, 0, 0, 0] := sorry

theorem solve_example_2 :
  solve 2 6 [-5, 9] = [1, 2, 0] := sorry

theorem solve_example_3 :
  solve 6 99 [-1, -1, -1, -1, -1, -1] = [0, 6, 5, 4, 3, 2, 1] := sorry
-- </vc-theorems>