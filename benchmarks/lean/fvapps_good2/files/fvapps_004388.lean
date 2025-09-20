-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pac_man (size : Nat) (pacman : List Nat) (enemies : List (List Nat)) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pac_man_result_bounds
  (size : Nat)
  (px py : Nat)
  (enemies : List (List Nat))
  (h : size ≥ 2) :
  let normalizedPx := px % size
  let normalizedPy := py % size
  let result := pac_man size [normalizedPx, normalizedPy] enemies
  result ≥ -1 ∧ result ≤ size * size - 1 :=
sorry

theorem pac_man_specific_cases :

  pac_man 3 [0, 0] [] = 8 ∧

  pac_man 4 [3, 0] [[1, 2]] = 3 ∧

  pac_man 2 [0, 0] [[0, 1], [1, 0], [1, 1]] = 0 :=
sorry
-- </vc-theorems>