-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_nb (n : Int) : Int :=
sorry

def sum_cubes (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_nb_small_perfect_cubes (n : Nat) (h : n ≤ 10) :
  find_nb (sum_cubes n) = n :=
sorry

theorem find_nb_invalid_volumes {n : Int} (h : n > 0) :
  find_nb n = -1 ∨ sum_cubes (find_nb n).toNat = n :=
sorry

theorem find_nb_nonpositive {n : Int} (h : n ≤ 0) :
  find_nb n = -1 :=
sorry

theorem find_nb_valid_result (n : Nat) :
  let volume := sum_cubes n
  let result := find_nb volume
  result > 0 ∧ sum_cubes result.toNat = volume :=
sorry

theorem find_nb_produces_volume {n : Int} (h : find_nb n > 0) :
  sum_cubes (find_nb n).toNat = n :=
sorry
-- </vc-theorems>