-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_even_index (arr : List Int) : Nat :=
  sorry

def sum_list (arr : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_even_index_centered {n : Nat} :
  let arr := List.replicate n 1 ++ [0] ++ List.replicate n 1
  find_even_index arr = n
  :=
sorry

theorem find_even_index_single_element :
  find_even_index [0] = 0 :=
sorry

theorem find_even_index_single_nonzero :
  find_even_index [1] = 0 :=
sorry

theorem find_even_index_all_zeros :
  find_even_index [0, 0, 0] = 0 :=
sorry
-- </vc-theorems>