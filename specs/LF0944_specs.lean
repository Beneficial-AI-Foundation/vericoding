-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_diff (N : Nat) (K : Nat) (arr : List Int) : Int :=
sorry

def list_max (arr : List Int) : Int :=
sorry

def list_min (arr : List Int) : Int :=
sorry

def list_sort (arr : List Int) : List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_diff_non_negative (N : Nat) (K : Nat) (arr : List Int)
    (h : arr.length > 0) :
  find_max_diff N K arr ≥ 0 :=
sorry

theorem find_max_diff_reverse_invariant (N : Nat) (K : Nat) (arr : List Int)
    (h : arr.length > 0) :
  find_max_diff N K arr = find_max_diff N K arr.reverse :=
sorry

theorem find_max_diff_single_element (N : Nat) (K : Nat) (arr : List Int)
    (h : arr.length = 1) :
  find_max_diff N K arr = 2 * K :=
sorry
-- </vc-theorems>