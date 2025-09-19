-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def prev_perm_opt1 (arr : List Int) : List Int :=
sorry

def list_sortFn : List Int → List Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prev_perm_length_preserved {arr : List Int} (h : arr ≠ []) :
  (prev_perm_opt1 arr).length = arr.length :=
sorry

theorem prev_perm_same_elements {arr : List Int} (h : arr ≠ []) :
  list_sortFn (prev_perm_opt1 arr) = list_sortFn arr :=
sorry

theorem prev_perm_sorted_unchanged {arr : List Int} (h : arr ≠ []) :
  arr = list_sortFn arr → prev_perm_opt1 arr = arr :=
sorry

theorem prev_perm_lexicographically_smaller {arr : List Int} (h : arr ≠ []) :
  prev_perm_opt1 arr ≤ arr :=
sorry

theorem prev_perm_idempotent {arr : List Int} (h : arr ≠ []) :
  prev_perm_opt1 (prev_perm_opt1 arr) ≤ prev_perm_opt1 arr :=
sorry

theorem prev_perm_singleton_unchanged {arr : List Int} (h : arr.length = 1) :
  prev_perm_opt1 arr = arr :=
sorry
-- </vc-theorems>