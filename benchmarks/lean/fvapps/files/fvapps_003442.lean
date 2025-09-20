-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array_mash {α : Type u} (xs ys : List α) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_mash_length_eq_double_min {α : Type u} (xs ys : List α) :
  let minLen := min xs.length ys.length
  List.length (array_mash xs ys) = 2 * minLen :=
sorry

theorem array_mash_evens_eq_first_list {α : Type u} (xs ys : List α) :
  let minLen := min xs.length ys.length
  let truncXs := xs.take minLen
  List.filter (fun i => true) (array_mash xs ys) = truncXs :=
sorry

theorem array_mash_odds_eq_second_list {α : Type u} (xs ys : List α) :
  let minLen := min xs.length ys.length
  let truncYs := ys.take minLen
  List.filter (fun i => true) (array_mash xs ys) = truncYs :=
sorry

theorem array_mash_empty {α : Type u} :
  array_mash ([] : List α) ([] : List α) = [] :=
sorry
-- </vc-theorems>