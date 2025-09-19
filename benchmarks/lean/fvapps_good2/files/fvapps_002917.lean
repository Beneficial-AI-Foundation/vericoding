-- <vc-preamble>
def listSum (lst: List Int) : Int :=
  lst.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listToSet (lst: List Int) : List Int := sorry

def unique_sum (lst: List Int) : Option Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unique_sum_properties (lst : List Int) :
  match lst with
  | [] => unique_sum lst = none
  | _  => unique_sum lst = some (listSum (listToSet lst))
  :=
sorry

theorem unique_sum_nonempty {lst : List Int} (h : lst ≠ []) :
  ∃ n : Int, unique_sum lst = some n ∧ n = listSum (listToSet lst) :=
sorry

theorem unique_sum_duplicates {lst : List Int} (h : lst ≠ [])
  (h2 : ∀ x ∈ lst, x ≠ 0) :
  unique_sum (lst ++ lst) = unique_sum lst :=
sorry
-- </vc-theorems>