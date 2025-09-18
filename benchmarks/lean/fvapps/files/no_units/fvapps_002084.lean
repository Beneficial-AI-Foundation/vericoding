-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_max_banknotes (start g1 g2 : Int) (notes : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_max_banknotes_basic_properties
  (start g1 g2 : Int) (notes : List Int) :
  let result := count_max_banknotes start g1 g2 notes
  result ≥ 0 ∧ 
  result ≤ notes.length ∧
  result = (notes.filter (fun n => g1 < n ∧ n < g2)).length :=
sorry

theorem count_max_banknotes_guard_order 
  (start g1 g2 : Int) (notes : List Int) (h : notes.length > 0) :
  let res1 := count_max_banknotes start g1 g2 notes
  let res2 := count_max_banknotes start g2 g1 notes
  res1 = 0 ∨ res2 = 0 :=
sorry

theorem count_max_banknotes_empty_notes
  (start g1 g2 : Int) :
  count_max_banknotes start g1 g2 [] = 0 :=
sorry

theorem count_max_banknotes_start_irrelevant
  (start g1 g2 : Int) (notes : List Int) :
  count_max_banknotes start g1 g2 notes = 
  count_max_banknotes (start + 1) g1 g2 notes :=
sorry
-- </vc-theorems>