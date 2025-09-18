-- <vc-preamble>
def listSum (l : List Int) : Int :=
  l.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumEvenNumbers (l : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_even_numbers_sums_evens (l : List Int) :
  sumEvenNumbers l = listSum (l.filter (fun n => n % 2 = 0)) := by
  sorry

theorem sum_even_numbers_is_even (l : List Int) :
  sumEvenNumbers l % 2 = 0 := by
  sorry

theorem sum_even_numbers_idempotent (l : List Int) :
  let result := sumEvenNumbers l
  result ≠ 0 → sumEvenNumbers [result] = result := by
  sorry

theorem sum_even_numbers_empty :
  sumEvenNumbers [] = 0 := by
  sorry
-- </vc-theorems>