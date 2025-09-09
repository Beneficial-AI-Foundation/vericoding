def sumEvenNumbers (l : List Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def listSum (l : List Int) : Int :=
  l.foldl (· + ·) 0

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

/-
info: 30
-/
-- #guard_msgs in
-- #eval sum_even_numbers [4, 3, 1, 2, 5, 10, 6, 7, 9, 8]

/-
info: 0
-/
-- #guard_msgs in
-- #eval sum_even_numbers []

/-
info: 14
-/
-- #guard_msgs in
-- #eval sum_even_numbers [-16, -32, 20, 21, 41, 42]

-- Apps difficulty: introductory
-- Assurance level: guarded