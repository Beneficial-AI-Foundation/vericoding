-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def evenNumbers (arr : List Int) (n : Nat) : List Int := sorry

theorem evenNumbers_len_leq_min (arr : List Int) (n : Nat) : 
  let result := evenNumbers arr n
  let numEven := (arr.filter (fun x => x % 2 = 0)).length
  result.length ≤ min n numEven := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem evenNumbers_all_even (arr : List Int) (n : Nat) :
  let result := evenNumbers arr n
  ∀ x ∈ result, x % 2 = 0 := sorry

theorem evenNumbers_subset (arr : List Int) (n : Nat) :
  let result := evenNumbers arr n
  ∀ x ∈ result, x ∈ arr := sorry

theorem evenNumbers_preserves_order (arr : List Int) (n : Nat) :
  let result := evenNumbers arr n
  let evenNums := arr.filter (fun x => x % 2 = 0)
  result = evenNums.drop (evenNums.length - result.length) := sorry

theorem evenNumbers_large_n (arr : List Int) :
  let n := arr.length + 1
  let result := evenNumbers arr n
  result = arr.filter (fun x => x % 2 = 0) := sorry

/-
info: [4, 6, 8]
-/
-- #guard_msgs in
-- #eval even_numbers [1, 2, 3, 4, 5, 6, 7, 8, 9] 3

/-
info: [-8, 26]
-/
-- #guard_msgs in
-- #eval even_numbers [-22, 5, 3, 11, 26, -6, -7, -8, -9, -8, 26] 2

/-
info: [6]
-/
-- #guard_msgs in
-- #eval even_numbers [6, -25, 3, 7, 5, 5, 7, -3, 23] 1
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded