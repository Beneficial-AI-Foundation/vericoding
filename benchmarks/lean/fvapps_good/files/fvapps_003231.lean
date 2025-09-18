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
-- </vc-theorems>