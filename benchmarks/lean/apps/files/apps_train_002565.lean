-- <vc-helpers>
-- </vc-helpers>

def sumArrays (arr1 arr2 : List Int) : List Int := sorry

-- Empty arrays sum to empty array

theorem sum_empty : sumArrays [] [] = [] := sorry

-- Empty array is neutral element

theorem sum_empty_neutral (arr : List Int) : 
  sumArrays arr [] = arr ∧ sumArrays [] arr = arr := sorry

-- Sum of arrays equals sum of their numerical values

theorem sum_equals_numerical_sum (arr1 arr2 : List Int) :
  let toNum (arr : List Int) := if arr = [] then (0 : Int) else
    let digits := arr.tail.map (fun x => (x.toNat : Int))
    let num := digits.foldl (fun acc d => acc * 10 + d) (0 : Int)
    if arr.head! < 0 then -num else num
  toNum (sumArrays arr1 arr2) = toNum arr1 + toNum arr2 := sorry

/-
info: [3, 4, 1]
-/
-- #guard_msgs in
-- #eval sum_arrays #[3, 2, 9] #[1, 2]

/-
info: [-3, 9, 6, 2]
-/
-- #guard_msgs in
-- #eval sum_arrays #[3, 2, 6, 6] #[-7, 2, 2, 8]

/-
info: []
-/
-- #guard_msgs in
-- #eval sum_arrays #[] #[]

-- Apps difficulty: introductory
-- Assurance level: unguarded