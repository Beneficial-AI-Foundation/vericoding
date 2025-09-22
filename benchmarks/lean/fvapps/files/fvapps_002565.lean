-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumArrays (arr1 arr2 : List Int) : List Int := sorry

-- Empty arrays sum to empty array
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>