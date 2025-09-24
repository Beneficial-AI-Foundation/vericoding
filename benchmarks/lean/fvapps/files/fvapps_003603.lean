-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def orArrays (arr1 : List Nat) (arr2 : List Nat) (default : Nat := 0) : List Nat := sorry

theorem or_arrays_length (arr1 arr2 : List Nat) (default : Nat) :
  (orArrays arr1 arr2 default).length = max arr1.length arr2.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem or_arrays_elemwise (arr1 arr2 : List Nat) (default : Nat) (i : Nat) (h : i < (orArrays arr1 arr2 default).length) :
  (orArrays arr1 arr2 default)[i]'h = 
    (if h1 : i < arr1.length then arr1[i]'h1 else default) ||| 
    (if h2 : i < arr2.length then arr2[i]'h2 else default) := sorry

theorem or_arrays_identity_right (arr : List Nat) : 
  orArrays arr (List.replicate arr.length 0) 0 = arr := sorry

theorem or_arrays_identity_left (arr : List Nat) :
  orArrays (List.replicate arr.length 0) arr 0 = arr := sorry

theorem or_arrays_commutative (arr1 arr2 : List Nat) (default : Nat) :
  orArrays arr1 arr2 default = orArrays arr2 arr1 default := sorry

theorem or_arrays_empty :
  orArrays [] [] 0 = [] := sorry

theorem or_arrays_empty_right (arr : List Nat) :
  orArrays arr [] 0 = arr := sorry

theorem or_arrays_empty_left (arr : List Nat) :
  orArrays [] arr 0 = arr := sorry
-- </vc-theorems>