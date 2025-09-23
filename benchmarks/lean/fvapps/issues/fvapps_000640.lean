-- <vc-preamble>
def List.sum : List Int → Int 
  | [] => 0
  | x::xs => x + sum xs 

def find_subarray_length (n : Nat) (k : Nat) (s : Int) (arr : List Int) : Int :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Int.abs (i : Int) : Int :=
  if i < 0 then -i else i
-- </vc-definitions>

-- <vc-theorems>
theorem subarray_length_n_leq_k {n k : Nat} {s : Int} {arr : List Int} 
  (h : n ≤ k) : 
  find_subarray_length n k s arr = -1 := 
sorry

theorem subarray_length_valid {n k : Nat} {s : Int} {arr : List Int}
  (h : find_subarray_length n k s arr ≠ -1) :
  find_subarray_length n k s arr > k := 
sorry

theorem exists_subarray_sum {n k : Nat} {s : Int} {arr : List Int}
  (h : find_subarray_length n k s arr ≠ -1) :
  ∃ i : Nat, i + find_subarray_length n k s arr ≤ n ∧ 
    (List.sum (List.take (find_subarray_length n k s arr).toNat (List.drop i arr)) > s) :=
sorry

theorem no_smaller_length {n k : Nat} {s : Int} {arr : List Int} 
  (h : find_subarray_length n k s arr ≠ -1)
  (len : Nat)
  (h1 : k < len)
  (h2 : len < (find_subarray_length n k s arr).toNat) :
  ∀ i : Nat, i + len ≤ n → 
    List.sum (List.take len (List.drop i arr)) ≤ s :=
sorry

theorem positive_arr_negative_s {n k : Nat} {s : Int} {arr : List Int}
  (h1 : ∀ x ∈ arr, 0 ≤ x)
  (h2 : s < 0)
  (h3 : n > k) :
  find_subarray_length n k s arr = k + 1 :=
sorry

theorem sum_too_high {n k : Nat} {s : Int} {arr : List Int}
  (h : s > List.sum (List.map Int.abs arr)) :
  find_subarray_length n k s arr = -1 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_subarray_length 5 1 5 [1, 2, 3, 4, 5]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_subarray_length 3 2 1 [9, 9, 1]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_subarray_length 4 3 100 [1, 2, 3, 4]
-- </vc-theorems>