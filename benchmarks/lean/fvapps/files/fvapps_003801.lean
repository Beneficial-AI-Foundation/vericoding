-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def finding_k (arr : List Nat) : Int := sorry

def list_max : List Nat → Nat 
  | [] => 0
  | (x::xs) => max x (list_max xs)
-- </vc-definitions>

-- <vc-theorems>
theorem finding_k_valid_k_or_minus_one (arr : List Nat) (h : arr ≠ []) : 
  let k := finding_k arr
  if k ≠ -1 then 
    (k > 0) ∧ 
    (k < list_max arr) ∧
    (∀ x, x ∈ arr → ∃ r, x % k = r)
  else
    ∀ k', k' ∈ List.range (list_max arr) → 
    ∃ x y, x ∈ arr ∧ y ∈ arr ∧ x % k' ≠ y % k'
  := sorry

theorem all_same_numbers_return_minus_one (arr : List Nat) (h : arr ≠ []) :
  (∀ x y, x ∈ arr → y ∈ arr → x = y) → finding_k arr = -1 := sorry
-- </vc-theorems>