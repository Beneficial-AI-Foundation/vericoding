-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_max_product (arr : List Int) (k : Nat) : Option (Int × Int) := sorry

theorem find_min_max_product_result_ordered 
    {arr : List Int} {k : Nat} 
    (h : k ≤ arr.length) :
    (find_min_max_product arr k).all (fun (min_max : Int × Int) => min_max.1 ≤ min_max.2) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_max_product_bounds
    {arr : List Int} {k : Nat}
    (h : k ≤ arr.length)
    (i : Nat)
    (hi : i + k ≤ arr.length) :
    (find_min_max_product arr k).all (fun (min_max : Int × Int) =>
      let prod := (List.range k).foldl (fun acc j => acc * arr[i + j]!) 1
      min_max.1 ≤ prod ∧ prod ≤ min_max.2) := sorry

theorem find_min_max_product_empty_list
    {arr : List Int} {k : Nat}
    (hempty : arr = []) 
    (hk : k > 0) :
    find_min_max_product arr k = none := sorry

theorem find_min_max_product_k_too_large
    {arr : List Int} {k : Nat}
    (h : k > arr.length) :
    find_min_max_product arr k = none := sorry
-- </vc-theorems>