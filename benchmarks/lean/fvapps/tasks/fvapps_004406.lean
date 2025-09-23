-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_product (lst : List Int) (n : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_product_single_equals_maximum {lst : List Int} 
  (h : lst.length > 0) :
  ∃ m ∈ lst, (max_product lst 1 = m ∧ ∀ x ∈ lst, x ≤ m) :=
  sorry

theorem max_product_full_list {lst : List Int}
  (h : lst.length > 0) :
  max_product lst lst.length = List.foldl (· * ·) 1 lst :=
  sorry

theorem max_product_singleton_positive :
  max_product [1] 1 = 1 :=
  sorry

theorem max_product_singleton_negative :
  max_product [-1] 1 = -1 :=
  sorry

theorem max_product_singleton_zero :
  max_product [0] 1 = 0 :=
  sorry
-- </vc-theorems>