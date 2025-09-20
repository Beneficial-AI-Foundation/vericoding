-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def first_n_smallest (arr : List Int) (n : Nat) : List Int := sorry

theorem first_n_smallest_length {arr : List Int} {n : Nat} (h : 0 < arr.length)
  (hn : n ≤ arr.length) :
  (first_n_smallest arr n).length = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem first_n_smallest_contains_input {arr : List Int} {n : Nat} (h : 0 < arr.length)
  (hn : n ≤ arr.length) :
  ∀ x ∈ first_n_smallest arr n, x ∈ arr := sorry

theorem first_n_smallest_full_length {arr : List Int} (h : 0 < arr.length) :
  first_n_smallest arr arr.length = arr := sorry
-- </vc-theorems>