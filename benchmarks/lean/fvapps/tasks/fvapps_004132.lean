-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nth_smallest (arr : List Int) (pos : Nat) : Int := sorry

theorem last_smallest_is_max (arr : List Int) (h : arr.length > 0) :
  ∀ x ∈ arr, x ≤ nth_smallest arr arr.length := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>