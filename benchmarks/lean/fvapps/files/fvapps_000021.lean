-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_smallest_k (n : Nat) (s : List Nat) : Int := sorry

def bxor (a b : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_smallest_k_positive (n : Nat) (s : List Nat) :
  let k := find_smallest_k n s
  k ≠ -1 → k > 0 := sorry

theorem find_smallest_k_bounded (n : Nat) (s : List Nat) :
  let k := find_smallest_k n s
  k ≠ -1 → k ≤ 1024 := sorry

theorem find_smallest_k_permutation_invariant (n : Nat) (s : List Nat) :
  s.length ≥ 2 → 
  find_smallest_k n s = find_smallest_k n s.reverse := sorry
-- </vc-theorems>