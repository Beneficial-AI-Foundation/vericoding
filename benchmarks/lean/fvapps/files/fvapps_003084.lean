-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def checkchoose (m n : Int) : Int := sorry

def choose (n k : Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem checkchoose_valid_range (n : Int) (h : n ≥ 1) (h2 : n ≤ 20) : 
  let res := checkchoose (choose n 2) n;
  res ≠ -1 → choose n res = choose n 2 := sorry

theorem checkchoose_bounds (n x : Int) (h : n ≥ 1) (h2 : n ≤ 20) (h3 : x ≥ 0) (h4 : x ≤ 20) :
  let res := checkchoose x n;
  res ≤ n/2 ∨ res = -1 := sorry

theorem checkchoose_impossible_m (m n : Int) (h : m ≤ 0) (h2 : n ≥ 1) (h3 : n ≤ 20) :
  checkchoose m n = -1 := sorry
-- </vc-theorems>