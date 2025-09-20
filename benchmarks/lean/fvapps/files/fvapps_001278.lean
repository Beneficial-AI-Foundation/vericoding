-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_gcd (n k : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_gcd_divides_n {n k : Int} (hn : n > 0) (hk : k > 0)
    (h : (k * (k + 1)) / 2 ≤ n) (hres : find_max_gcd n k ≠ -1) :
  n % (find_max_gcd n k) = 0 :=
  sorry

theorem find_max_gcd_positive {n k : Int} (hn : n > 0) (hk : k > 0) 
    (h : (k * (k + 1)) / 2 ≤ n) (hres : find_max_gcd n k ≠ -1) :
  find_max_gcd n k > 0 :=
  sorry

theorem find_max_gcd_invalid_n {n k : Int} (hn : n ≤ 0) (hk : k > 0) :
  find_max_gcd n k = -1 :=
  sorry

theorem find_max_gcd_dist_condition {n k : Int} (hn : n > 0) (hk : k > 0) 
    (hres : find_max_gcd n k ≠ -1) :
  (k * (k + 1)) / 2 ≤ n :=
  sorry
-- </vc-theorems>