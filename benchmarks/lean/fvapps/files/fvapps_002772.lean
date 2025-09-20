-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_multiples (n : Nat) (limit : Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_multiples_empty_when_limit_less {n : Nat} {limit : Nat} 
  (h : limit < n) : find_multiples n limit = [] :=
sorry

theorem find_multiples_all_divisible {n : Nat} {limit : Nat} {x : Nat}
  (h : x ∈ find_multiples n limit) : 
  x % n = 0 :=
sorry

theorem find_multiples_all_within_limit {n : Nat} {limit : Nat} {x : Nat}
  (h : x ∈ find_multiples n limit) :
  x ≤ limit :=
sorry

theorem find_multiples_ordered {n : Nat} {limit : Nat} {i j : Nat}
  (hi : i < (find_multiples n limit).length)
  (hj : j < (find_multiples n limit).length)
  (h : i < j) :
  (find_multiples n limit)[i] < (find_multiples n limit)[j] :=
sorry

theorem find_multiples_first_element {n : Nat} {limit : Nat}
  (h : limit ≥ n) :
  (find_multiples n limit).head? = some n :=
sorry

theorem find_multiples_consecutive_diff {n : Nat} {limit : Nat} {i : Nat}
  (h : i + 1 < (find_multiples n limit).length) :
  (find_multiples n limit)[i+1] - (find_multiples n limit)[i] = n :=
sorry

theorem find_multiples_same_limit {n : Nat} :
  find_multiples n n = [n] :=
sorry
-- </vc-theorems>