-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: [5, 10, 15, 20, 25]
-/
-- #guard_msgs in
-- #eval find_multiples 5 25

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval find_multiples 1 2

/-
info: [4, 8, 12, 16, 20, 24]
-/
-- #guard_msgs in
-- #eval find_multiples 4 27
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible