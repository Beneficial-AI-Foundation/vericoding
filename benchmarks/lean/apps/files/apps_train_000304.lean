/-
Return the length of the shortest, non-empty, contiguous subarray of A with sum at least K.
If there is no non-empty subarray with sum at least K, return -1.

Example 1:
Input: A = [1], K = 1
Output: 1

Example 2:
Input: A = [1,2], K = 4
Output: -1

Example 3:
Input: A = [2,-1,2], K = 3
Output: 3

Note:

1 <= A.length <= 50000
-10 ^ 5 <= A[i] <= 10 ^ 5
1 <= K <= 10 ^ 9
-/

def shortestSubarray (arr : List Int) (k : Int) : Int :=
  sorry

def sumList (l : List Int) : Int :=
  l.foldl (· + ·) 0

-- <vc-helpers>
-- </vc-helpers>

def toNat (i : Int) : Nat :=
  if i ≤ 0 then 0 else i.natAbs

theorem impossible_cases (k : Int) : 
  shortestSubarray [] k = -1 ∧ 
  shortestSubarray [0] k = -1 ∧ 
  shortestSubarray [0,0] k = -1 :=
sorry

theorem positive_only (arr : List Int) (k : Int) (h1 : ∀ x ∈ arr, 0 < x) (h2 : 0 < k) :
  let result := shortestSubarray arr k
  if result = -1 then
    ∀ start len : Nat, start + len ≤ arr.length → 
      sumList ((arr.take (start + len)).drop start) < k
  else
    (∃ start : Nat, start + (toNat result) ≤ arr.length ∧ 
      sumList ((arr.take (start + (toNat result))).drop start) ≥ k) ∧
    (∀ len : Nat, len < (toNat result) → ∀ start : Nat, start + len ≤ arr.length →
      sumList ((arr.take (start + len)).drop start) < k) :=
sorry

theorem result_bounds (arr : List Int) (k : Int) (h1 : 0 < k) (h2 : ¬arr.isEmpty) :
  let result := shortestSubarray arr k
  if result = -1 then True
  else 1 ≤ result ∧ result ≤ arr.length :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval shortestSubarray [1] 1

/-
info: -1
-/
-- #guard_msgs in
-- #eval shortestSubarray [1, 2] 4

/-
info: 3
-/
-- #guard_msgs in
-- #eval shortestSubarray [2, -1, 2] 3

-- Apps difficulty: interview
-- Assurance level: unguarded