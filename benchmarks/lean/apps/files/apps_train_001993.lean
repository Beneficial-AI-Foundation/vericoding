/-
Levko loves array a_1, a_2, ... , a_{n}, consisting of integers, very much. That is why Levko is playing with array a, performing all sorts of operations with it. Each operation Levko performs is of one of two types:

  Increase all elements from l_{i} to r_{i} by d_{i}. In other words, perform assignments a_{j} = a_{j} + d_{i} for all j that meet the inequation l_{i} ≤ j ≤ r_{i}.  Find the maximum of elements from l_{i} to r_{i}. That is, calculate the value $m_{i} = \operatorname{max}_{j = l_{i}}^{r_{i}} a_{j}$. 

Sadly, Levko has recently lost his array. Fortunately, Levko has records of all operations he has performed on array a. Help Levko, given the operation records, find at least one suitable array. The results of all operations for the given array must coincide with the record results. Levko clearly remembers that all numbers in his array didn't exceed 10^9 in their absolute value, so he asks you to find such an array.

-----Input-----

The first line contains two integers n and m (1 ≤ n, m ≤ 5000) — the size of the array and the number of operations in Levko's records, correspondingly.

Next m lines describe the operations, the i-th line describes the i-th operation. The first integer in the i-th line is integer t_{i} (1 ≤ t_{i} ≤ 2) that describes the operation type. If t_{i} = 1, then it is followed by three integers l_{i}, r_{i} and d_{i} (1 ≤ l_{i} ≤ r_{i} ≤ n,  - 10^4 ≤ d_{i} ≤ 10^4) — the description of the operation of the first type. If t_{i} = 2, then it is followed by three integers l_{i}, r_{i} and m_{i} (1 ≤ l_{i} ≤ r_{i} ≤ n,  - 5·10^7 ≤ m_{i} ≤ 5·10^7) — the description of the operation of the second type.

The operations are given in the order Levko performed them on his array.

-----Output-----

In the first line print "YES" (without the quotes), if the solution exists and "NO" (without the quotes) otherwise.

If the solution exists, then on the second line print n integers a_1, a_2, ... , a_{n} (|a_{i}| ≤ 10^9) — the recovered array.

-----Examples-----
Input
4 5
1 2 3 1
2 1 2 8
2 3 4 7
1 1 3 3
2 3 4 8

Output
YES
4 7 4 7
Input
4 5
1 2 3 1
2 1 2 8
2 3 4 7
1 1 3 3
2 3 4 13

Output
NO
-/

-- <vc-helpers>
-- </vc-helpers>

def find_array (n : Nat) (ops : List (Nat × Nat × Nat × Int)) : (String × Option (List Int)) :=
  sorry

theorem find_array_valid_result (n : Nat) (ops : List (Nat × Nat × Nat × Int)) 
  (h : n > 0) :
  let (result, arr) := find_array n ops
  result = "YES" ∨ result = "NO" :=
sorry

theorem find_array_array_length (n : Nat) (ops : List (Nat × Nat × Nat × Int))
  (h : n > 0) :
  let (result, arr) := find_array n ops
  result = "YES" → arr.isSome ∧ arr.get!.length = n :=
sorry

theorem find_array_type1_ops (n : Nat) (ops : List (Nat × Nat × Nat × Int))
  (h : n > 0) :
  let (result, arr) := find_array n ops
  result = "YES" →
  arr.isSome →
  ∀ op ∈ ops, 
    let (t, l, r, x) := op
    t = 1 →
    l ≤ r ∧ r ≤ n →
    ∀ j : Fin arr.get!.length, l - 1 ≤ j.val ∧ j.val ≤ r - 1 →
    arr.get!.get j = arr.get!.get j + x :=
sorry

theorem find_array_type2_ops (n : Nat) (ops : List (Nat × Nat × Nat × Int))
  (h : n > 0) :
  let (result, arr) := find_array n ops
  result = "YES" →
  arr.isSome →
  ∀ op ∈ ops,
    let (t, l, r, x) := op
    t = 2 →
    l ≤ r ∧ r ≤ n →
    (∃ j : Fin arr.get!.length, l - 1 ≤ j.val ∧ j.val ≤ r - 1 ∧ arr.get!.get j = x) ∧
    ∀ j : Fin arr.get!.length, l - 1 ≤ j.val ∧ j.val ≤ r - 1 → arr.get!.get j ≤ x :=
sorry

theorem find_array_single_query (n : Nat) (x : Int)
  (h : n > 0) :
  let ops := [(2, 1, n, x)]
  let (result, arr) := find_array n ops
  result = "YES" ∧ 
  arr.isSome ∧
  ∀ i : Fin arr.get!.length, arr.get!.get i = x :=
sorry

theorem find_array_empty_ops (n : Nat)
  (h : n > 0) :
  let (result, arr) := find_array n []
  result = "YES" ∧
  arr.isSome ∧
  arr.get!.length = n ∧
  ∀ i : Fin arr.get!.length, arr.get!.get i = 10^9 :=
sorry

-- Apps difficulty: competition
-- Assurance level: guarded