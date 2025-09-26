-- <vc-preamble>
def List.sum (xs : List Int) : Int :=
match xs with
| [] => 0
| h :: t => h + List.sum t

def max_list (xs : List Int) : Int :=
match xs with
| [] => 0
| [x] => x
| x::xs => max x (max_list xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_coins (n k : Nat) (arr : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_max_coins_k_exceeds_n {n k : Nat} {arr : List Int} 
  (h1 : arr.length = n)
  (h2 : k > n) :
  find_max_coins n k arr = 0 :=
sorry

theorem find_max_coins_k_equals_n {n k : Nat} {arr : List Int}
  (h1 : arr.length = n)
  (h2 : k = n)
  (h3 : n > 0) :
  find_max_coins n k arr = List.sum arr :=
sorry

theorem find_max_coins_sliding_window {n k : Nat} {arr : List Int}
  (h1 : arr.length = n)
  (h2 : k > 0)
  (h3 : k ≤ n) :
  find_max_coins n k arr = max_list ((List.range n).map (fun i => 
    List.sum (List.take k (List.drop i (arr ++ arr)))
  )) :=
sorry

theorem find_max_coins_monotonic {n k : Nat} {arr : List Int}
  (h1 : arr.length = n)
  (h2 : k ≤ n)
  (h3 : k > 1)
  (h4 : ∀x ∈ arr, x ≥ 0) :
  find_max_coins n k arr ≥ find_max_coins n (k-1) arr :=
sorry

/-
info: 24
-/
-- #guard_msgs in
-- #eval find_max_coins 5 3 [8, 6, 9, 4, 10]

/-
info: 18
-/
-- #guard_msgs in
-- #eval find_max_coins 6 4 [1, 2, 3, 4, 5, 6]

/-
info: 90
-/
-- #guard_msgs in
-- #eval find_max_coins 5 2 [10, 20, 30, 40, 50]
-- </vc-theorems>