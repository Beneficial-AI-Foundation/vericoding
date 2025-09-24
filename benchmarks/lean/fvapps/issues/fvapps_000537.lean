-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum xs

def List.sort (l : List Nat) : List Nat :=
sorry

def abs (n : Nat) : Nat :=
  if n ≥ 0 then n else 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_max_weight_difference (N : Nat) (K : Nat) (weights : List Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_invariant {N K : Nat} {weights : List Nat} :
  weights.length = N →
  K ≤ N →
  get_max_weight_difference N K weights = get_max_weight_difference N K weights.reverse :=
sorry

theorem complement_invariant {N K : Nat} {weights : List Nat} :
  weights.length = N →
  K ≤ N →
  get_max_weight_difference N K weights = get_max_weight_difference N (N-K) weights :=
sorry 

theorem sort_preserves_sum {weights : List Nat} :
  List.sum weights = List.sum (List.sort weights) :=
sorry

theorem identical_weights_property {N K w : Nat} {weights : List Nat} :
  weights = List.replicate N w →
  K ≤ N →
  get_max_weight_difference N K weights = if 2*K ≥ N 
    then Int.ofNat ((2*K - N)*w)
    else Int.ofNat ((N - 2*K)*w) :=
sorry

/-
info: 17
-/
-- #guard_msgs in
-- #eval get_max_weight_difference 5 2 [8, 4, 5, 2, 10]

/-
info: 2
-/
-- #guard_msgs in
-- #eval get_max_weight_difference 8 3 [1, 1, 1, 1, 1, 1, 1, 1]

/-
info: 13
-/
-- #guard_msgs in
-- #eval get_max_weight_difference 4 1 [5, 2, 7, 3]
-- </vc-theorems>