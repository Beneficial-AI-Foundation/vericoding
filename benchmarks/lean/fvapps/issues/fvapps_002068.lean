-- <vc-preamble>
def List.sum : List Nat → Nat
  | [] => 0
  | x::xs => x + sum xs

def List.minimum : List Nat → Nat 
  | [] => 0
  | [x] => x
  | x::xs => Nat.min x (minimum xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_party_weights (n m w : Nat) (weights beauties : List Nat) 
  (friend_pairs : List (Nat × Nat)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem party_weights_result_bounded 
  (n m w : Nat) 
  (weights beauties : List Nat)
  (friend_pairs : List (Nat × Nat))
  (h1 : n ≥ 1) (h2 : n ≤ 20)
  (h3 : m ≥ 0) (h4 : m ≤ 10)
  (h5 : w ≥ 1) (h6 : w ≤ 100)
  (h7 : weights.length = n)
  (h8 : beauties.length = n)
  (h9 : ∀ x ∈ weights, x ≥ 1 ∧ x ≤ 50)
  (h10 : ∀ x ∈ beauties, x ≥ 1 ∧ x ≤ 20)
  (h11 : friend_pairs.length ≤ 10)
  (h12 : ∀ p ∈ friend_pairs, p.1 ≥ 1 ∧ p.1 ≤ 20 ∧ p.2 ≥ 1 ∧ p.2 ≤ 20) :
  let result := solve_party_weights n m w weights beauties friend_pairs
  (result ≥ -1 ∧ result ≤ beauties.sum) :=
  sorry

theorem party_weights_invalid_when_weight_too_small
  (n m w : Nat)
  (weights beauties : List Nat)
  (friend_pairs : List (Nat × Nat))
  (h1 : n ≥ 1) (h2 : n ≤ 20)
  (h3 : m ≥ 0) (h4 : m ≤ 10)
  (h5 : w ≥ 1) (h6 : w ≤ 100)
  (h7 : weights.length = n)
  (h8 : beauties.length = n)
  (h9 : ∀ x ∈ weights, x ≥ 1 ∧ x ≤ 50)
  (h10 : w < weights.minimum) :
  solve_party_weights n m w weights beauties friend_pairs = -1 :=
  sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_party_weights 3 1 5 [3, 2, 5] [2, 4, 2] [(1, 2)]

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_party_weights 4 2 11 [2, 4, 6, 6] [6, 4, 2, 1] [(1, 2), (2, 3)]
-- </vc-theorems>