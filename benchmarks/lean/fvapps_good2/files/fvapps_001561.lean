-- <vc-preamble>
def list_sum : List Nat → Nat
  | [] => 0
  | (h::t) => h + list_sum t

def list_sorted : List Nat → Bool
  | [] => true
  | [_] => true
  | (a::b::rest) => a ≤ b && list_sorted (b::rest)

def list_all (l : List Nat) (p : Nat → Bool) : Bool :=
  List.all l p

def square (n : Nat) : Nat := n * n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decompose (n : Nat) : Option (List Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decompose_valid (n : Nat) (result : List Nat) :
  decompose n = some result →
  (list_sum (List.map square result) = n * n) ∧
  list_sorted result = true ∧
  list_all result (λ x => x > 0) = true ∧
  list_all result (λ x => x < n) = true :=
sorry

theorem decompose_2_impossible :
  decompose 2 = none :=
sorry

theorem decompose_3_impossible :
  decompose 3 = none :=
sorry
-- </vc-theorems>