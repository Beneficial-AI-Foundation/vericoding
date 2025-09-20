-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n: Nat) : Nat :=
sorry

def numSquarefulPerms (A: List Nat) : Nat :=
sorry

def factorial (n: Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def isPerfectSquare (n: Nat) : Bool :=
  match n with
  | 0 => true
  | n + 1 =>
    let sq := sqrt n
    sq * sq = n

theorem output_bounds
  (A: List Nat)
  (h1: ∀ x ∈ A, 1 ≤ x ∧ x ≤ 100) :
  let result := numSquarefulPerms A
  0 ≤ result ∧ result ≤ factorial A.length :=
sorry

theorem valid_permutations
  (A: List Nat)
  (h1: A.length ≥ 2)
  (h2: ∀ x ∈ A, 1 ≤ x ∧ x ≤ 100)
  (h3: numSquarefulPerms A > 0) :
  ∃ i, i < A.length - 1 ∧ isPerfectSquare (A[i]! + A[i+1]!) :=
sorry

theorem identical_elements
  (A: List Nat)
  (h1: A.length > 0)
  (h2: ∀ x ∈ A, 1 ≤ x ∧ x ≤ 100)
  (x: Nat)
  (h3: x = A[0]!) :
  numSquarefulPerms (List.replicate A.length x) = 0 ∨
  numSquarefulPerms (List.replicate A.length x) = 1 :=
sorry

theorem sorting_invariance
  (A: List Nat)
  (h1: A.length > 0)
  (h2: ∀ x ∈ A, 1 ≤ x ∧ x ≤ 100) :
  numSquarefulPerms A = numSquarefulPerms (List.reverse A) :=
sorry
-- </vc-theorems>