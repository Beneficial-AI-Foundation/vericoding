-- <vc-preamble>
def isSorted (l : List Nat) : Bool :=
  match l with
  | [] => true
  | [_] => true
  | x :: y :: rest => x ≤ y && isSorted (y :: rest)

def listSum (l : List Nat) : Nat :=
  List.foldl (·+·) 0 l
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def primeMaxLengthChain (n : Nat) : List Nat := sorry

def isPrime (n : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_list (n : Nat) (h : n ≥ 1) (h2 : n ≤ 1000) :
  let result := primeMaxLengthChain n
  isSorted result :=
sorry

theorem small_inputs (n : Nat) (h : n ≥ 1) (h2 : n ≤ 4) :
  primeMaxLengthChain n = [] :=
sorry

theorem output_are_primes (n : Nat) (h : n ≥ 5) (h2 : n ≤ 1000) :
  let result := primeMaxLengthChain n
  ∀ x, x ∈ result → isPrime x ∧ x < n :=
sorry

theorem results_are_sums_of_consecutive_primes (n : Nat) (h : n ≥ 5) (h2 : n ≤ 1000) :
  let result := primeMaxLengthChain n
  ∀ x, x ∈ result → ∃ start length,
    let primes := List.filter isPrime (List.range n)
    let slice := (primes.drop start).take length
    length ≥ 2 ∧
    listSum slice = x :=
sorry
-- </vc-theorems>