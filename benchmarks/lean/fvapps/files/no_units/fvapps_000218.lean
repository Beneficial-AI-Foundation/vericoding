-- <vc-preamble>
def List.isSorted (xs : List Nat) : Bool :=
  match xs with
  | [] => true
  | [_] => true
  | x :: y :: xs => (x < y) && isSorted (y::xs)

def listGet (xs : List Nat) (i : Nat) : Option Nat :=
  xs.get? i

def isFibonacciSeq (seq : List Nat) : Bool :=
  if seq.length ≤ 2 then true
  else
    let rec checkFib (i : Nat) (fuel : Nat) : Bool :=
      if fuel = 0 then false
      else if i ≥ seq.length then true
      else if i < 2 then checkFib (i+1) (fuel-1)
      else match listGet seq i, listGet seq (i-1), listGet seq (i-2) with
        | some x, some y, some z => x == y + z && checkFib (i+1) (fuel-1)
        | _, _, _ => false
    checkFib 0 seq.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lenLongestFibSubseq (A : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounds {A : List Nat} : 
  let result := lenLongestFibSubseq A
  result = 0 ∨ (result ≥ 3 ∧ result ≤ A.length) :=
  sorry

theorem input_strictly_increasing {A : List Nat} :
  A.isSorted = true → ∀ i, i > 0 → i < A.length → 
  match listGet A i, listGet A (i-1) with
  | some x, some y => x > y
  | _, _ => true :=
  sorry

theorem fibonacci_subsequence_exists {A : List Nat} :
  let result := lenLongestFibSubseq A
  A.isSorted = true →
  result ≥ 3 →
  ∃ subseq : List Nat,
    subseq.length = result ∧ 
    isFibonacciSeq subseq = true ∧
    ∀ x, x ∈ subseq → x ∈ A :=
  sorry
-- </vc-theorems>