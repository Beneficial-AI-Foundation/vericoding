-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digitsList (n : Nat) : List Nat :=
sorry

def sumList (xs : List Nat) : Nat :=
sorry

def check (n : Nat) (maxSum : Nat) : Bool :=
sorry

def max_sumDig (nmax : Nat) (maxSum : Nat) : Nat × Nat × Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_type (n : Nat) (maxSum : Nat) : check n maxSum = true ∨ check n maxSum = false :=
sorry

theorem check_max_sum (n : Nat) (maxSum : Nat)
    (h1 : n ≥ 1000) (h2 : n < 10000) (h3 : maxSum ≤ 36) :
  check n maxSum = true ↔
    ∀ i, i + 4 ≤ (digitsList n).length →
      sumList (List.drop i (List.take (i+4) (digitsList n))) ≤ maxSum :=
sorry

theorem max_sumDig_constraints (nmax maxSum : Nat)
    (h1 : nmax ≥ 2000) (h2 : nmax < 10000) (h3 : maxSum ≥ 3) (h4 : maxSum ≤ 36) :
  let (count, closest, sum) := max_sumDig nmax maxSum
  count ≥ 0 ∧
  closest ≥ 1000 ∧
  closest ≤ nmax ∧
  check closest maxSum = true ∧
  sum ≥ 0 :=
sorry
-- </vc-theorems>