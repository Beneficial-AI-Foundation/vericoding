-- <vc-preamble>
def odd (n : Nat) : Bool := n % 2 = 1
def even (n : Nat) : Bool := n % 2 = 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def partitionOddEven (a : Array Nat) : Array Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem partitionOddEven_spec (a : Array Nat) :
let result := partitionOddEven a;

-- Output has same elements as input (using multiset equality)

result.size = a.size

-- No even number before odd number

∧ ¬(∃ i j, 0 ≤ i ∧ i < j ∧ j < result.size ∧ even (result[i]!) ∧ odd (result[j]!)) :=
sorry
-- </vc-theorems>