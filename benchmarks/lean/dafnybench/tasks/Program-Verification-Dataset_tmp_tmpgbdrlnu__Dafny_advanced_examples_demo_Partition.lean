-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Partition (a : Array Int) : Nat × Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem partition_spec (a : Array Int) (lo hi : Nat) :
let result := Partition a

-- Bounds check

0 ≤ result.1 ∧ result.1 ≤ result.2 ∧ result.2 ≤ a.size ∧

-- Elements before lo are negative

(∀ x, 0 ≤ x ∧ x < result.1 → (a[x]!) < 0) ∧

-- Elements between lo and hi are zero

(∀ x, result.1 ≤ x ∧ x < result.2 → (a[x]!) = 0) ∧

-- Elements after hi are positive

(∀ x, result.2 ≤ x ∧ x < a.size → (a[x]!) > 0) :=
sorry
-- </vc-theorems>