-- <vc-preamble>
def contains (v : Int) (a : Array Int) (n : Nat) : Prop :=
∃ j, 0 ≤ j ∧ j < n ∧ a[j]! = v
def upper_bound (v : Int) (a : Array Int) (n : Nat) : Prop :=
∀ j, 0 ≤ j ∧ j < n → a[j]! ≤ v
def is_max (m : Int) (a : Array Int) (n : Nat) : Prop :=
contains m a n ∧ upper_bound m a n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max (a : Array Int) (n : Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_spec (a : Array Int) (n : Nat) :
0 < n ∧ n ≤ a.size →
is_max (max a n) a n :=
sorry
-- </vc-theorems>