-- <vc-preamble>
def max (a b : Int) : Int :=
if a > b then a else b

def abs (x : Int) : Int :=
if x < 0 then -x else x

def fib (n : Nat) : Nat :=
if n = 0 then 0
else if n = 1 then 1
else fib (n - 1) + fib (n - 2)

def sorted (a : Array Int) : Prop :=
∀ j k, 0 ≤ j → j < k → k < a.size → a[j]! < a[k]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Testing : Unit :=
sorry

def FindMax (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindMax_spec (a : Array Int) (i : Int) :
a.size ≥ 1 →
(0 ≤ i ∧ i < a.size) ∧
(∀ k, 0 ≤ k ∧ k < a.size → a[k]! ≤ a[i.toNat]!) :=
sorry
-- </vc-theorems>