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

def Find (a : Array Int) (key : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Find_spec (a : Array Int) (key : Int) (index : Int) :
(0 ≤ index → index < a.size ∧ a[index.toNat]! = key) ∧
(index < 0 → ∀ k, 0 ≤ k ∧ k < a.size → a[k]! ≠ key) :=
sorry
-- </vc-theorems>