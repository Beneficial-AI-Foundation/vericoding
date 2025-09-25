-- <vc-preamble>
def fib (n : Nat) : Nat :=
if n = 0 then 0
else if n = 1 then 1
else fib (n - 1) + fib (n - 2)

def sorted (a : Array Int) : Prop :=
∀ n m, 0 ≤ n → n < m → m < a.size → a[n]! ≤ a[m]!

partial def count (a : Array Bool) : Nat :=
if a.size = 0 then 0
else (if a[0]! then 1 else 0) + count (a.extract 1 a.size)

structure Node where
next : Array Node
deriving Inhabited

def closed (graph : List Node) : Prop :=
∀ i, i ∈ graph → ∀ k, 0 ≤ k ∧ k < i.next.size → i.next[k]! ∈ graph ∧ i.next[k]! ≠ i
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def update (s : Array Int) (i : Int) (v : Int) : Array Int :=
sorry

def path (p : Array Node) (graph : List Node) : Bool :=
sorry

def pathSpecific (p : Array Node) (start end_ : Node) (graph : List Node) : Bool :=
sorry

def FindZero (a : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem update_spec (s : Array Int) (i : Nat) (v : Int) :
0 ≤ i ∧ i < s.size →
update s i v = s.set! i v :=
sorry

theorem FindZero_spec (a : Array Int) (index : Int) :
(∀ i, 0 ≤ i → i < a.size → 0 ≤ a[i]!) →
(∀ i, 0 < i → i < a.size → a[i-1]! - 1 ≤ a[i]!) →
((index < 0 → ∀ i, 0 ≤ i → i < a.size → a[i]! ≠ 0) ∧
(0 ≤ index → index < a.size ∧ a[index.toNat]! = 0)) :=
sorry
-- </vc-theorems>