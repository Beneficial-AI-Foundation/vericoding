-- <vc-preamble>
def Sorted (q : Array Int) : Prop :=
∀ i j, 0 ≤ i → i ≤ j → j < q.size → q[i]! ≤ q[j]!

def Inv_ (a a1 a2 : Array Int) (i mid : Nat) : Prop :=
i ≤ a1.size ∧ i ≤ a2.size ∧ i + mid ≤ a.size ∧
(a1.extract 0 i = a.extract 0 i) ∧
(a2.extract 0 i = a.extract mid (i + mid))

def InvSorted (b c d : Array Int) (i j : Nat) : Prop :=
i ≤ c.size ∧ j ≤ d.size ∧ i + j ≤ b.size ∧
((i + j > 0 ∧ i < c.size) → b[j + i - 1]! ≤ c[i]!) ∧
((i + j > 0 ∧ j < d.size) → b[j + i - 1]! ≤ d[j]!) ∧
Sorted (b.extract 0 (i + j))

def InvSubSet (b c d : Array Int) (i j : Nat) : Prop :=
i ≤ c.size ∧ j ≤ d.size ∧ i + j ≤ b.size ∧
(b.extract 0 (i + j)) =  (c.extract 0 i).append (d.extract 0 j)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Merge (b c d : Array Int) : Array Int :=
sorry

def MergeSort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem merge_spec (b c d : Array Int) :
b ≠ c → b ≠ d → b.size = c.size + d.size →
Sorted c → Sorted d →
Sorted (Merge b c d) ∧
(Merge b c d) = (c.extract 0 i).append (d.extract 0 j) :=
sorry

theorem mergesort_spec (a : Array Int) :
let b := MergeSort a
b.size = a.size ∧ Sorted b ∧ b = a :=
sorry
-- </vc-theorems>