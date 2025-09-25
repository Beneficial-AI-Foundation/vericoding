-- <vc-preamble>
def Sorted (q : Array Int) : Prop :=
∀ i j, 0 ≤ i → i ≤ j → j < q.size → q[i]! ≤ q[j]!

def Inv_ (a : Array Int) (a1 : Array Int) (a2 : Array Int) (i : Nat) (mid : Nat) : Prop :=
i ≤ a1.size ∧ i ≤ a2.size ∧ i + mid ≤ a.size ∧
(a1.extract 0 i = a.extract 0 i) ∧
(a2.extract 0 i = a.extract mid (i + mid))

def InvSorted (b : Array Int) (c : Array Int) (d : Array Int) (i : Nat) (j : Nat) : Prop :=
i ≤ c.size ∧ j ≤ d.size ∧ i + j ≤ b.size ∧
((i + j > 0 ∧ i < c.size) →  (b[j + i - 1]! ≤ c[i]!)) ∧
((i + j > 0 ∧ j < d.size) → (b[j + i - 1]! ≤ d[j]!)) ∧
Sorted (b.extract 0 (i + j))

def InvSubSet (b : Array Int) (c : Array Int) (d : Array Int) (i : Nat) (j : Nat) : Prop :=
i ≤ c.size ∧ j ≤ d.size ∧ i + j ≤ b.size ∧
(b.extract 0 (i + j)) =  (c.extract 0 i).append (d.extract 0 j)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MergeLoop (b c d : Array Int) (i0 j0 : Nat) : (Nat × Nat) :=
sorry

def Merge (b c d : Array Int) : Unit :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem MergeLoop_spec (b c d : Array Int) (i0 j0 : Nat) :
b ≠ c → b ≠ d → b.size = c.size + d.size →
Sorted c → Sorted d →
i0 ≤ c.size → j0 ≤ d.size → i0 + j0 ≤ b.size →
InvSubSet b c d i0 j0 →
InvSorted b c d i0 j0 →
i0 + j0 < b.size →
let (i, j) := MergeLoop b c d i0 j0
i ≤ c.size ∧ j ≤ d.size ∧ i + j ≤ b.size ∧
InvSubSet b c d i j ∧
InvSorted b c d i j ∧
(0 ≤ c.size - i ∧ c.size - i < c.size - i0 ∨
(c.size - i = c.size - i0 ∧ 0 ≤ d.size - j ∧ d.size - j < d.size - j0)) :=
sorry

theorem Merge_spec (b c d : Array Int) :
b ≠ c → b ≠ d → b.size = c.size + d.size →
Sorted c → Sorted d →
Sorted b ∧  (b.extract 0 (i + j)) =  (c.extract 0 i).append (d.extract 0 j) :=
sorry
-- </vc-theorems>