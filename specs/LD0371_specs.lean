-- <vc-preamble>
def SplitPoint (a : Array Int) (n : Nat) : Prop :=
∀ i j, 0 ≤ i ∧ i < n ∧ n ≤ j ∧ j < a.size → a[i]! ≤ a[j]!

def SwapFrame (a a' : Array Int) (lo hi : Nat) : Prop :=
(∀ i, (0 ≤ i ∧ i < lo) ∨ (hi ≤ i ∧ i < a.size) → a[i]! = a'[i]!)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Partition (a : Array Int) (lo hi : Nat) : Int :=
sorry

def QuickSortAux (a : Array Int) (lo hi : Nat) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Partition_spec (a : Array Int) (lo hi : Nat) :
0 ≤ lo ∧ lo < hi ∧ hi ≤ a.size ∧
SplitPoint a lo ∧ SplitPoint a hi →
let p := Partition a lo hi;
let a' := a;
lo ≤ p ∧ p < hi ∧
(∀ i, lo ≤ i ∧ i < p → a'[i]! < a'[p.toNat]!) ∧
(∀ i, p ≤ i ∧ i < hi → a'[p.toNat]! ≤ a'[i.toNat]!) ∧
SplitPoint a' lo ∧ SplitPoint a' hi ∧
SwapFrame a a' lo hi :=
sorry

theorem QuickSortAux_spec (a : Array Int) (lo hi : Nat) :
0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ a.size ∧
SplitPoint a lo ∧ SplitPoint a hi →
let a' := QuickSortAux a lo hi;
(∀ i j, lo ≤ i ∧ i < j ∧ j < hi → a'[i]! ≤ a'[j]!) ∧
SwapFrame a a' lo hi ∧
SplitPoint a' lo ∧ SplitPoint a' hi :=
sorry
-- </vc-theorems>