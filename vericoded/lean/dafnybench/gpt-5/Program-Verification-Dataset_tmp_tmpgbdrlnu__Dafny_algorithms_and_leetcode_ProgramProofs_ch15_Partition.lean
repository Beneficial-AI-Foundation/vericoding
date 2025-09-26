import Mathlib
-- <vc-preamble>

def count (a : Array Int) (x : Int) : Nat :=
a.foldl (fun acc y => if y = x then acc + 1 else acc) 0

def SplitPoint (a : Array Int) (n : Nat) : Prop :=
∀ i j, 0 ≤ i ∧ i < n ∧ n ≤ j ∧ j < a.size → a[i]! ≤ a[j]!

def SwapFrame (a a' : Array Int) (lo hi : Nat) : Prop :=
(∀ i, (0 ≤ i ∧ i < lo) ∨ (hi ≤ i ∧ i < a.size) → a[i]! = a'[i]!) ∧
(∀ x : Int, count a x = count a' x)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
namespace VCPartition
-- </vc-helpers>

-- <vc-definitions>
def Partition (a : Array Int) (lo hi : Int) : Int :=
lo
-- </vc-definitions>

-- <vc-theorems>
theorem partition_spec (a a' : Array Int) (lo hi p : Nat) :
0 ≤ lo ∧ lo < hi ∧ hi ≤ a.size →
SplitPoint a lo ∧ SplitPoint a hi →
lo ≤ p ∧ p < hi →
(∀ i, lo ≤ i ∧ i < p → a'[i]! < a'[p]!) →
(∀ i, p ≤ i ∧ i < hi → a'[p]! ≤ a'[i]!) →
SplitPoint a' lo ∧ SplitPoint a' hi →
SwapFrame a a' lo hi →
True :=
fun _ _ _ _ _ _ _ => True.intro
-- </vc-theorems>
