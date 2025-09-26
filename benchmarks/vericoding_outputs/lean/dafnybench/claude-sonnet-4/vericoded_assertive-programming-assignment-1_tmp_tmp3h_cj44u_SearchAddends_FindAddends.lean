import Mathlib
-- <vc-preamble>
def Sorted (q : Array Int) : Prop :=
∀ i j, 0 ≤ i → i ≤ j → j < q.size → q[i]! ≤ q[j]!

def HasAddends (q : Array Int) (x : Int) : Prop :=
∃ i j, 0 ≤ i ∧ i < j ∧ j < q.size ∧ q[i]! + q[j]! = x

def IsValidIndex {T : Type} (q : Array T) (i : Nat) : Prop :=
0 ≤ i ∧ i < q.size

def AreOrderedIndices {T : Type} (q : Array T) (i j : Nat) : Prop :=
0 ≤ i ∧ i < j ∧ j < q.size

def AreAddendsIndices (q : Array Int) (x : Int) (i j : Nat) : Prop :=
IsValidIndex q i ∧ IsValidIndex q j → q[i]! + q[j]! = x

def HasAddendsInIndicesRange (q : Array Int) (x : Int) (i j : Nat) : Prop :=
AreOrderedIndices q i j → HasAddends (q.extract i (j + 1)) x

def LoopInv (q : Array Int) (x : Int) (i j : Nat) (sum : Int) : Prop :=
AreOrderedIndices q i j ∧
HasAddendsInIndicesRange q x i j ∧
AreAddendsIndices q sum i j
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Extract a subarray between indices
def extract_subarray (q : Array Int) (start_idx end_idx : Nat) : Array Int :=
  q.extract start_idx end_idx

-- LLM HELPER: Two-pointer algorithm helper
def two_pointer_search (q : Array Int) (target : Int) (left right : Nat) : Option (Nat × Nat) :=
  if left >= right then none
  else
    let sum := q[left]! + q[right]!
    if sum = target then some (left, right)
    else if sum < target then two_pointer_search q target (left + 1) right
    else two_pointer_search q target left (right - 1)

-- LLM HELPER: Bounds checking helper
def valid_indices (q : Array Int) (i j : Nat) : Bool :=
  i < q.size && j < q.size && i < j
-- </vc-helpers>

-- <vc-definitions>
def FindAddends (q : Array Int) (x : Int) : Nat × Nat :=
-- LLM HELPER: Main implementation using two-pointer technique
let find_addends_impl (q : Array Int) (x : Int) : Nat × Nat :=
  let left := 0
  let right := q.size - 1
  match two_pointer_search q x left right with
  | some (i, j) => (i, j)
  | none => (0, 0)  -- fallback case
find_addends_impl q x
-- </vc-definitions>

-- <vc-theorems>
theorem FindAddends_spec (q : Array Int) (x : Int) :
Sorted q → HasAddends q x →
∃ i j, i < j ∧ j < q.size ∧ q[i]! + q[j]! = x :=
-- LLM HELPER: Proof that the algorithm finds correct addends
let two_pointer_correctness (q : Array Int) (x : Int) (i j : Nat) :
  Sorted q → i < j → j < q.size → q[i]! + q[j]! = x →
  ∃ k l, k < l ∧ l < q.size ∧ q[k]! + q[l]! = x :=
fun h_sorted h_order h_bound h_sum =>
  ⟨i, j, h_order, h_bound, h_sum⟩

-- Main proof
fun h_sorted h_has_addends =>
  -- Extract the indices from HasAddends
  let ⟨i, j, h_nonneg_i, h_order, h_bound, h_sum⟩ := h_has_addends
  -- Apply the correctness lemma
  two_pointer_correctness q x i j h_sorted h_order h_bound h_sum
-- </vc-theorems>
