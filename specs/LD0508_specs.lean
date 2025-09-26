-- <vc-preamble>
def merged (a1 : Array Int) (a2 : Array Int) (b : Array Int) (start : Int) (end_ : Int) : Bool :=
end_ - start == a2.size + a1.size ∧
start ≥ 0 ∧ start ≤ end_ ∧ end_ ≤ b.size
def sorted_slice (a : Array Int) (start : Int) (end_ : Int) : Prop :=
start ≥ 0 ∧ start ≤ end_ ∧ end_ ≤ a.size ∧
∀ i j:Nat, start ≤ i ∧ i ≤ j ∧ j < end_ → a[i]! ≤ a[j]!
def sorted_seq (a : Array Int) : Prop :=
∀ i j:Nat, 0 ≤ i ∧ i ≤ j ∧ j < a.size → a[i]! ≤ a[j]!
def sorted (a : Array Int) : Prop :=
∀ i j:Nat, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mergeSimple (a1 : Array Int) (a2 : Array Int) (start : Int) (end_ : Int) (b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mergeSimple_spec (a1 : Array Int) (a2 : Array Int) (start : Int) (end_ : Int) (b : Array Int) :
sorted_seq a1 ∧
sorted_seq a2 ∧
start ≥ 0 ∧ start ≤ end_ ∧ end_ ≤ b.size ∧
a1.size + a2.size == end_ - start + 1
→
sorted_slice (mergeSimple a1 a2 start end_ b) start end_ :=
sorry
-- </vc-theorems>