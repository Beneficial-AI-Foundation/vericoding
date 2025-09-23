-- <vc-preamble>
def count (a : Array Int) (x : Int) : Nat :=
a.foldl (fun acc y => if y = x then acc + 1 else acc) 0

def merged (a1 : Array Int) (a2 : Array Int) (b : Array Int) (start : Int) (end_ : Int) : Prop :=
end_ - start == a1.size + a2.size ∧
0 ≤ start ∧ start ≤ end_ ∧ end_ ≤ b.size ∧
(∀ x : Int, count a1 x + count a2 x = count (b.extract start.toNat end_.toNat) x)

def sorted_slice (a : Array Int) (start : Int) (end_ : Int) : Prop :=
0 ≤ start ∧ start ≤ end_ ∧ end_ ≤ a.size ∧
∀ i j:Nat, start ≤ i ∧ i ≤ j ∧ j < end_ → a[i]! ≤ a[j]!

def sorted_seq (a : Array Int) : Prop :=
∀ i j:Nat, 0 ≤ i ∧ i ≤ j ∧ j < a.size → a[i]! ≤ a[j]!

def sorted (a : Array Int) : Prop :=
∀ i j:Nat, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def merge (a1 : Array Int) (a2 : Array Int) (start : Int) (end_ : Int) (b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem merge_spec (a1 : Array Int) (a2 : Array Int) (start : Int) (end_ : Int) (b : Array Int) :
sorted_seq a1 ∧
sorted_seq a2 ∧
end_ - start == a1.size + a2.size ∧
0 ≤ start ∧ start < end_ ∧ end_ < a1.size ∧ end_ ≤ a2.size ∧ end_ < b.size ∧
end_ < a1.size ∧ end_ < a2.size ∧
b.size == a2.size + a1.size
→
sorted_slice (merge a1 a2 start end_ b) start end_ ∧
merged a1 a2 (merge a1 a2 start end_ b) start end_ :=
sorry
-- </vc-theorems>