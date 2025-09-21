-- <vc-preamble>
partial def sum (a : Array Int) (i j : Int) : Int :=
if i = j then
0
else
a[(j-1).toNat]! + sum a i (j-1)

def is_prefix_sum_for (a c : Array Int) : Prop :=
a.size + 1 = c.size ∧
c[0]! = 0 ∧
∀ j, 1 ≤ j ∧ j ≤ a.size → c[j]! = sum a 0 j

inductive List_ (T : Type)
| Nil : List_ T
| Cons : T → List_ T → List_ T

def mem {T : Type} [BEq T] (x : T) (l : List_ T) : Bool :=
match l with
| List_.Nil => false
| List_.Cons y r => if x == y then true else mem x r
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def from_array {T : Type} (a : Array T) : List_ T :=
sorry

def queryFast (a c : Array Int) (i j : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem queryFast_spec (a c : Array Int) (i j : Int) :
is_prefix_sum_for a c ∧
0 ≤ i ∧ i ≤ j ∧ j ≤ a.size ∧ a.size < c.size →
queryFast a c i j = sum a i j :=
sorry
-- </vc-theorems>