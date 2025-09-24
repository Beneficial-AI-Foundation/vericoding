-- <vc-preamble>
partial def sum (a : Array Int) (i j : Int) : Int :=
if i == j then
0
else
a[(j-1).toNat]! + sum a i (j-1)

def is_prefix_sum_for (a c : Array Int) : Prop :=
a.size + 1 == c.size ∧
c[0]! == 0 ∧
∀ j, 1 ≤ j ∧ j ≤ a.size → c[j]! == sum a 0 j

inductive List_ (T : Type) where
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

def query (a : Array Int) (i j : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem query_spec (a : Array Int) (i j : Int) :
0 ≤ i ∧ i ≤ j ∧ j ≤ a.size →
query a i j = sum a i j :=
sorry

theorem from_array_spec {T : Type} [BEq T] [Inhabited T] (a : Array T) :
a.size > 0 →
∀ j, 0 ≤ j ∧ j < a.size →
mem (a[j]!) (from_array a) :=
sorry
-- </vc-theorems>