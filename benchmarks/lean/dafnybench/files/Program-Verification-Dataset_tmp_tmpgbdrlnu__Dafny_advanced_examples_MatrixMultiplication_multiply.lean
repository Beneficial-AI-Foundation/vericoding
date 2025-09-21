-- <vc-preamble>
partial def RowColumnProductFrom (m1 : Array (Array Int)) (m2 : Array (Array Int)) (row : Nat) (column : Nat) (k : Nat) : Int :=
if k == m1.size then
0
else
m1[row]![k]! * m2[k]![column]! + RowColumnProductFrom m1 m2 row column (k + 1)
def RowColumnProduct (m1 : Array (Array Int)) (m2 : Array (Array Int)) (row : Nat) (column : Nat) : Int :=
RowColumnProductFrom m1 m2 row column 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiply (m1 : Array (Array Int)) (m2 : Array (Array Int)) : Array (Array Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiply_spec (m1 m2 : Array (Array Int)) :
m1.size > 0 ∧ m2.size > 0 ∧ m1.size == m2.size →
let m3 := multiply m1 m2
m3.size == m1.size ∧ m3.size == m2.size ∧
∀ i j, i < m3.size ∧ j < m3.size →
m3[i]![j]! == RowColumnProduct m1 m2 i j :=
sorry
-- </vc-theorems>