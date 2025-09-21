-- <vc-preamble>
def count (a : Array Int) (x : Int) : Nat :=
a.foldl (fun acc y => if y = x then acc + 1 else acc) 0

def valid_permut (a b : Array Int) : Prop :=
a.size = b.size ∧ ∀ x : Int, count a x = count b x

def sorted (a : Array Int) : Prop :=
∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < a.size → a[i]! ≤ a[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def swap (a : Array Int) (i j : Int) : Array Int :=
sorry

def lol_sort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem swap_spec (a : Array Int) (i j : Int) :
0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a.size →
let result := swap a i j
result.size = a.size ∧ valid_permut result a :=
sorry

theorem lol_sort_spec (a : Array Int) :
let result := lol_sort a
valid_permut result a ∧ sorted result :=
sorry
-- </vc-theorems>