-- <vc-preamble>
def is_sorted (ss : Array Int) : Prop :=
∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < ss.size → ss[i]! ≤ ss[j]!

def is_permutation (a b : Array Int) : Prop :=
a.size = b.size ∧
(a.size = 0 ∧ b.size = 0 ∨
∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < b.size ∧
a[i]! = b[j]!)

def is_permutation2 (a b : Array Int) : Prop :=
a.toList = b.toList
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_index (a : Array Int) (s : Int) (e : Int) : Int :=
sorry

def selection_sort (ns : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_index_spec (a : Array Int) (s : Int) (e : Int) :
a.size > 0 ∧
0 ≤ s ∧ s < a.size ∧
e ≤ a.size ∧
e > s →
let min_i := find_min_index a s e
min_i ≥ s ∧
min_i < e ∧
∀ k:Nat, s ≤ k ∧ k < e → a[min_i.toNat]! ≤ a[k]! :=
sorry

theorem selection_sort_spec (ns : Array Int) :
ns.size ≥ 0 →
let result := selection_sort ns
is_sorted result ∧
is_permutation2 ns result :=
sorry
-- </vc-theorems>