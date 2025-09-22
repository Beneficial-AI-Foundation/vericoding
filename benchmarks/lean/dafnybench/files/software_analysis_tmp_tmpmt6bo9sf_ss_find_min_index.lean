-- <vc-preamble>
def is_sorted (s : Array Int) : Prop :=
∀ i j, 0 ≤ i → i ≤ j → j < s.size → s[i]! ≤ s[j]!
def is_permutation (a b : Array Int) : Prop :=
a.size = b.size ∧
((a.size = 0 ∧ b.size = 0) ∨
∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < b.size ∧
a[i]! = b[j]!)
def is_permutation2 (a b : Array Int) : Bool :=
a.toList = b.toList
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_index (a : Array Int) (s : Int) (e : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_index_spec (a : Array Int) (s e min_i : Int) :
a.size > 0 →
0 ≤ s →
s < a.size →
e ≤ a.size →
e > s →
min_i = find_min_index a s e →
(min_i ≥ s ∧
min_i < e ∧
∀ k:Nat, s ≤ k → k < e → a[min_i.toNat]! ≤ a[k]!) :=
sorry
-- </vc-theorems>