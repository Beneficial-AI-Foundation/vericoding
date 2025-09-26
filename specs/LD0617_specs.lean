-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multisets {α : Type} [Inhabited α] (s : Array α) : List α :=
sorry

def swap {α : Type} [Inhabited α] (a : Array α) (i j : Nat) : Array α :=
sorry

def two_way_sort (a : Array Bool) : Array Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem swap_spec {α : Type} [Inhabited α] (a : Array α) (i j : Nat) :
0 ≤ i ∧ i < j ∧ j < a.size →
let a' := swap a i j
(a'[i]! = a[j]!) ∧
(a'[j]! = a[i]!) ∧
(∀ m, 0 ≤ m ∧ m < a.size ∧ m ≠ i ∧ m ≠ j → a'[m]! = a[m]!) ∧
(multisets a' = multisets a) :=
sorry

theorem two_way_sort_spec (a : Array Bool) :
let a' := two_way_sort a
(∀ m n, 0 ≤ m ∧ m < n ∧ n < a'.size → ¬(a'[m]!) ∨ a'[n]!) ∧
(multisets a' = multisets a) :=
sorry
-- </vc-theorems>