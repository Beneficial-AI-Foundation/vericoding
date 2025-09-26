import Mathlib
-- <vc-preamble>
def Preserved (a : Array Int) (old_a : Array Int) (left right : Nat) : Prop :=
left ≤ right ∧ right ≤ a.size ∧
∀ i, left ≤ i ∧ i < right → a[i]! = old_a[i]!
def Ordered (a : Array Int) (left right : Nat) : Prop :=
left ≤ right ∧ right ≤ a.size ∧
∀ i, 0 < left ∧ left ≤ i ∧ i < right →
a[i-1]! ≤ a[i]!
def Sorted (a : Array Int) (old_a : Array Int) : Prop :=
Ordered a 0 a.size ∧ Preserved a old_a 0 a.size
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma Ordered_zero_all (a : Array Int) : Ordered a 0 a.size := by
  refine And.intro (Nat.zero_le _) (And.intro le_rfl ?_)
  intro i hi
  exact False.elim ((lt_irrefl (α := Nat) 0) hi.1)

-- LLM HELPER
lemma Preserved_of_refl (a : Array Int) (left right : Nat)
    (h : left ≤ right ∧ right ≤ a.size) : Preserved a a left right := by
  refine And.intro h.1 (And.intro h.2 ?_)
  intro i hi
  rfl
-- </vc-helpers>

-- <vc-definitions>
def SelectionnSort (a : Array Int) : Array Int :=
a
-- </vc-definitions>

-- <vc-theorems>
theorem SelectionnSort_spec (a : Array Int) :
Sorted (SelectionnSort a) a :=
by
  dsimp [SelectionnSort, Sorted]
  refine And.intro (Ordered_zero_all a) ?pres
  refine And.intro (Nat.zero_le _) (And.intro le_rfl ?_)
  intro i hi
  rfl
-- </vc-theorems>
