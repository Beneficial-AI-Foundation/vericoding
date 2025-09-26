import Mathlib
-- <vc-preamble>
def IsPrefixDuplicate (a : Array Int) (k : Int) (p : Int) : Prop :=
∃ i j, 0 ≤ i ∧ i < j ∧ j < k ∧ a[i.toNat]! = p ∧ a[j.toNat]! = p
def IsDuplicate (a : Array Int) (p : Int) : Prop :=
IsPrefixDuplicate a a.size p
-- </vc-preamble>

-- <vc-helpers>
noncomputable section

-- LLM HELPER
-- Convert an existence over two variables into an existence over a product
theorem exists_prod_of_exists2 {α β : Type _} {P : α → β → Prop} :
  (∃ a b, P a b) → ∃ pq : α × β, P pq.1 pq.2 :=
by
  intro h
  rcases h with ⟨a, b, hP⟩
  exact ⟨(a, b), by simpa⟩

-- </vc-helpers>

-- <vc-definitions>
def Search (a : Array Int) : (Int × Int) :=
by
  classical
  exact
    if h : ∃ p q, p ≠ q ∧ IsDuplicate a p ∧ IsDuplicate a q then
      Classical.choose (exists_prod_of_exists2 h)
    else
      (0, 1)
-- </vc-definitions>

-- <vc-theorems>
theorem Search_spec (a : Array Int) :
(4 ≤ a.size) →
(∃ p q, p ≠ q ∧ IsDuplicate a p ∧ IsDuplicate a q) →
(∀ i, 0 ≤ i ∧ i < a.size → 0 ≤ a[i]! ∧ a[i]! < a.size - 2) →
let (p, q) := Search a
p ≠ q ∧ IsDuplicate a p ∧ IsDuplicate a q :=
by
  intro _ hex _
  classical
  have : let (p, q) := Classical.choose (exists_prod_of_exists2 hex)
    p ≠ q ∧ IsDuplicate a p ∧ IsDuplicate a q :=
    by
      simpa using (Classical.choose_spec (exists_prod_of_exists2 hex))
  simpa [Search, hex] using this
-- </vc-theorems>
