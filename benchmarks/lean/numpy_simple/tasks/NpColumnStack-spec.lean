-- <vc-preamble>
def Matrix (m n : Nat) (α : Type) := Fin m → Fin n → α

instance {m n : Nat} {α : Type} [Inhabited α] : GetElem (Matrix m n α) (Nat × Nat) α (fun _ ij => ij.1 < m ∧ ij.2 < n) where
  getElem mat ij h := mat ⟨ij.1, h.1⟩ ⟨ij.2, h.2⟩

def Matrix.size {m n : Nat} {α : Type} (_ : Matrix m n α) : Nat := m * n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def column_stack {m n : Nat} (input : Vector (Vector Int m) n) : Matrix m n Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem column_stack_spec {m n : Nat} (input : Vector (Vector Int m) n)
  (h1 : n ≠ 0)
  (h2 : ∀ i : Fin n, input[i].size = m) :
  let ret := column_stack input
  (ret.size = m * n) ∧
  (∀ i : Nat, ∀ j : Nat, i < n → j < m → ret[(j,i)]! = input[i]![j]!) :=
sorry
-- </vc-theorems>