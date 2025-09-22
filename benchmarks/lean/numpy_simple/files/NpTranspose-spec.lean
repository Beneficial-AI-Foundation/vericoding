-- <vc-preamble>
def Matrix (m n : Nat) (α : Type) := Fin m → Fin n → α

instance {m n : Nat} {α : Type} [Inhabited α] : GetElem (Matrix m n α) (Nat × Nat) α (fun _ ij => ij.1 < m ∧ ij.2 < n) where
  getElem mat ij h := mat ⟨ij.1, h.1⟩ ⟨ij.2, h.2⟩

def Matrix.size {m n : Nat} {α : Type} (_ : Matrix m n α) : Nat := m * n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def transpose {m n : Nat} (arr : Matrix m n Int) : Matrix n m Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem transpose_spec {m n : Nat} (arr : Matrix m n Int) :
  let ret := transpose arr
  (ret.size = n * m) ∧
  (∀ i j : Nat, i < m → j < n → ret[(j,i)]! = arr[(i,j)]!) :=
sorry
-- </vc-theorems>