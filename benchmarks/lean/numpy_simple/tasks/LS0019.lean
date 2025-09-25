-- <vc-preamble>
def Matrix (m n : Nat) (α : Type) := Fin m → Fin n → α

instance {m n : Nat} {α : Type} [Inhabited α] : GetElem (Matrix m n α) (Nat × Nat) α (fun _ ij => ij.1 < m ∧ ij.2 < n) where
  getElem mat ij h := mat ⟨ij.1, h.1⟩ ⟨ij.2, h.2⟩

def Matrix.size {m n : Nat} {α : Type} (_ : Matrix m n α) : Nat := m * n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def flatten2 {m n : Nat} (mat : Matrix m n Int) : Vector Int (m * n) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flatten2_spec {m n : Nat} (mat : Matrix m n Int)
  (h1 : m > 0)
  (h2 : n > 0) :
  let ret := flatten2 mat
  (ret.size = m * n) ∧
  (∀ i j : Nat, i < m → j < n → ret[i * n + j]! = mat[(i,j)]!) :=
sorry
-- </vc-theorems>