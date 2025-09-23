-- <vc-preamble>
def Matrix (m n : Nat) (α : Type) := Fin m → Fin n → α

instance {m n : Nat} {α : Type} [Inhabited α] : GetElem (Matrix m n α) (Nat × Nat) α (fun _ ij => ij.1 < m ∧ ij.2 < n) where
  getElem mat ij h := mat ⟨ij.1, h.1⟩ ⟨ij.2, h.2⟩

def Matrix.size {m n : Nat} {α : Type} (_ : Matrix m n α) : Nat := m * n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tril {m n : Nat} (arr : Matrix m n Int) (k : Int) : Matrix m n Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tril_spec {m n : Nat} (arr : Matrix m n Int) (k : Int)
  (h : -m + 1 < k ∧ k < n - 1) :
  let ret := tril arr k
  (ret.size = m * n) ∧
  (∀ i j : Nat, i < m → j < n →
    if j - i > k then ret[(i,j)]! = 0 else ret[(i,j)]! = arr[(i,j)]!) :=
sorry
-- </vc-theorems>