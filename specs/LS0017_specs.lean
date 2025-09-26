-- <vc-preamble>
def Matrix (m n : Nat) (α : Type) := Fin m → Fin n → α

instance {m n : Nat} {α : Type} [Inhabited α] : GetElem (Matrix m n α) (Nat × Nat) α (fun _ ij => ij.1 < m ∧ ij.2 < n) where
  getElem mat ij h := mat ⟨ij.1, h.1⟩ ⟨ij.2, h.2⟩

def Matrix.size {m n : Nat} {α : Type} (_ : Matrix m n α) : Nat := m * n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diagonal {n : Nat} (arr : Matrix n n Int) (k : Int) : Vector Int (if k > 0 then n - k.natAbs else n + k.natAbs) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diagonal_spec {n : Nat} (arr : Matrix n n Int) (k : Int)
  (h1 : -n < k ∧ k < n) :
  let ret := diagonal arr k
  (if k > 0 then ret.size = n - k.natAbs else ret.size = n + k.natAbs) ∧
  (∀ i : Nat, i < ret.size →
    if k ≥ 0 then ret[i]! = arr[(i, i + k.natAbs)]!
    else ret[i]! = arr[(i + k.natAbs, i)]!) :=
sorry
-- </vc-theorems>