namespace NpTril

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := Fin m → Fin n → α

-- LLM HELPER
def Matrix.of {α : Type*} {m n : Nat} (f : Fin m → Fin n → α) : Matrix α m n := f

-- LLM HELPER
def Matrix.get {α : Type*} {m n : Nat} (M : Matrix α m n) (i : Fin m) (j : Fin n) : α := M i j

-- LLM HELPER
def Matrix.toList_length {α : Type*} {m n : Nat} (M : Matrix α m n) : Nat := m * n

def tril {m n : Nat} (arr : Matrix Int m n) (k : Int) : Matrix Int m n :=
  Matrix.of fun i j => if (j : Int) - (i : Int) > k then 0 else arr i j

theorem tril_spec {m n : Nat} (arr : Matrix Int m n) (k : Int)
  (h : -↑m + 1 < k ∧ k < ↑n - 1) :
  let ret := tril arr k
  (Matrix.toList_length ret = m * n) ∧
  (∀ i : Fin m, ∀ jf : Fin n, ret i jf = if k < ↑jf - ↑i then 0 else arr i jf) := by
  constructor
  · rfl
  · intro i jf
    simp [tril, Matrix.of]
    by_cases h_cond : k < ↑jf - ↑i
    · simp [h_cond]
      have : (jf : Int) - (i : Int) > k := by linarith
      simp [this]
    · simp [h_cond]
      have : ¬((jf : Int) - (i : Int) > k) := by linarith
      simp [this]

end NpTril