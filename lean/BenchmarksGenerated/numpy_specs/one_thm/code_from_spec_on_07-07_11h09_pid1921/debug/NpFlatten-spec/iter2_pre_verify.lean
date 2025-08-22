namespace NpFlatten

-- LLM HELPER
def Matrix (α : Type*) (m n : Nat) : Type* := 
  { arr : Array (Array α) // arr.size = m ∧ ∀ i, i < m → arr[i]!.size = n }

-- LLM HELPER
instance : GetElem (Matrix α m n) Nat (Array α) (fun _ i => i < m) where
  getElem mat i h := mat.val[i]!

def flatten2 {m n : Nat} (mat : Matrix Int m n) : Vector Int (m * n) := 
  Vector.ofFn (fun k => mat[k / n]![k % n]!)

-- LLM HELPER
lemma div_mod_unique (k m n : Nat) (h : n > 0) : k < m * n → k / n < m ∧ k % n < n := by
  intro hk
  constructor
  · rw [Nat.div_lt_iff_lt_mul h]
    exact hk
  · exact Nat.mod_lt k h

-- LLM HELPER
lemma flatten_index_bounds {m n : Nat} (i j : Nat) (hi : i < m) (hj : j < n) (hn : n > 0) :
  i * n + j < m * n := by
  calc i * n + j 
    < i * n + n := Nat.add_lt_add_left hj (i * n)
    _ = (i + 1) * n := by rw [Nat.add_mul]
    _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hi)

-- LLM HELPER
lemma div_add_mod {i j n : Nat} (hn : n > 0) (hj : j < n) :
  (i * n + j) / n = i ∧ (i * n + j) % n = j := by
  constructor
  · rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_zero_of_lt hj]
    simp
  · rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hj

-- LLM HELPER
def Matrix.get_rows (mat : Matrix α m n) : Nat := m

-- LLM HELPER
def Matrix.get_cols (mat : Matrix α m n) : Nat := n

theorem flatten2_spec {m n : Nat} (mat : Matrix Int m n)
  (h1 : m > 0)
  (h2 : n > 0) :
  let ret := flatten2 mat
  (ret.toList.length = m * n) ∧
  (∀ i j : Nat, i < m → j < n → ret[i * n + j]! = mat[i]![j]!) := by
  constructor
  · simp [flatten2]
    rw [Vector.toList_ofFn]
    simp [List.length_ofFn]
  · intros i j hi hj
    simp [flatten2]
    rw [Vector.getElem_ofFn]
    have h_bounds := flatten_index_bounds hi hj h2
    have h_div_mod := div_add_mod h2 hj
    rw [h_div_mod.1, h_div_mod.2]

end NpFlatten