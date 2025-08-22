namespace NpRavel

def ravel {m n : Nat} (arr : Matrix Int m n) : Vector Int (m * n) := 
  Vector.ofFn (fun k => arr[k / n]![k % n]!)

-- LLM HELPER
lemma div_mod_lt {m n k : Nat} (h1 : k < m * n) (h2 : 0 < n) : k / n < m := by
  have : k / n * n ≤ k := Nat.div_mul_le_self k n
  have : k < m * n := h1
  rw [Nat.mul_comm] at this
  exact Nat.div_lt_of_lt_mul this

-- LLM HELPER
lemma mod_lt {n k : Nat} (h : 0 < n) : k % n < n := Nat.mod_lt k h

theorem ravel_spec {m n : Nat} (arr : Matrix Int m n) :
  let ret := ravel arr
  (ret.toList.length = m * n) ∧
  (∀ i j : Nat, i < m → j < n → ret[i * n + j]! = arr[i]![j]!) := by
  constructor
  · simp [ravel]
    exact Vector.length_toList _
  · intro i j hi hj
    simp [ravel]
    rw [Vector.getElem_ofFn]
    by_cases h : n = 0
    · simp [h] at hj
    · have hn : 0 < n := Nat.pos_of_ne_zero h
      have : i * n + j < m * n := by
        have : i * n < m * n := Nat.mul_lt_mul_of_pos_right hi hn
        have : j < n := hj
        omega
      congr 1
      · rw [Nat.add_div_of_le_mod_add_mod]
        rw [Nat.mul_div_cancel_left i hn]
        simp [Nat.mod_eq_of_lt hj]
      · rw [Nat.add_mod]
        rw [Nat.mul_mod]
        simp [Nat.mod_self]
        exact Nat.mod_eq_of_lt hj

end NpRavel