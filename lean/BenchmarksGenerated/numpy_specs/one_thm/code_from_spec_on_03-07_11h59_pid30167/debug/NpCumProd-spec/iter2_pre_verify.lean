namespace NpCumProd

/- LLM HELPER -/
def cumProdAux {n : Nat} (a : Vector Int n) : Nat → Int
  | 0 => if h : 0 < n then a[0]'h else 0
  | k + 1 => if h : k + 1 < n then cumProdAux a k * a[k + 1]'h else 0

def cumProd {n : Nat} (a : Vector Int n) : Vector Int n :=
  Vector.ofFn (fun i => cumProdAux a i.val)

/- LLM HELPER -/
lemma cumProdAux_zero {n : Nat} (a : Vector Int n) (h : 0 < n) :
  cumProdAux a 0 = a[0]'h := by
  simp [cumProdAux]

/- LLM HELPER -/
lemma cumProdAux_succ {n : Nat} (a : Vector Int n) (k : Nat) (h : k + 1 < n) :
  cumProdAux a (k + 1) = cumProdAux a k * a[k + 1]'h := by
  simp [cumProdAux]

/- LLM HELPER -/
lemma cumProd_get {n : Nat} (a : Vector Int n) (i : Fin n) :
  (cumProd a)[i] = cumProdAux a i.val := by
  simp [cumProd, Vector.get_ofFn]

theorem cumProd_spec {n : Nat} (a : Vector Int n) :
  (cumProd a)[0]'(Nat.zero_lt_of_ne_zero fun h => by cases n <;> simp [Vector.get] at a; exact Nat.not_lt_zero 0 (Fin.pos ⟨0, by simp⟩)) = a[0]'(Nat.zero_lt_of_ne_zero fun h => by cases n <;> simp [Vector.get] at a; exact Nat.not_lt_zero 0 (Fin.pos ⟨0, by simp⟩)) ∧
  ∀ i : Fin n, i.val > 0 → (cumProd a)[i] = (cumProd a)[⟨i.val - 1, by have : i.val - 1 < n := by have : i.val < n := i.isLt; have : i.val > 0 := by assumption; exact Nat.lt_trans (Nat.pred_lt (ne_of_gt this)) i.isLt⟩]'(by have : i.val - 1 < n := by have : i.val < n := i.isLt; have : i.val > 0 := by assumption; exact Nat.lt_trans (Nat.pred_lt (ne_of_gt this)) i.isLt; exact this) * a[i] := by
  constructor
  · rw [cumProd_get]
    rw [cumProdAux_zero]
  · intro i hi
    rw [cumProd_get]
    have h1 : i.val - 1 + 1 = i.val := Nat.succ_pred_eq_of_pos hi
    rw [← h1]
    have h2 : i.val - 1 + 1 < n := by rw [h1]; exact i.isLt
    rw [cumProdAux_succ a (i.val - 1) h2]
    rw [cumProd_get]
    rfl

end NpCumProd