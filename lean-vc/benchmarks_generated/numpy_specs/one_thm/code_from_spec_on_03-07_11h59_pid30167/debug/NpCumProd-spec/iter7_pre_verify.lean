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
  simp [cumProdAux, h]

/- LLM HELPER -/
lemma cumProdAux_succ {n : Nat} (a : Vector Int n) (k : Nat) (h : k + 1 < n) :
  cumProdAux a (k + 1) = cumProdAux a k * a[k + 1]'h := by
  simp [cumProdAux, h]

/- LLM HELPER -/
lemma cumProd_get {n : Nat} (a : Vector Int n) (i : Fin n) :
  (cumProd a)[i] = cumProdAux a i.val := by
  simp [cumProd, Vector.get_ofFn]

theorem cumProd_spec {n : Nat} (a : Vector Int n) :
  (n > 0 → (cumProd a)[0] = a[0]) ∧
  ∀ i : Fin n, i.val > 0 → (cumProd a)[i] = (cumProd a)[⟨i.val - 1, Nat.lt_trans (Nat.pred_lt (ne_of_gt ‹i.val > 0›)) i.isLt⟩] * a[i] := by
  constructor
  · intro h
    rw [cumProd_get]
    have h_pos : 0 < n := h
    rw [cumProdAux_zero a h_pos]
    have h_zero : 0 < n := h
    have : (0 : Fin n) = ⟨0, h_zero⟩ := by simp
    rw [this]
    rfl
  · intro i hi
    rw [cumProd_get]
    have h1 : i.val - 1 + 1 = i.val := Nat.succ_pred_eq_of_pos hi
    rw [← h1]
    have h2 : i.val - 1 + 1 < n := by rw [h1]; exact i.isLt
    rw [cumProdAux_succ a (i.val - 1) h2]
    rw [cumProd_get]
    rfl

end NpCumProd