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
  rw [cumProdAux]
  simp [h]

/- LLM HELPER -/
lemma cumProdAux_succ {n : Nat} (a : Vector Int n) (k : Nat) (h : k + 1 < n) :
  cumProdAux a (k + 1) = cumProdAux a k * a[k + 1]'h := by
  rw [cumProdAux]
  simp [h]

/- LLM HELPER -/
lemma cumProd_zero {n : Nat} (a : Vector Int n) (h : 0 < n) :
  (cumProd a)[0]'h = a[0]'h := by
  rw [cumProd, Vector.get_ofFn]
  simp [Fin.val_zero]
  exact cumProdAux_zero a h

/- LLM HELPER -/
lemma cumProd_succ {n : Nat} (a : Vector Int n) (i : Fin n) (h : i.val > 0) :
  (cumProd a)[i] = (cumProd a)[i.val - 1]'(Nat.sub_lt i.isLt (Nat.pos_of_ne_zero (ne_of_gt h))) * a[i] := by
  rw [cumProd, Vector.get_ofFn]
  have h_pos : i.val > 0 := h
  have h_pred : i.val - 1 < n := Nat.sub_lt i.isLt (Nat.pos_of_ne_zero (ne_of_gt h))
  have h_succ : i.val - 1 + 1 = i.val := Nat.sub_add_cancel (Nat.le_of_lt h_pos)
  rw [← h_succ]
  rw [cumProdAux_succ a (i.val - 1) i.isLt]
  rw [cumProd, Vector.get_ofFn]
  simp

theorem cumProd_spec {n : Nat} (a : Vector Int n) :
  (n > 0 → (cumProd a)[0]'(Nat.pos_of_ne_zero (Nat.not_eq_zero_of_lt (by assumption))) = a[0]'(Nat.pos_of_ne_zero (Nat.not_eq_zero_of_lt (by assumption)))) ∧
  (∀ i : Fin n, i.val > 0 → (cumProd a)[i] = (cumProd a)[i.val - 1]'(Nat.sub_lt i.isLt (Nat.pos_of_ne_zero (Nat.not_eq_zero_of_lt (by assumption)))) * a[i]) := by
  constructor
  · intro h
    exact cumProd_zero a h
  · intro i h
    exact cumProd_succ a i h

end NpCumProd