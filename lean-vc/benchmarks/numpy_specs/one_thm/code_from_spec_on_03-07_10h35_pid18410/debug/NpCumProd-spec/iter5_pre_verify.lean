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

/- LLM HELPER -/
lemma fin_nonempty_of_zero {n : Nat} (h : 0 < n) : Nonempty (Fin n) := by
  exact ⟨0⟩

theorem cumProd_spec {n : Nat} (a : Vector Int n) :
  (n > 0 → (cumProd a)[0]'(Nat.pos_iff_ne_zero.mpr (Fin.pos_iff_nonempty.mpr ⟨0⟩)) = a[0]'(Nat.pos_iff_ne_zero.mpr (Fin.pos_iff_nonempty.mpr ⟨0⟩))) ∧
  ∀ i : Fin n, i.val > 0 → (cumProd a)[i] = (cumProd a)[⟨i.val - 1, Nat.sub_lt i.isLt (Nat.pos_of_ne_zero (Ne.symm (Nat.ne_of_gt i.val_pos)))⟩] * a[i] := by
  constructor
  · intro hn
    rw [cumProd_get]
    rw [cumProdAux_zero]
  · intro i hi
    rw [cumProd_get]
    have h_pred : i.val - 1 + 1 = i.val := Nat.sub_add_cancel hi
    rw [← h_pred]
    rw [cumProdAux_succ]
    congr 1
    rw [cumProd_get]
    simp [h_pred]

end NpCumProd