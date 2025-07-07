namespace NpCumProd

-- LLM HELPER
def cumProdAux {n : Nat} (a : Vector Int n) : Nat → Int
  | 0 => if h : 0 < n then a[0]'h else 0
  | k + 1 => if h : k + 1 < n then cumProdAux a k * a[k + 1]'h else 0

def cumProd {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.ofFn (fun i => cumProdAux a i.val)

-- LLM HELPER
lemma cumProdAux_zero {n : Nat} (a : Vector Int n) (h : 0 < n) :
  cumProdAux a 0 = a[0]'h := by
  simp [cumProdAux]

-- LLM HELPER
lemma cumProdAux_succ {n : Nat} (a : Vector Int n) (k : Nat) (h : k + 1 < n) :
  cumProdAux a (k + 1) = cumProdAux a k * a[k + 1]'h := by
  simp [cumProdAux]

-- LLM HELPER
lemma cumProd_get_zero {n : Nat} (a : Vector Int n) (h : 0 < n) :
  (cumProd a)[0]'h = a[0]'h := by
  simp [cumProd, Vector.get_ofFn]
  exact cumProdAux_zero a h

-- LLM HELPER
lemma cumProd_get_succ {n : Nat} (a : Vector Int n) (i : Fin n) (h : i.val > 0) :
  (cumProd a)[i] = (cumProd a)[i.val - 1]'(by omega) * a[i] := by
  simp [cumProd, Vector.get_ofFn]
  have h_pos : i.val > 0 := h
  have h_pred : i.val - 1 < n := by omega
  have h_eq : i.val = (i.val - 1) + 1 := by omega
  rw [h_eq]
  rw [cumProdAux_succ]
  congr 1
  simp [cumProd, Vector.get_ofFn]

theorem cumProd_spec {n : Nat} (a : Vector Int n) :
  (cumProd a)[0]'(by omega) = a[0]'(by omega) ∧
  ∀ i : Fin n, i.val > 0 → (cumProd a)[i] = (cumProd a)[i.val - 1]'(by omega) * a[i] := by
  constructor
  · exact cumProd_get_zero a (by omega)
  · intro i h
    exact cumProd_get_succ a i h

end NpCumProd