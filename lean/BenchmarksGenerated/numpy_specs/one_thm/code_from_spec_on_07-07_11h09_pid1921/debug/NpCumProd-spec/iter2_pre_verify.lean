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
  (cumProd a)[i] = (cumProd a)[i.val - 1]'(Nat.sub_lt_of_pos_le (Nat.pos_of_ne_zero (ne_of_gt h)) (Nat.le_of_lt_succ (Nat.lt_succ_of_lt i.isLt))) * a[i] := by
  simp [cumProd, Vector.get_ofFn]
  have h_pos : i.val > 0 := h
  have h_pred : i.val - 1 < n := Nat.sub_lt_of_pos_le (Nat.pos_of_ne_zero (ne_of_gt h)) (Nat.le_of_lt_succ (Nat.lt_succ_of_lt i.isLt))
  have h_eq : i.val = (i.val - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.pos_iff_ne_zero.mp h_pos)]
  rw [h_eq]
  rw [cumProdAux_succ]
  congr 1
  simp [cumProd, Vector.get_ofFn]

theorem cumProd_spec {n : Nat} (a : Vector Int n) :
  (cumProd a)[0]'(Nat.zero_lt_succ (n - 1)) = a[0]'(Nat.zero_lt_succ (n - 1)) ∧
  ∀ i : Fin n, i.val > 0 → (cumProd a)[i] = (cumProd a)[i.val - 1]'(Nat.sub_lt_of_pos_le (Nat.pos_of_ne_zero (ne_of_gt (show i.val > 0 from by assumption))) (Nat.le_of_lt_succ (Nat.lt_succ_of_lt i.isLt))) * a[i] := by
  constructor
  · cases' n with n
    · simp [cumProd]
    · exact cumProd_get_zero a (Nat.zero_lt_succ n)
  · intro i h
    exact cumProd_get_succ a i h

end NpCumProd