/-
# NumPy Select Specification

Port of np_select.dfy to Lean 4
-/

namespace DafnySpecs.NpSelect

-- LLM HELPER
def selectHelper {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m) (j : Fin n) : Float :=
  let rec findFirst (i : Nat) (h : i < m) : Float :=
    if condlist[⟨i, h⟩][j] then
      choicelist[⟨i, h⟩][j]
    else if i + 1 < m then
      findFirst (i + 1) (Nat.lt_trans (Nat.lt_succ_self i) h)
    else
      0.0
  if h : m > 0 then
    findFirst 0 h
  else
    0.0

/-- Select elements based on conditions -/
def select {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m) : Vector Float n :=
  Vector.ofFn (fun j => selectHelper condlist choicelist j)

-- LLM HELPER
lemma vector_length_eq {α : Type*} {n : Nat} (v : Vector α n) : v.toList.length = n := by
  simp [Vector.toList_length]

/-- Specification: The result has correct length -/
theorem select_length {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m)
  (h1 : m > 0 ∧ n > 0)
  (h2 : ∀ i : Fin m, condlist[i].toList.length = n ∧ choicelist[i].toList.length = n) :
  let ret := select condlist choicelist
  ret.toList.length = n := by
  simp [select]
  apply vector_length_eq

-- LLM HELPER
lemma selectHelper_spec {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m)
  (i : Fin m) (j : Fin n) (h : condlist[i][j] = true) (h_pos : m > 0) :
  ∃ k : Fin m, k ≤ i ∧ condlist[k][j] = true ∧ selectHelper condlist choicelist j = choicelist[k][j] := by
  use i
  constructor
  · exact le_refl i
  constructor
  · exact h
  · simp [selectHelper, h_pos]
    induction' i using Fin.induction with k ih
    · simp [h]
    · simp [h]

/-- Specification: Conditional selection -/
theorem select_spec {m n : Nat} (condlist : Vector (Vector Bool n) m) (choicelist : Vector (Vector Float n) m)
  (h1 : m > 0 ∧ n > 0)
  (h2 : ∀ i : Fin m, condlist[i].toList.length = n ∧ choicelist[i].toList.length = n) :
  let ret := select condlist choicelist
  ∀ i : Fin m, ∀ j : Fin n, condlist[i][j] → ret[j] = choicelist[i][j] := by
  intro i j h_cond
  simp [select]
  have h_get : ret[j] = selectHelper condlist choicelist j := by
    simp [Vector.get_ofFn]
  rw [h_get]
  have h_spec := selectHelper_spec condlist choicelist i j h_cond h1.1
  obtain ⟨k, hk_le, hk_cond, hk_eq⟩ := h_spec
  rw [hk_eq]
  congr

end DafnySpecs.NpSelect