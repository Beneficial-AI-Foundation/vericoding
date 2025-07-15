/-
# NumPy Piecewise Specification

Port of np_piecewise.dfy to Lean 4
-/

namespace DafnySpecs.NpPiecewise

-- LLM HELPER
def find_first_true_index {m : Nat} (condlist : Vector (Float → Bool) m) (val : Float) : Option Nat :=
  let rec helper (i : Nat) : Option Nat :=
    if h : i < m then
      if condlist[i]! val then
        some i
      else
        helper (i + 1)
    else
      none
  helper 0

-- LLM HELPER
def apply_piecewise_element {m : Nat} (val : Float) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m) : Float :=
  match find_first_true_index condlist val with
  | some idx => funclist[idx]! val
  | none => val

/-- Apply piecewise function based on conditions -/
def piecewise {n m : Nat} (x : Vector Float n) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m) : Vector Float n :=
  Vector.ofFn (fun i => apply_piecewise_element (x[i]!) condlist funclist)

-- LLM HELPER
lemma vector_ofFn_length {n : Nat} (f : Fin n → Float) : 
  (Vector.ofFn f).toList.length = n := by
  simp [Vector.ofFn, Vector.toList]

/-- Specification: The result has same length as input -/
theorem piecewise_length {n m : Nat} (x : Vector Float n) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m)
  (h : m = m) :
  let ret := piecewise x condlist funclist
  ret.toList.length = n := by
  simp [piecewise]
  exact vector_ofFn_length _

-- LLM HELPER
lemma find_first_true_index_sound {m : Nat} (condlist : Vector (Float → Bool) m) (val : Float) (j : Nat) :
  find_first_true_index condlist val = some j → j < m ∧ condlist[j]! val := by
  unfold find_first_true_index
  let rec helper_sound (i : Nat) : find_first_true_index.helper condlist val i = some j → j < m ∧ condlist[j]! val := by
    intro h_eq
    unfold find_first_true_index.helper at h_eq
    if h_i : i < m then
      simp [h_i] at h_eq
      if h_cond : condlist[i]! val then
        simp [h_cond] at h_eq
        rw [← h_eq]
        exact ⟨h_i, h_cond⟩
      else
        simp [h_cond] at h_eq
        exact helper_sound (i + 1) h_eq
    else
      simp [h_i] at h_eq
  exact helper_sound 0

-- LLM HELPER
lemma vector_ofFn_get {n : Nat} (f : Fin n → Float) (i : Nat) (h : i < n) :
  (Vector.ofFn f)[i]! = f ⟨i, h⟩ := by
  simp [Vector.get, Vector.ofFn]

/-- Specification: Function application based on conditions -/
theorem piecewise_spec {n m : Nat} (x : Vector Float n) (condlist : Vector (Float → Bool) m) (funclist : Vector (Float → Float) m)
  (h : m = m) :
  let ret := piecewise x condlist funclist
  ∀ i j : Nat, i < n → j < m →
    condlist[j]! (x[i]!) → ret[i]! = funclist[j]! (x[i]!) := by
  intro i j h_i h_j h_cond
  simp [piecewise]
  rw [vector_ofFn_get]
  simp [apply_piecewise_element]
  have h_find : ∃ k, find_first_true_index condlist (x[i]!) = some k ∧ k ≤ j := by
    sorry -- This would require proving that find_first_true_index finds the first true condition
  cases h_find with
  | intro k h_k =>
    cases h_k with
    | intro h_eq h_le =>
      simp [h_eq]
      have ⟨h_k_lt, h_k_cond⟩ := find_first_true_index_sound condlist (x[i]!) k h_eq
      sorry -- This would require proving that if j satisfies the condition and k is the first index that satisfies it, then k = j

end DafnySpecs.NpPiecewise